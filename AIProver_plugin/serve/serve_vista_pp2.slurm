#!/bin/bash
#SBATCH -p gh
#SBATCH -N 2                      # 2 x GH200 (~95 GiB usable each) = ~190 GiB
#SBATCH --ntasks-per-node=1
#SBATCH -t 04:00:00
#SBATCH -J aiprover_serve
#
# Multi-node vLLM for the AIProver model on Slurm, pipeline-parallel across the nodes (one GPU per
# node, so every byte of parallelism crosses the network: PP passes activations at stage
# boundaries only, TP would all-reduce every layer). Written for TACC Vista (GH200, aarch64).
#
#   sbatch -A <your-allocation> \
#     --export=ALL,MODEL=/path/to/aiprover_model,CONTAINER=/path/to/vllm-arm64.sif,RAYENV=/path/to/rayenv \
#     serve/serve_vista_pp2.slurm
#
#   MODEL      the model directory (params.json, tekken.json, consolidated-*.safetensors)
#   CONTAINER  an apptainer image with vLLM (tested: vllm/vllm-openai v0.27.1, arm64)
#   RAYENV     a directory holding `ray` installed with the CONTAINER's own python (ray is not in
#              the image; vLLM's multi-node PP needs it). Install with the container's pip using
#              `--target`, then prune transitive deps (protobuf!) so they do not shadow the image's.
#   PORT (8041), HANDOFF (file written once the API answers: node=<n> port=<p> job=<id>),
#   LOGDIR (ray logs), SERVED_NAME (aiprover-model)
#
# When it is up: ssh -fN -L 8041:<node>:8041 <login-host>, then aiprover.toml [endpoint].
# Lessons baked in below: srun --overlap on every step (1 task/node), the model bind-mounted into
# the ray WORKER containers too, no nvc compiler (CC/CXX pinned to the container's gcc), and the
# compile caches on node-local /tmp (shared Lustre gave ESTALE between the two ranks).
#
set -uo pipefail

set +u
module load tacc-apptainer
set -u

APP=/opt/apps/tacc-apptainer/1.4.1/bin/apptainer
MODEL=${MODEL:?set MODEL=/path/to/aiprover_model}
CONTAINER=${CONTAINER:?set CONTAINER=/path/to/vllm-arm64.sif}
RAYENV=${RAYENV:?set RAYENV=/path/to/rayenv}
PORT=${PORT:-8041}
LOGDIR=${LOGDIR:-${SCRATCH:-$HOME}/aiprover_logs}
HANDOFF=${HANDOFF:-$LOGDIR/aiprover_server.txt}
SERVED_NAME=${SERVED_NAME:-aiprover-model}
RAY_PORT=6379
mkdir -p "$(dirname "$HANDOFF")" "$LOGDIR"

echo "[vista] arch=$(uname -m) nodes=$SLURM_JOB_NUM_NODES list=$SLURM_JOB_NODELIST job=$SLURM_JOB_ID"
[ -f "$CONTAINER" ]      || { echo "[vista] FATAL no container: $CONTAINER"; exit 1; }
[ -d "$MODEL" ]          || { echo "[vista] FATAL no model: $MODEL"; exit 1; }
[ -x "$RAYENV/bin/ray" ] || { echo "[vista] FATAL no ray in $RAYENV (see RAYENV in the header)"; exit 1; }

HEAD=$(scontrol show hostnames "$SLURM_JOB_NODELIST" | head -1)
HEAD_IP=$(getent hosts "$HEAD" | awk '{print $1}' | head -1)
echo "[vista] ray head: $HEAD ($HEAD_IP:$RAY_PORT)"

BIND=(--nv --bind "$MODEL":/model:ro --bind "$RAYENV":/rayenv)
# FIX 8 -- compile caches MUST be node-local, not Lustre. An earlier revision of this script
# put TRITON_CACHE_DIR and VLLM_CACHE_ROOT on $SCRATCH; both PP ranks then wrote Inductor
# artifacts into the SAME Lustre directory concurrently and job 927837 died in
# compile_or_warm_up_model with "[Errno 116] Stale file handle" -- ESTALE, right after
# successfully allocating a 2,418,272-token KV cache. /tmp is node-local, so each rank gets
# its own. Job-scoped names keep concurrent jobs from colliding.
CACHE=/tmp/aiprover_$SLURM_JOB_ID
ENVS=(--env PYTHONPATH=/rayenv --env CC=/usr/bin/gcc --env CXX=/usr/bin/g++
      --env TRITON_CACHE_DIR=$CACHE/triton --env VLLM_CACHE_ROOT=$CACHE/vllm
      --env XDG_CACHE_HOME=$CACHE/xdg --env RAY_DEDUP_LOGS=0)
# Create the per-node cache roots on every node before any rank needs them.
srun --overlap -N "$SLURM_JOB_NUM_NODES" --ntasks-per-node=1 \
  mkdir -p "$CACHE/triton" "$CACHE/vllm" "$CACHE/xdg"

srun --overlap -N 1 -n 1 -w "$HEAD" $APP exec "${BIND[@]}" "${ENVS[@]}" "$CONTAINER" \
  /rayenv/bin/ray start --head --port=$RAY_PORT --num-gpus=1 --block \
  > "$LOGDIR/ray_head_$SLURM_JOB_ID.log" 2>&1 &

for h in $(scontrol show hostnames "$SLURM_JOB_NODELIST" | tail -n +2); do
  echo "[vista] ray worker on $h"
  srun --overlap -N 1 -n 1 -w "$h" $APP exec "${BIND[@]}" "${ENVS[@]}" "$CONTAINER" \
    /rayenv/bin/ray start --address="$HEAD_IP:$RAY_PORT" --num-gpus=1 --block \
    > "$LOGDIR/ray_worker_${h}_$SLURM_JOB_ID.log" 2>&1 &
done

echo "[vista] waiting for $SLURM_JOB_NUM_NODES ray nodes..."
JOINED=0
for i in $(seq 1 60); do
  N=$(srun --overlap -N 1 -n 1 -w "$HEAD" $APP exec "${BIND[@]}" "${ENVS[@]}" "$CONTAINER" \
        /rayenv/bin/ray status --address="$HEAD_IP:$RAY_PORT" 2>/dev/null | grep -c "node_")
  [ "${N:-0}" -ge "$SLURM_JOB_NUM_NODES" ] && { echo "[vista] ray up: $N nodes"; JOINED=1; break; }
  sleep 5
done
[ "$JOINED" = "1" ] || { echo "[vista] FATAL ray cluster never formed"; exit 1; }

# Full 1M context. MLA makes it affordable: (kv_lora_rank 256 + qk_rope_head_dim 64) * 36
# layers = 11,520 elements/token = 22.5 KiB/token, so one 1,048,576-token sequence needs
# 22.5 GiB of KV against a ~58 GiB budget (0.9 * 190 GiB - 112.62 GiB weights) -- roughly 2.6
# concurrent full-length sequences. Plain MHA at 32 heads x 128 dim would need 576 KiB/token,
# i.e. 576 GiB for ONE sequence, so the window is only reachable via the compressed path,
# which job 927821 confirmed is active (FLASH_ATTN_MLA).
srun --overlap -N 1 -n 1 -w "$HEAD" $APP exec "${BIND[@]}" "${ENVS[@]}" \
  --env RAY_ADDRESS="$HEAD_IP:$RAY_PORT" "$CONTAINER" \
  vllm serve /model --served-model-name "$SERVED_NAME" \
    --host 0.0.0.0 --port "$PORT" \
    --tensor-parallel-size 1 \
    --pipeline-parallel-size "$SLURM_JOB_NUM_NODES" \
    --distributed-executor-backend ray \
    --max-model-len 1048576 \
    --tokenizer-mode mistral --config-format mistral --load-format mistral \
    --tool-call-parser mistral --enable-auto-tool-choice --reasoning-parser mistral &
SERVE_PID=$!

# Write the handoff only once the API actually answers, so its presence means "reachable".
URL="http://$HEAD:$PORT"
for i in $(seq 1 300); do
  if curl -s --max-time 5 "$URL/v1/models" 2>/dev/null | grep -q "$SERVED_NAME"; then
    echo "node=$HEAD port=$PORT job=$SLURM_JOB_ID cluster=vista nodes=$SLURM_JOB_NUM_NODES ready=$(date -Is)" \
      | tee "$HANDOFF"
    echo "[vista] SERVER READY after $((i*10))s -- tunnel with:"
    echo "[vista]   ssh -fN -L $PORT:$HEAD:$PORT <login-host>"
    break
  fi
  kill -0 $SERVE_PID 2>/dev/null || { echo "[vista] FATAL serve exited during startup"; break; }
  sleep 10
done

wait $SERVE_PID   # hold the reservation open for the serving lifetime
