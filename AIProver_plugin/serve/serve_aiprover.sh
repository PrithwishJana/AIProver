#!/usr/bin/env bash
# Serve the AIProver model with vLLM, with the exact flags the harness needs.
#
#   serve/serve_aiprover.sh /path/to/aiprover_model
#
# Settings (environment or flags): PORT (8041), SERVED_NAME (aiprover-model), TP, PP,
# MAX_MODEL_LEN (1048576, the full context), EXTRA_ARGS (appended to `vllm serve`),
# DRY_RUN=1 (print the command, run nothing).
#
# SIZE: the weights are FP8, ~112 GB, so the GPUs you give vLLM need well over 112 GB in total
# plus room for the KV cache (the model uses MLA, ~22.5 KiB per token). Examples:
#   one node, 2+ GPUs of 80 GB    TP=<gpus> PP=1        (this script's default: TP = GPUs on the node)
#   two nodes, one 96 GB GPU each TP=1 PP=2             (needs a ray cluster across the nodes, see
#                                                        serve_vista_pp2.slurm, which does it for Slurm)
# Pipeline-parallel (PP) across nodes is preferred over tensor-parallel (TP) when GPUs are on
# different machines: PP only passes activations between stages, TP all-reduces every layer.
#
# Then point aiprover.toml [endpoint] at host:PORT and run  bin/aiprover doctor.
# Requests use the served model name (default "aiprover-model") and need `reasoning_effort` at
# the top level of the request body; bin/aiprover already does both.
set -euo pipefail

MODEL=${1:-${AIPROVER_MODEL:-}}
[ -n "$MODEL" ] || { sed -n '2,6p' "$0" | sed 's/^# \{0,1\}//'; echo "usage: $0 /path/to/aiprover_model" >&2; exit 2; }
[ -f "$MODEL/params.json" ] && [ -f "$MODEL/tekken.json" ] || { echo "not a model directory (params.json / tekken.json missing): $MODEL" >&2; exit 1; }

PORT=${PORT:-8041}
SERVED_NAME=${SERVED_NAME:-aiprover-model}
MAX_MODEL_LEN=${MAX_MODEL_LEN:-1048576}
PP=${PP:-1}
if [ -z "${TP:-}" ]; then
  TP=$( (nvidia-smi -L 2>/dev/null || true) | wc -l)
  [ "$TP" -ge 1 ] || TP=1
fi

if command -v nvidia-smi >/dev/null 2>&1; then
  TOTAL_MIB=$(nvidia-smi --query-gpu=memory.total --format=csv,noheader,nounits | awk '{s+=$1} END{print s+0}')
  NEED_MIB=$((130 * 1024))   # ~112 GB weights + a little KV; PP spans nodes, so this counts this node only
  if [ "$PP" -le 1 ] && [ "$TOTAL_MIB" -lt "$NEED_MIB" ]; then
    echo "warning: this node has $((TOTAL_MIB / 1024)) GiB of GPU memory in total; the FP8 weights alone are ~112 GB." >&2
    echo "         Use PP=2 across two nodes (serve_vista_pp2.slurm) or a node with more GPU memory." >&2
  fi
fi

CMD=(vllm serve "$MODEL"
  --served-model-name "$SERVED_NAME"
  --host 0.0.0.0 --port "$PORT"
  --tensor-parallel-size "$TP" --pipeline-parallel-size "$PP"
  --max-model-len "$MAX_MODEL_LEN"
  --tokenizer-mode mistral --config-format mistral --load-format mistral
  --tool-call-parser mistral --enable-auto-tool-choice --reasoning-parser mistral)
# PP across nodes needs vLLM's ray executor (the ray cluster must already be up).
[ "$PP" -gt 1 ] && CMD+=(--distributed-executor-backend ray)
# shellcheck disable=SC2206
[ -n "${EXTRA_ARGS:-}" ] && CMD+=($EXTRA_ARGS)

echo "[serve] ${CMD[*]}" >&2
[ "${DRY_RUN:-0}" = "1" ] && exit 0
exec "${CMD[@]}"
