# AIProver: startup and verification

**Any agent or person using this plugin: read this first, then run the check in §1.** If every
line says PASS, the environment is ready and nothing else here needs doing. If something FAILs,
§5 says what it means and how to fix it. Do not work around a failing check: every number
quoted for AIProver was measured in a working environment, and a broken tool silently costs
accuracy. (One earlier run lost 16 of its 23 Lean tools without anyone noticing, which was worth
−0.074 fitness.)

```
AIProver_plugin/
├── aiprover.toml        THE config: model endpoint (SSH), paths, concurrency. Edit only this.
├── STARTUP.md           this file
├── README.md            what the plugin is, in one page
├── setup.sh             provisions + installs + verifies everything (idempotent)
├── bin/aiprover         the CLI (symlink into the skill)
├── setup/               exact dependency pins: venv lock files, the Lean project's lakefile/manifest
├── smoke/step1_smoke.py end-to-end test: one problem through Claude Code or Codex, as step1 runs it
├── claude_code/         Claude Code plugin: skill + lean-lsp MCP server (.mcp.json)
│   └── skills/aiprover-autoformalize/{SKILL.md, references/, scripts/, harness/}
└── codex/               Codex skill (same scripts + harness, Codex-specific SKILL.md)
    └── skills/aiprover-autoformalize/...
```

## 0. What has to work

Three things. The check in §1 tests each one directly rather than inferring it.

| component | what it is | needs |
|---|---|---|
| **AIProver model** | our fine-tuned Leanstral-1.5-class model on vLLM | reachable over SSH (§2) |
| **AIProver agent** | the evolved hevo harness (`harness/harness.py`, champion `d01_r04` plus the cslib deltas listed in `harness/MANIFEST.json`) driving that model through `mistral-vibe` with the 23 `lean-lsp-mcp` tools | vibe venv, MCP venv, Lean 4.23.0 + Mathlib + cslib, ripgrep |
| **coding agent** | Claude Code or Codex with the `aiprover-autoformalize` skill + the same lean-lsp tools | plugin/skill installed (§3) |

AIProver runs **on the machine you call it from**. The harness runs directly under the host's
Python: no container, no apptainer, no docker. Every path the harness uses is resolved from
`aiprover.toml`. `doctor` imports the harness exactly as a rollout does and asserts that every
absolute path it resolved exists on this machine ("harness paths all local"). Only the model
runs remotely.

## 1. Verify (do this first, every new session or machine)

```bash
AIProver_plugin/bin/aiprover doctor                   # ~40 s: config, Lean, venvs, tunnel, model
AIProver_plugin/bin/aiprover doctor --full            # + harness selftest, all 23 lean-lsp tools,
                                                      #   and ONE LIVE AIProver rollout (~3-5 min)
AIProver_plugin/bin/aiprover doctor --full --agents   # + asks Claude Code and Codex themselves
```

Expected: `14/14 PASS` (quick), `17/17` (`--full`), `19/19` (`--full --agents`). With the model
server down, two rows depend on it (`model endpoint`, and `model thinks` / the live rollout are
then not run): the quick run reports `13/14` with only `model endpoint` failing.
The checks cover both kinds of agent. A tool that is installed but broken fails here, even
after a successful setup:
- **Libraries.** `cslib built (CS library, same Lean)` asserts the pinned cslib package is built
  AND declares the project's own toolchain. `lean_local_search reaches the libraries` asserts the
  ripgrep `--follow` patch in lean-lsp-mcp (§3): without it, name search sees no library at all.
- **AIProver as an agent.** `harness selftest` checks its environment without a model call.
  `AIProver live rollout + its tools` runs a real rollout on a one-line theorem. It PASSes only
  if the answer verifies AND the model made lean-lsp calls with zero failures.
- **Claude Code / Codex as agents.** `lean-lsp-mcp tools` calls all 23 tools through the same
  launcher the agents' MCP config uses, and checks the answers (the goal text, a closing
  tactic, a real lemma name), not just "no error". `Claude Code sees skill + lean-lsp` reads a
  real session's init: skill present, server connected, ≥ 20 lean tools. `Codex sees skill +
  calls lean-lsp` has Codex make an actual lean-lsp call.

`--full` shows two known, harmless notes:
- `harness selftest ... 60/61 ... (known under host execution: 'mathlib read-only')`: the
  selftest asserts the container's read-only Mathlib mount. On the host it just means this user
  may write the shared Lean project (see §6).
- `lean_state_search` as a hosted-service WARN: an external premise-search service that
  intermittently times out. It is not required.

Then check that the agents see the plugin:
```bash
claude plugin list | grep aiprover                  # aiprover@aiprover-local  ✔ enabled
codex mcp list | grep lean-lsp                      # lean-lsp ... enabled
ls -l ~/.agents/skills/aiprover-autoformalize       # -> AIProver_plugin/codex/skills/...
```

## 2. The model endpoint (`[endpoint]` in `aiprover.toml`)

Starting the server itself: `serve/serve_aiprover.sh /path/to/aiprover_model` (or
`serve/serve_vista_pp2.slurm` on Slurm); the flags it uses are the ones the harness needs.

The CLI opens the SSH tunnel itself, checks it on every call, and re-opens it if it drops.
Nothing needs to stay running. Pick the setup that matches where the model is served:

**(A) A cluster (TACC Vista/Stampede3): SSH to the login node, model on a compute node.**
Compute nodes are not reachable from outside, and the node changes with every job. So give the
login host plus the handoff file the vLLM job writes (`node=<n> port=<p> job=<id>`). The tunnel
reads it fresh each time it opens, so a server that moves is followed automatically.
```toml
mode = "ssh"
ssh_host = "vista.tacc.utexas.edu"      # or an ~/.ssh/config alias
ssh_user = "<you>"
control_socket = "~/.ssh/vista.sock"    # TACC requires MFA: see below
server_handoff = "/scratch/11428/pjana/servers/leanstral_step1_d.txt"
local_port = 18555
```
MFA cannot be answered by a script, so open ONE ControlMaster by hand. After that, every tunnel
and handoff read rides it with no prompt:
```bash
ssh -fNM -S ~/.ssh/vista.sock -o ServerAliveInterval=30 <you>@vista.tacc.utexas.edu   # type password + MFA once
ssh -S ~/.ssh/vista.sock -O check vista.tacc.utexas.edu                                # "Master running"
```
This works from any machine, inside or outside TACC. If the socket dies, `doctor` says so and
prints this command.

**(B) A server you can SSH to directly (model on that machine): just IP + port.**
```toml
mode = "ssh"
ssh_host = "203.0.113.7"
ssh_user = "ubuntu"
ssh_options = ["-i", "~/.ssh/id_ed25519"]
control_socket = ""
server_handoff = ""
remote_host = "127.0.0.1"               # vLLM listens on the SSH host itself
remote_port = 8000
local_port = 18555
```

**(C) Already reachable** (an existing tunnel, same network): `mode = "direct"`,
`api_base = "http://host:port/v1"`.

`model = ""` takes the first id `/v1/models` reports. Set it when the server hosts several.

**Serving requirements.** The harness needs a vLLM OpenAI-compatible server with Mistral tool
calling and reasoning enabled, at the full context length:
```
--tokenizer-mode mistral --config-format mistral --load-format mistral
--tool-call-parser mistral --enable-auto-tool-choice --reasoning-parser mistral
--max-model-len 1048576          [--served-model-name <name>  -> [endpoint].model]
```
The proven recipe for the official fp8 Leanstral is `~/leanstral_vista_vllm.slurm` on Vista
(2 GH200 nodes, pipeline-parallel 2, about 270 s cold start; the handoff file is written only
once `/v1/models` answers). A fine-tuned checkpoint is served the same way from its own path.
`doctor` checks both that the endpoint answers and that the model actually THINKS at
`reasoning_effort=high`. If reasoning is not returned, the parser flags above are missing, and
the harness would run with thinking off, which was measured at 4% vs 55.6% on identical weights.

## 3. Install on a new machine

Prerequisites: Linux (x86_64 or aarch64), Python 3.12 (venvs) and ≥ 3.11 (CLI), git, curl,
about 10 GB disk for Mathlib, SSH access to the model host, and `claude` and/or `codex`
installed and logged in.

```bash
cd AIProver_plugin
$EDITOR aiprover.toml          # [endpoint] per §2; [paths] where things live / should be built
./setup.sh                     # everything; or step by step:
./setup.sh deps                #   elan + Lean v4.23.0, Mathlib v4.23.0 project + REPL, cslib, both venvs, ripgrep
./setup.sh cslib               #   add + build the pinned cslib package in an existing project (~15 s)
./setup.sh claude              #   Claude Code plugin (skill + lean-lsp MCP), user scope
./setup.sh codex               #   Codex: skill -> ~/.agents/skills, MCP server 'lean-lsp' in ~/.codex/config.toml
./setup.sh doctor              #   = bin/aiprover doctor --full --agents
```
What each step does, so you can do or check it by hand:

| step | does | verified by doctor as |
|---|---|---|
| Lean | elan; `leanprover/lean4:v4.23.0`; a project from `setup/lean_project/` (Mathlib `v4.23.0` + Lean REPL, the exact manifest the champion used), `lake exe cache get`, `lake build repl` | lean project built / toolchain / REPL / canary compiles |
| cslib | appends the `require cslib` pin and manifest entry from `setup/lean_project/` to the project (if absent), lifts the read-only bit on `.lake/packages` for the build only, `lake build cslib/Cslib`, re-locks, and asserts cslib's `lean-toolchain` equals the project's. The pinned commit (`cd368e6`, cslib's last on Lean v4.23.0) declares mathlib `37df177aaa` and batteries `d117e2c28c` -- exactly this project's revisions -- so nothing else is fetched or rebuilt | cslib built (CS library, same Lean) |
| vibe venv | `pip install -r setup/requirements-vibe.lock` (mistral-vibe 2.24.2, the harness's agent loop) | vibe (harness agent loop) |
| MCP venv | `pip install -r setup/requirements-mcp.lock` (lean-lsp-mcp 0.30.0), then three patches: relaxes leanclient's `MIN_LEAN_VERSION` to (4, 23); warms the scratch pools with `import Mathlib`; adds `--follow` to `lean_local_search`'s ripgrep so it traverses the `.lake/packages` symlink both Lean projects use. Each deletes the stale `.pyc` | lean-lsp-mcp + leanclient patch; lean_local_search reaches the libraries |
| ripgrep | into `[paths].rg_dir` | ripgrep |
| Claude Code | `claude plugin marketplace add AIProver_plugin` + `claude plugin install aiprover@aiprover-local`; links `~/.config/aiprover/aiprover.toml` (the installed plugin runs from a cache copy and finds the config there) | `claude plugin list` |
| Codex | symlink `~/.agents/skills/aiprover-autoformalize`; `codex mcp add lean-lsp -- .../scripts/aiprover mcp-serve` with 120 s startup / 600 s tool timeouts | `codex mcp list` |

**Why the leanclient patch matters.** leanclient ≥ 0.12 refuses to start a language server on
Lean < 4.24. We pin 4.23.0 because the agent must compile with the grader's toolchain, and the
gate is advisory. Unpatched, most lean-lsp tools fail on every call. **Any `pip install` into the
MCP venv undoes the patch. Re-run `./setup.sh venvs` afterwards.**

`setup.sh` itself needs a Python ≥ 3.11 on `PATH` for its helper scripts; on a box whose
system `python3` is older, `PATH=~/mcp_env/bin:$PATH ./setup.sh ...` works.

**After editing anything under `claude_code/`, re-run `./setup.sh sync claude`.** `sync` makes
`codex/` identical (doctor checks this). `claude` reinstalls the plugin, because Claude Code runs
an installed plugin from a cached copy that it refreshes only on a version bump. Codex links to
the files directly.

## 4. Running

**Interactive.** Start `claude` or `codex --sandbox danger-full-access` and give it the NL
theorem+proof pair. The skill triggers on that request; you can also ask for it by name.

**Headless / step1** (`llm_inferAndEval`):
```bash
cd llm_inferAndEval
AIPROVER=1 INFERENCE_BACKEND=claude_code MODEL_ID=claude-opus-5 ./step1_run_inference.sh
AIPROVER=1 INFERENCE_BACKEND=codex_code  ./step1_run_inference.sh
```
`AIPROVER=1` (see CONFIG.conf) loads the plugin into the Agent SDK session. It allow-lists Bash,
file and lean-lsp tools, because step1's `dontAsk` mode otherwise DENIES them. It raises the
turn and time budgets (400 turns, 4 h per sample), gives each sample its own working directory,
forces Codex's `full_access` sandbox, and suffixes outputs `-aiprover`. Without it, step1 behaves
exactly as before.

Directly: `claude -p --plugin-dir AIProver_plugin/claude_code "<prompt>"`, or in the Agent SDK
`ClaudeAgentOptions(plugins=[{"type": "local", "path": ".../AIProver_plugin/claude_code"}],
allowed_tools=[..., "mcp__plugin_aiprover_lean-lsp"])`.

**Codex sandbox.** AIProver needs the network (its tunnel on 127.0.0.1, SSH) and writes
`~/.aiprover`. On this VM `workspace-write` cannot run ANY command (bubblewrap:
`loopback: Failed RTM_NEWADDR`), so use `danger-full-access`.

**End-to-end smoke** (one problem through the real agent, step1's prompt and answer extraction,
then `aiprover check` on the extracted file):
```bash
~/lean_env/bin/python3 smoke/step1_smoke.py --agent claude --problem P.txt --out /tmp/smoke_cc
~/lean_env/bin/python3 smoke/step1_smoke.py --agent codex  --problem P.txt --out /tmp/smoke_cx
```

**Capacity.** `[runtime].max_parallel` caps concurrent AIProver rollouts on this machine,
across all jobs and agents (a file-lock semaphore). Each holds a Lean server (~1.5 GB) and
compiles peak at ~5 GB. The model server's KV cache is the other limit: 32 concurrent rollouts
kept one Vista PP=2 server at 85–95% KV.

## 5. When a check fails

| FAIL | meaning | fix |
|---|---|---|
| harness is the pinned champion | harness/grader bytes differ from `harness/MANIFEST.json` | restore from git; never edit the harness in place (a deliberate change must update `harness_sha256` AND `deltas_from_champion` in the manifest) |
| both skill copies identical | `codex/` drifted from `claude_code/` | `./setup.sh sync` |
| lean project built / REPL / canary | Mathlib oleans or REPL missing, or Lean broken | `./setup.sh lean`; check `[paths].lean_project`, `elan_home` |
| check: kernel axiom probe | the completeness check cannot be trusted | Lean/Mathlib broken: fix those first |
| harness paths all local | a harness path resolved to a non-existent (cluster) location | set the `[paths]` entry it names |
| vibe | wrong/missing mistral-vibe | `./setup.sh venvs` |
| lean-lsp-mcp + leanclient patch | gate not relaxed (often after a pip install) | `./setup.sh venvs` |
| ripgrep | `lean_local_search` would fail every call | `./setup.sh rg`, set `[paths].rg_dir` |
| cslib built (CS library, same Lean) | the pinned cslib package is missing, unbuilt, or on another toolchain | `./setup.sh cslib` (needs the project built first; reports the toolchain it found) |
| lean_local_search reaches the libraries | the ripgrep `--follow` patch is missing (often after a pip install into the MCP venv) | `./setup.sh venvs` |
| model endpoint | tunnel/handoff/server | `bin/aiprover tunnel up` prints the reason. Dead ControlMaster: re-open per §2. Handoff unreadable: the server job is not up. Local port bound: `tunnel down` or change `local_port` |
| model thinks | server lacks `--reasoning-parser mistral` | restart vLLM with the §2 flags |
| harness selftest | anything except `mathlib read-only` | read its FAIL lines: `cd ~/.aiprover/doctor_selftest && <vibe>/bin/python3 <skill>/harness/harness.py selftest` with the env from `aiprover.py:harness_env` |
| lean-lsp-mcp tools | a core tool errors | run `bin/aiprover _mcp_smoke` for the per-tool table |
| AIProver live rollout + its tools | model/harness/tools fail together, live | read `~/.aiprover/jobs/doctor-live-*/s0/agent.log`; a failed `m_lean_*` call names the tool: re-run `./setup.sh venvs` |
| Claude Code sees skill + lean-lsp | plugin not installed/enabled, or MCP not connected | `./setup.sh claude`; `claude plugin list` |
| Codex sees skill + calls lean-lsp | skill link or MCP registration missing | `./setup.sh codex`; `codex mcp list` |

## 6. Known limits (read before trusting a number)

- **No isolation.** The AIProver agent has a shell and runs as you, as it did during
  evolution (`tools/apptainer-local`). It could write the shared Lean project. Point
  `[paths].lean_project` at a copy you do not mind, or make it read-only
  (`chmod -R a-w`). Doctor then shows the selftest at 60/60.
- **Hosted search tools** (`lean_leansearch`, `lean_loogle`, `lean_leanfinder`,
  `lean_state_search`, `lean_hammer_premise`) need outbound internet and may index a newer
  Mathlib. The harness already tells the model to confirm names locally.
- **Frontier cost is dominated by waiting and judging.** Claude Code waits with one blocking
  command per 9 minutes. Codex polls every 60 s (≈1–2 k tokens per poll with cached context).
  Jobs themselves cost no frontier tokens.
- The harness's own context compaction threshold is 200k (the evolved value; the server serves
  1M). It is part of the measured artifact and is left as evolved.
- **Turn and time budget.** `[runtime].max_turns = 200` and `timeout_sec = 10800` are DEFAULTS
  above the champion's measured 100 / 5400 s; the harness's time fences (search withdrawn,
  finalize, soft notice) scale with each job's timeout at the champion's ratios, so a job keeps
  the same landing behaviour at any size. Numbers quoted for AIProver were measured at 100 turns;
  `submit --max-turns 100 --timeout 5400` reproduces that setting exactly.
- **cslib is a snapshot.** The pinned commit is the last one on Lean v4.23.0 (2025-09-15): 29
  modules, ~500 declarations. cslib on GitHub today has ~250 modules on Lean 4.35; none of that
  can be imported without moving the whole project, the harness and every measured number to a
  newer toolchain. `aiprover search` and `lean_local_search` read the pinned snapshot, so what
  they find is exactly what compiles here.
- **`probe` is advisory.** `plausible` needs sampling and decidability instances: statements over
  abstract carriers or ℝ come back `untestable`; `no counterexample` after 100 random tests is
  not evidence of correctness. Only `COUNTEREXAMPLE` is a verdict (the statement is false).
- **Hosted search rate limits inside lean-lsp-mcp** (per server process): loogle 3 calls / 30 s,
  leanfinder 10 / 30 s, state-search and hammer-premise 6 / 30 s, leansearch 90 / 30 s. A burst
  of `lean_loogle` calls returns rate-limit errors that cost the agent a turn each; the harness
  prompt steers the model to `lean_local_search` first.
