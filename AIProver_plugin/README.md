# AIProver plugin

Makes **Claude Code** and **Codex** strong at *proof auto-formalization*. Given a
natural-language theorem with its proof, the agent produces a Lean 4 file that (a) compiles,
(b) has no `sorry`, (c) states exactly the theorem, and (d) follows the proof.

The coding agent does the parts that need judgement: planning, **judging (c) and (d)**,
decomposing, and weaving the pieces together. It hands all Lean writing and proof search to
**AIProver**: our fine-tuned Leanstral model driven by the best evolved harness (hevo champion
`d01_r04`, vendored and pinned by hash; its only additions since the measured bytes are the cslib
support listed in `harness/MANIFEST.json`). Each AIProver call is a full agentic Lean session on
our GPUs, so frontier tokens go only where they matter.

Libraries: Lean `v4.23.0`, Mathlib `v4.23.0`, and **cslib** (the Lean library for Computer
Science) at its last Lean-4.23.0 commit -- one toolchain for everything. The coding agent also
gets `aiprover probe` (counterexample search on candidate statements) and `aiprover search`
(declarations + docstrings of both libraries); see "What is new" below.

## Already installed? Startup after updating

Every update that touches the Lean project, the venvs or the skill files needs these steps once,
in this order (all idempotent; nothing is rebuilt that already works):

```bash
cd AIProver_plugin
./setup.sh cslib venvs         # 1. adds + builds the pinned cslib package (~15 s); re-applies the
                               #    three lean-lsp-mcp patches (leanclient gate, scratch warm-up,
                               #    ripgrep --follow for lean_local_search)
./setup.sh sync claude codex   # 2. codex/ gets the canonical files; Claude Code REINSTALLS the
                               #    plugin (it runs a cached copy, refreshed only on reinstall or
                               #    a version bump -- this release is 1.1.0); Codex is re-linked
bin/aiprover doctor            # 3. 14/14 (13/14 if the model server is down: only the endpoint row)
```
Then **restart any open Claude Code / Codex session**: a running lean-lsp MCP server keeps the
old library path and will not see cslib until it is relaunched. `setup.sh` needs a Python ≥ 3.11
on `PATH` (`PATH=~/mcp_env/bin:$PATH ./setup.sh ...` works on a box whose system python is older).

## Quick start: any machine, any Claude Code / Codex

You supply **where the model is** (an IP/host to SSH into, and the model's port). Everything
else is set up and checked for you.

**0. Start the model server** (skip if someone already runs one for you). Give it the model
directory (`params.json`, `tekken.json`, `consolidated-*.safetensors`):
```bash
serve/serve_aiprover.sh /path/to/aiprover_model     # vLLM with the flags the harness needs; port 8041
```
The weights are FP8, ~112 GB, so the GPUs must hold well over that in total. On one node with
enough GPUs the script is all you need (`TP`, `PP`, `PORT` are environment variables, `DRY_RUN=1`
prints the command). With one GPU per node (TACC Vista GH200), use pipeline-parallel across two
nodes instead: `sbatch -A <allocation> --export=ALL,MODEL=...,CONTAINER=...,RAYENV=...
serve/serve_vista_pp2.slurm` (its header explains the three variables). Either way the server
answers as `aiprover-model`; step 1 tells the CLI where to find it.

**1. Edit `aiprover.toml`, `[endpoint]`.** The current server:

| | value |
|---|---|
| SSH into | `vista.tacc.utexas.edu` (129.114.63.161), user `pjana` |
| model at | `c613-081` (129.114.17.176), port **8055**: vLLM job 1011285, up until ~2026-09-23 08:13 CDT |

```toml
ssh_host    = "vista.tacc.utexas.edu"   # the IP/host you SSH into
ssh_user    = "pjana"
remote_host = "c613-081"                # where vLLM runs, as seen from ssh_host ("127.0.0.1" = on ssh_host itself)
remote_port = 8055
server_handoff = "/scratch/11428/pjana/servers/leanstral_step1_d.txt"   # optional: follows the server if it moves
control_socket = "~/.ssh/vista.sock"    # TACC needs MFA: see step 2. Empty for plain key-based ssh.
```
The compute node's port is not reachable from outside TACC, which is why the SSH hop exists.
For a server you can SSH to directly, the whole endpoint is `ssh_host` + `remote_host =
"127.0.0.1"` + `remote_port`. The tunnel is opened, checked and re-opened automatically.

**2. TACC only: open one SSH master by hand** (MFA cannot be scripted). It lasts until you close it:
```bash
ssh -fNM -S ~/.ssh/vista.sock -o ServerAliveInterval=30 pjana@vista.tacc.utexas.edu
```

**3. Set up and verify everything:**
```bash
./setup.sh
```
This installs what is missing and uses what is already there:
- Lean 4.23.0 + Mathlib + REPL, then cslib pinned to the same toolchain (`./setup.sh cslib`)
- the harness's two Python venvs, from exact lock files, plus three small patches to lean-lsp-mcp
  (see STARTUP.md §3)
- ripgrep
- the Claude Code plugin and the Codex skill, each with the lean-lsp MCP server

It then runs `bin/aiprover doctor --full --agents`, which tests every layer for real:

| layer | what is actually exercised |
|---|---|
| environment | Lean compiles Mathlib; cslib built on the same toolchain; the kernel-level `sorry`/axiom checker; the pinned harness bytes; every path the harness resolves is local; `lean_local_search` can reach the libraries |
| model | the SSH tunnel; `/v1/models`; the model really *thinks* at `reasoning_effort=high` |
| AIProver as an agent | the harness's own selftest; **one live AIProver rollout** that must succeed *and* use its lean-lsp tools with zero failures |
| tools for Claude Code / Codex | all 23 lean-lsp tools, called through the same launcher the agents use, with answers checked for correctness |
| Claude Code / Codex as agents | each agent is asked whether it sees the skill; Codex also makes a real lean-lsp call |

All PASS means ready. Any FAIL names the problem; [STARTUP.md](STARTUP.md) §5 maps each one to its fix.
Re-run `bin/aiprover doctor --full --agents` any time. Agents run `bin/aiprover doctor` themselves
at the start of every task.

**4. Use it.**
- Claude Code: give it the NL theorem+proof.
- Codex: run `codex --sandbox danger-full-access` and do the same. Its default sandbox cannot
  reach the network AIProver needs.
- step1 batch runs: `AIPROVER=1 INFERENCE_BACKEND=claude_code ./step1_run_inference.sh` (or
  `codex_code`), from `llm_inferAndEval/`.

Needs: Linux, Python 3.12, git, curl, ~10 GB disk (Mathlib), `claude` and/or `codex` logged in.

## Layout

| path | what |
|---|---|
| `aiprover.toml` | the one config: endpoint, paths, concurrency, `[helpers]` (which LLM answers `expand`/`backtranslate`/`ask`) |
| `setup.sh` | idempotent provisioning + install into both agents + verification |
| `STARTUP.md` | the runbook: what each check means and how to fix it; details of every setup step |
| `bin/aiprover` | the CLI: `doctor`, `submit`/`wait`/`result` jobs, `check`, `probe`, `search`, `extract`, `expand`/`backtranslate`/`ask` (LLM-backed, backend per mode), `tunnel`, `mcp-serve` |
| `claude_code/` | Claude Code plugin: `skills/aiprover-autoformalize/` + `.mcp.json` (lean-lsp) |
| `codex/` | Codex skill (same scripts and harness; Codex-specific SKILL.md) |
| `…/SKILL.md` | the procedure: delegate → judge (a)–(d) → decompose → weave → final gate |
| `…/references/playbook.md` | worked decomposition; AIProver's measured failure modes; the rigor pass; reading `probe`; lemma extraction; search order; tactic rules |
| `…/harness/` | the champion harness (+ the cslib deltas) and its grader, pinned by sha256 in `MANIFEST.json` |
| `serve/` | `serve_aiprover.sh` (vLLM with the harness's flags, any node with enough GPUs) and `serve_vista_pp2.slurm` (2-node pipeline-parallel on Slurm) |
| `setup/` | lock files for both venvs; the Lean project's exact lakefile/manifest (Mathlib + REPL + cslib pins) |
| `smoke/step1_smoke.py` | end-to-end: one problem through a real agent, with step1's prompt and answer extraction |

## What is new (plugin 1.1.0)

| | what | where |
|---|---|---|
| cslib | the Lean library for Computer Science, pinned to its last Lean-4.23.0 commit (`cd368e6`: lambda calculi, STLC, combinatory logic, LTS/bisimulation, CCS, linear logic), built into the project next to Mathlib. Importable by the coding agent AND by AIProver (`import Cslib.<Module>`; the import whitelist of the harness, the grader and `check` admit it). | `setup/lean_project/`, `setup.sh cslib`, harness `MANIFEST.json` deltas |
| `aiprover probe FILE` | statement sanity before judging: every theorem's proof is replaced by `plausible` (random counterexample search) and the closers `decide simp omega norm_num aesop grind` are tried on each statement alone. `COUNTEREXAMPLE` = the statement is false as written, so (c) already fails. | `scripts/aiprover.py`, SKILL step 3/4a, playbook §8 |
| `aiprover search WORDS` | declarations + docstrings of cslib (default) and Mathlib (`--lib`), for the concept when the name is unknown; prints the exact `import` line. `--lib loogle|leansearch|leandex` wrap the hosted indexes for standalone use, each answer carrying the Mathlib-version caveat | `scripts/aiprover.py`, playbook §10 |
| `aiprover extract FILE --line N` | the goal at a `sorry` as a standalone lemma, binders written by Lean's `extract_goal` (context, instances, universes, earlier `have`s); the second rung of the escalation ladder | `scripts/aiprover.py`, SKILL step 4d, playbook §9 |
| `aiprover expand` / `backtranslate` / `ask` | the rigor pass (writer + critic rounds), the blind back-translation of a Lean file, and a free-form question. `--backend auto` uses the LLM of the mode you are in: a fresh `claude -p` inside Claude Code (your subscription), a fresh `codex exec` inside Codex, the AIProver model server standalone; `[helpers]` in `aiprover.toml` configures it | `scripts/aiprover.py`, `aiprover.toml`, playbook §12 |
| `lean_local_search` fix | its ripgrep leg never saw the libraries (both projects reach them through a `.lake/packages` symlink ripgrep does not follow); `setup.sh venvs` patches `--follow` in, `doctor` checks it. Mathlib AND cslib names are now found by prefix, for Claude Code, Codex and the AIProver harness alike. | `setup.sh`, doctor |
| `--hint-file` | longer resubmission guidance (error + goal state + confirmed lemma names) | `submit` |
| turn budget 200 / 3 h | default `max_turns` 200 and `timeout_sec` 10800 (the champion was measured at 100 / 5400 s); the harness's time fences now scale with each job's timeout at the champion's ratios, and the prompt's "you have about N turns" follows `--max-turns` | `aiprover.toml`, `scripts/aiprover.py` |
| skill procedure | step 1b makes P explicit before delegation; step 3 probes before judging; step 4d is a numbered ladder (structured hint, extract the stuck step as a lemma via `lean_goal`, split, only then prove by hand); tactic rules that protect (d) | `SKILL.md`, playbook §7-§11 |

