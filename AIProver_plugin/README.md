# AIProver plugin

Makes **Claude Code** and **Codex** strong at *proof auto-formalization*. Given a
natural-language theorem with its proof, the agent produces a Lean 4 file that (a) compiles,
(b) has no `sorry`, (c) states exactly the theorem, and (d) follows the proof.

The coding agent does the parts that need judgement: planning, **judging (c) and (d)**,
decomposing, and weaving the pieces together. It hands all Lean writing and proof search to
**AIProver**: our fine-tuned Leanstral model driven by the best evolved harness (hevo champion
`d01_r04`, vendored byte-identical). Each AIProver call is a full agentic Lean session on our
GPUs, so frontier tokens go only where they matter.

## Quick start: any machine, any Claude Code / Codex

You supply **where the model is** (an IP/host to SSH into, and the model's port). Everything
else is set up and checked for you.

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
- Lean 4.23.0 + Mathlib + REPL
- the harness's two Python venvs, from exact lock files
- ripgrep
- the Claude Code plugin and the Codex skill, each with the lean-lsp MCP server

It then runs `bin/aiprover doctor --full --agents`, which tests every layer for real:

| layer | what is actually exercised |
|---|---|
| environment | Lean compiles Mathlib; the kernel-level `sorry`/axiom checker; the pinned harness bytes; every path the harness resolves is local |
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
| `aiprover.toml` | the one config: endpoint, paths, concurrency |
| `setup.sh` | idempotent provisioning + install into both agents + verification |
| `STARTUP.md` | the runbook: what each check means and how to fix it; details of every setup step |
| `bin/aiprover` | the CLI: `doctor`, `submit`/`wait`/`result` jobs, `check`, `tunnel`, `mcp-serve` |
| `claude_code/` | Claude Code plugin: `skills/aiprover-autoformalize/` + `.mcp.json` (lean-lsp) |
| `codex/` | Codex skill (same scripts and harness; Codex-specific SKILL.md) |
| `…/SKILL.md` | the procedure: delegate → judge (a)–(d) → decompose → weave → final gate |
| `…/references/playbook.md` | worked decomposition; AIProver's measured failure modes |
| `…/harness/` | the champion harness + its grader, pinned by sha256 in `MANIFEST.json` |
| `setup/` | lock files for both venvs; the Lean project's exact lakefile/manifest |
| `smoke/step1_smoke.py` | end-to-end: one problem through a real agent, with step1's prompt and answer extraction |
