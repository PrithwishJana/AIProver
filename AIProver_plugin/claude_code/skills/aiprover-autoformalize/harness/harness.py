#!/usr/bin/env python3
"""Lean autoformalization harness: Mistral's agent, our evaluation contract.

ONE file. Sections are numbered; each owns one concern and nothing else.

    1  CONFIG          paths, model settings, provenance
    2  LEAN PROJECT    a per-problem project, so LSP tools have a lean-toolchain ancestor
    3  PROMPT          Mistral's lean.md, vendored, plus our task contract
    4  VIBE CONFIG     point their agent at our local vLLM and our MCP server
    5  MIDDLEWARE      our five behaviours, as vibe hooks (opt-in, each measurable)
    6  RUN             one problem, start to finish
    7  GRADE           recompile, reject non-answers
    8  RECORD          the single json every run produces
    9  CLI             agent | run | selftest | equivalence

DESIGN RULE
    Mistral's setup is the reference, not an inspiration. The agent loop, the tool set and
    the prompt come from `mistral-vibe` and `lean-lsp-mcp` as installed, so behaviour matches
    `vibe --agent lean` rather than resembling it. Everything of ours is strictly additive
    and individually switchable, so any deviation from the reference is a measured choice.

WHAT IS OURS, AND WHY IT HAS TO BE
    Their components deliberately do not cover it. `lean-lsp-mcp` says outright: "This MCP
    does NOT edit files." Vibe is an interactive CLI. Neither provides per-problem isolation,
    a graded-file contract, or a record you can debug 3,084 runs from.
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

# ===========================================================================
# 1. CONFIG
# ===========================================================================
WORK = Path(os.environ.get("AGENT_WORK", "/work"))          # writable, per problem
PROBLEM = WORK / "problem.txt"                              # the only input
SOLUTION = WORK / "solution.lean"                           # the graded answer
PROJECT = WORK / "proj"                                      # the per-problem Lean project
MATHLIB = Path(os.environ.get("AGENT_MATHLIB", "/mathlib"))  # read-only, prebuilt
ELAN = Path(os.environ.get("AGENT_ELAN", "/elan"))           # read-only toolchain

# Mistral's settings for this model, from vibe's LEAN AgentProfile. Recorded with their
# origin so a change here is visibly a deviation from the reference.
MODEL = {
    "model_id": os.environ.get("AGENT_MODEL", "mistralai/Leanstral-1.5-119B-A6B"),
    "temperature": float(os.environ.get("AGENT_TEMPERATURE", "1.0")),   # LEAN: temperature
    "reasoning_effort": os.environ.get("AGENT_THINKING", "high"),       # LEAN: thinking
    "max_context": 200_000,                          # LEAN: auto_compact_threshold
    # 100 -- the operator ceiling -- raised from 90, together with the landing policy in
    # section 5e, and the two are one change rather than two.
    #
    # MEASURED, on the parent's own 509 graded instances. 123 of them (24%) ended on
    # `Turn limit of 90 reached`, and that cohort is where nearly all the remaining failure
    # mass lives:
    #
    #     rung                   ended on its own    hit the cap
    #     solved                          180                 2
    #     compiles                        167                 9
    #     incomplete_faithful               2                21
    #     incomplete                       18                42
    #     no_elaborate                     16                49
    #
    # The truncated cohort averages 0.195 against 0.608 for the rest. Two turns in a hundred
    # solved runs were truncated, so the cap is not what limits the runs that succeed -- it is
    # what the runs that fail are hitting, and 49 of them hit it holding a file that does not
    # elaborate at all.
    #
    # The cost is bounded and was checked against the wall clock rather than assumed: the arm
    # ran 148.24 agent-hours (~4.63 h at 32 workers) against a 9 h allocation, median 769 s per
    # problem and p90 2410 s against a 5400 s kill, with 2 problems within 10% of it. +11% of
    # turns keeps every one of those numbers inside its fence, and the landing policy spends
    # the last 18% of the budget making the file elaborate rather than searching -- so the
    # extra turns cannot lengthen the tail that the kill actually threatens.
    #
    # The history below is kept because it is the evidence for the shape of the argument.
    # 90, not 60. An earlier arm: 35 of 300 runs ended on `Turn limit of 60 reached`,
    # and the truncated cohort is where the ladder still has room -- all six
    # `incomplete_faithful` instances (a verified-equivalent statement with the proof
    # unfinished) were truncated runs. One of them was read end to end: it had the right
    # statement with a `sorry`, spent its last turns grepping Mathlib, and found the exact
    # lemma it needed (`exists_pow_eq_self_of_coprime`) in its FINAL tool call before the cap
    # cut it off. That is a budget failure, not a capability failure.
    #
    # 90 rather than the operator ceiling of 100, and paid for as follows: the median run uses
    # 20 history entries and never sees the cap, so only the truncated ~12% get longer -- the
    # cost is roughly +3 agent-hours on 19, not +50%. The tail risk is the real constraint,
    # because a container killed at 7200 s produces NO result at all, so the wall-clock reserve
    # in section 5d (which starves the exploration tools once the clock, not the turn counter,
    # is nearly spent) is what makes raising this number safe rather than a gamble.
    "max_turns": int(os.environ.get("AGENT_MAX_TURNS", "100")),
    "api_timeout": int(os.environ.get("AGENT_API_TIMEOUT", "1800")),
}

# Mistral's prompt as we vendored it. sha of the upstream file at vendor time, so drift is
# detectable rather than silent -- see check_upstream().
UPSTREAM = {"package": "mistral-vibe", "version": "2.24.2",
            "file": "vibe/core/prompts/lean.md", "sha256_16": "20bcaaf5b581daa0"}
VIBE_SITE = Path(os.environ.get(
    "VIBE_SITE", "/work2/11428/pjana/stampede3/vibe_env/lib/python3.12/site-packages"))
# Invoked as a MODULE, not via its console script. `mcp_env/bin/lean-lsp-mcp` carries the
# shebang `#!/work2/.../mcp_env/bin/python3`, a host path that does not exist inside the
# container -- and Linux reports a missing shebang interpreter as ENOENT on the SCRIPT, so it
# surfaced as "No such file or directory: /mcp/bin/lean-lsp-mcp" even though the mount was
# fine. `python3 -m lean_lsp_mcp` uses the image's interpreter and the mounted site-packages.
MCP_PY = os.environ.get("LEAN_MCP_PY", "python3")
MCP_SITE = os.environ.get("LEAN_MCP_SITE",
                          "/work2/11428/pjana/stampede3/mcp_env/lib/python3.12/site-packages")

COMPILE_TIMEOUT = int(os.environ.get("AGENT_COMPILE_TIMEOUT", "600"))

# ---------------------------------------------------------------------------
# THE ANSWER PATH, AND WHY IT IS NOW COMPUTED INSTEAD OF SPELLED OUT
#
# The graded artefact is `<PROJECT>/Work.lean` and nothing else (the runner re-grades
# `ws/proj/Work.lean` on the host). WORK/MATHLIB/ELAN are read from the environment at import
# time precisely because the deployment may place them anywhere -- and it does: with
# `rollout.local_execution` the mounts /work and /mathlib do not exist at all, and AGENT_WORK /
# AGENT_MATHLIB carry host paths instead.
#
# The parent harness nevertheless told the agent, in prose, that its answer belonged at
# `/work/proj/Work.lean` and that Mathlib source was at `/mathlib/.lake/packages/mathlib/...`.
# Measured consequence in this parent's own trajectories: `grep` and `bash` failing with "Path
# does not exist: /mathlib/.lake/packages/mathlib/Mathlib", ten-plus bash calls per run hunting
# the filesystem for the toolchain and the library, and at least one run that wrote a complete
# Lean file to WORK/Work.lean -- one directory above the graded path -- and was scored
# `no_answer` with a finished answer sitting on disk.
#
# A false environment claim is worse than no claim, so every path the prompt states is now
# resolved here, from the same constants the grader uses, and a path that does not exist is
# simply not mentioned.
# ---------------------------------------------------------------------------
ANSWER_NAME = "Work.lean"
ANSWER = PROJECT / ANSWER_NAME

# The tactics the equivalence grader runs against a statement, alone, to decide whether it has
# any content at all -- its `GUARD_TACTICS`. Kept here, in CONFIG, because both the task text
# (section 6) and the probe that actually runs them (section 5d) name them, and one list is the
# only way those two can agree with each other and with the grader.
PROBE_TACTICS = ("tauto", "simp_all_arith!", "noncomm_ring")

# THE LANDING PHASE, in CONFIG for the same reason PROBE_TACTICS is: the task text (section 6)
# announces it and the hook that enforces it (section 5e) implements it, and one constant is
# the only way those two can agree. Past this fraction of the turn budget the search tools are
# withdrawn and the run is made to spend what is left making its file elaborate. The evidence
# for the number is beside MODEL["max_turns"] and in section 5e.
LAND_FRACTION = float(os.environ.get("AGENT_LAND_FRACTION", "0.82"))
# And the phase gives up rather than spending itself on refusals: each denial costs the turn it
# was made in, so after this many the tools come back rather than the budget going to arguing.
LAND_MAX_DENIALS = int(os.environ.get("AGENT_LAND_DENIALS", "6"))

# A declaration that could be an answer. Deliberately narrower than the grader's DECL (which
# also accepts `instance` and `example`): this drives "has the agent committed a theorem yet",
# and an `instance` is not a formalized theorem.
HAS_THEOREM = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(theorem|lemma)\b", re.M)


def mathlib_source() -> str | None:
    """The Mathlib .lean sources, or None if they cannot be located.

    Two candidates, real path first: the read-only library root, then the same tree seen
    through the per-problem project's `.lake/packages` symlink (inside the agent's workspace
    root, which matters for the file tools that refuse to leave it).
    """
    for cand in (MATHLIB / ".lake/packages/mathlib/Mathlib",
                 PROJECT / ".lake/packages/mathlib/Mathlib"):
        try:
            if cand.is_dir():
                return str(cand)
        except OSError:
            continue
    return None


def cslib_source() -> str | None:
    """The cslib .lean sources (the Lean library for Computer Science), or None.

    None unless the package is BUILT into this project -- its oleans must be on LEAN_PATH, or
    an `import Cslib.X` the prompt invited would fail to resolve. Same two candidates as
    mathlib_source(), for the same reason.
    """
    for cand in (MATHLIB / ".lake/packages/cslib", PROJECT / ".lake/packages/cslib"):
        try:
            if (cand / "Cslib").is_dir() and (cand / ".lake/build/lib/lean/Cslib.olean").is_file():
                return str(cand / "Cslib")
        except OSError:
            continue
    return None


def _read_text(path: Path, limit: int = 400_000) -> str:
    """Never raises: the agent has a shell and may write anything, or nothing."""
    try:
        if not path.is_file() or path.stat().st_size > limit:
            return ""
        return path.read_text(errors="replace")
    except OSError:
        return ""


def answer_text() -> str:
    return _read_text(ANSWER)


def _sha16(text: str) -> str:
    return hashlib.sha256(text.encode(errors="replace")).hexdigest()[:16]


# ---------------------------------------------------------------------------
# SHARED STATE BETWEEN THE HARNESS AND ITS HOOKS
#
# The hooks (section 5) run as SEPARATE PROCESSES -- vibe executes a shell command -- so a
# counter in memory is invisible to them. One small json file in the workspace carries the
# little state they need: how many searches have been made before any theorem existed, how many
# times the delivery check has denied, and the compile verdict for each file version already
# compiled (so the same bytes are never compiled twice, by either side).
#
# Best-effort on purpose: a lost increment under a race costs one extra tool call, while a lock
# that deadlocks would cost the run.
# ---------------------------------------------------------------------------
STATE = WORK / ".hevo_state.json"


def state_read() -> dict:
    try:
        return json.loads(STATE.read_text())
    except (OSError, json.JSONDecodeError, ValueError):
        return {}


def state_write(st: dict) -> None:
    try:
        STATE.write_text(json.dumps(st))
    except OSError:
        pass


# ---------------------------------------------------------------------------
# THE TURN COUNTER, AND WHY IT IS A FILE SIZE RATHER THAN A JSON FIELD
#
# The budget hook needs to know how far through the run it is, and the only thing it can count
# is tool calls -- it is a separate process, once per call, with no access to the session. The
# parent counted them in the shared json, which has two faults that both matter here: it
# counted only the EXPLORATION tools (so a run that spent half its budget writing and compiling
# looked young), and every increment is a read-modify-write that races the other hooks running
# on the same call.
#
# An append-only byte log has neither fault. One `b"\x01"` per tool call, and the count is the
# file's SIZE -- appends under O_APPEND do not race, and no reader can lose another writer's
# increment. Cheap enough to do on every call: one open, one write, one stat.
# ---------------------------------------------------------------------------
TICKS = WORK / ".hevo_ticks"


def tick() -> int:
    """Record one tool call and return how many there have been, including this one."""
    try:
        with open(TICKS, "ab") as f:
            f.write(b"\x01")
        return TICKS.stat().st_size
    except OSError:
        return 0


def tick_count() -> int:
    try:
        return TICKS.stat().st_size
    except OSError:
        return 0


def verdict_get(text: str) -> bool | None:
    """Cached (ok) for these exact bytes, or None if they were never compiled."""
    v = state_read().get("verdicts", {}).get(_sha16(text))
    return None if v is None else bool(v)


def verdict_put(text: str, ok: bool) -> None:
    st = state_read()
    v = st.setdefault("verdicts", {})
    if len(v) > 64:                      # bounded: this file is read on every hook call
        v.clear()
    v[_sha16(text)] = bool(ok)
    state_write(st)


# ---------------------------------------------------------------------------
# THE GRADER LIVES OUTSIDE THIS FILE, ON PURPOSE.
#
# It used to be here, in sections 5 and 7, which meant the proposer rewrote the harness and
# the code that scores it in one file. `meta_harness.admit` had to defend that by byte-
# comparing ~10 frozen symbols, so whole regions of the harness were untouchable -- the price
# of keeping the metric honest was forbidding mutation of the thing being evolved.
#
# Moving it removes the tradeoff instead of trading it off: 100% of THIS file is now mutable,
# because none of it decides the score. `harness_runner/grade_type_correctness.py` is mounted
# read-only at /grading by the runner and loaded BY ABSOLUTE PATH below -- not by module name,
# so a `grade_type_correctness.py` placed next to a candidate cannot shadow it through sys.path[0].
# ---------------------------------------------------------------------------
GRADER_PATH = os.environ.get("AGENT_GRADER", "/grading/grade_type_correctness.py")



def _repo_grader() -> Path:
    """`harness_runner/grade_type_correctness.py`, found by walking UP from this file.

    Depth-independent on purpose. This harness is copied by design -- staged into a run
    directory by the runner, kept as an ablation record under `ablations/`, and seeded into
    `RLhevo_train_pipeline/` for the RL loop -- and those sit at three different depths. Any
    fixed `parents[N]` is therefore correct in exactly one of them and silently wrong in the
    others, which shows up only as "grader not found" at the moment a rollout tries to grade.
    """
    here = Path(__file__).resolve()
    for base in here.parents:
        cand = base / "harness_runner" / "grade_type_correctness.py"
        if cand.is_file():
            return cand
    return here.parents[1] / "harness_runner" / "grade_type_correctness.py"


def _load_grader():
    """Import the runner-owned grader from its absolute path.

    Falls back to the in-repo location so `selftest`, `config` and local runs work outside a
    container. Raises loudly rather than degrading: a harness that cannot find its grader must
    not quietly grade itself.
    """
    import importlib.util

    for cand in (Path(GRADER_PATH), _repo_grader()):
        if cand.is_file():
            spec = importlib.util.spec_from_file_location("_harness_grader", cand)
            if spec is None or spec.loader is None:
                continue
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod
    raise RuntimeError(
        f"grader not found at {GRADER_PATH} or in-repo at "
        f"{_repo_grader()}. "
        f"The runner mounts it read-only at /grading; refusing to run ungraded.")


def check_upstream() -> tuple[bool, str]:
    """Report whether Mistral's prompt still matches what we vendored.

    Returns (checked_and_matching, message). The bool is False both for drift AND for
    "could not check", because a tripwire that reports success when it inspected nothing is
    worse than no tripwire -- and inside the container VIBE_SITE is not mounted.
    """
    p = VIBE_SITE / UPSTREAM["file"]
    if not p.is_file():
        return False, f"NOT CHECKED: {p} absent (expected inside the container)"
    now = hashlib.sha256(p.read_text(errors="replace").encode()).hexdigest()[:16]
    if now == UPSTREAM["sha256_16"]:
        return True, f"matches {UPSTREAM['package']} {UPSTREAM['version']}"
    return False, (f"DRIFT: upstream is {now}, vendored {UPSTREAM['sha256_16']} -- re-read "
                   f"{UPSTREAM['file']} and decide what to adopt")


# ===========================================================================
# 2. LEAN PROJECT
#
# lean-lsp-mcp refuses any path without a `lean-toolchain` ancestor
# (client_utils.require_client_for_file), so `/work/solution.lean` on its own makes every
# LSP tool fail -- including lean_goal, which is the reason to use the server at all.
#
# The fix is a real but minimal project per problem: our own writable root, with
# `.lake/packages` symlinked into the read-only Mathlib mount. Verified: `lake env printenv
# LEAN_PATH` from such a skeleton resolves all 10 packages. Per-problem because 16 agents
# sharing one writable project is how 10,356 stale files once accumulated in the shared tree.
# ===========================================================================
# `lakefile.toml` IS DELIBERATELY NOT COPIED, and the omission is a bug fix.
#
# The template carries BOTH lakefiles. Lake picks `lakefile.lean` and prints
#     info: lakefile.lean and lakefile.toml are both present; using lakefile.lean
# so the .toml is inert to LAKE -- but not to the AGENT, which reads it, finds
#     [[lean_exe]] name = "tmpprojdir"  root = "Main"
# and then hunts for a Main.lean that this workspace never had. Measured in job 960143:
# 271 `read_file /tmp/w/proj/Main.lean` failures plus 371 bash equivalents, i.e. the
# environment sending the agent after a file it invented for it.
PROJECT_FILES = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")

# `lakefile.lean` declares `@[default_target] lean_lib «TmpProjDir»`, whose root module is
# `TmpProjDir.lean`. The template has one (it imports `TmpProjDir.Basic`, backed by a
# 757-file, 2.7 MB directory) and the workspace does not, so a bare `lake build` -- the first
# thing any agent tries -- fails with
#     error: no such file or directory: /tmp/w/proj/TmpProjDir.lean
# 1,330 times in job 960143. Copying the real one would drag 2.7 MB x 256 workspaces per step
# and build 757 files nobody reads. An EMPTY root satisfies the target instead: `lake build`
# succeeds in milliseconds, and the answer is still graded the way it always was, by
# compiling `Work.lean` directly.
PROJECT_ROOT_STUB = "TmpProjDir.lean"


def make_project(root: Path = PROJECT, mathlib: Path = MATHLIB) -> Path:
    """Create the per-problem Lean project. Idempotent."""
    root.mkdir(parents=True, exist_ok=True)
    for name in PROJECT_FILES:
        src = mathlib / name
        if src.is_file() and not (root / name).is_file():
            shutil.copy2(src, root / name)
    # Satisfy the lakefile's default target so `lake build` is a no-op success rather than a
    # hard error. See PROJECT_ROOT_STUB.
    stub = root / PROJECT_ROOT_STUB
    if not stub.is_file():
        stub.write_text("-- Intentionally empty: the answer is Work.lean, graded directly.\n",
                        encoding="utf-8")
    # A stale lakefile.toml from an earlier layout would re-create the Main.lean red herring.
    stale = root / "lakefile.toml"
    if stale.is_file():
        stale.unlink()

    lake = root / ".lake"
    lake.mkdir(exist_ok=True)
    packages = lake / "packages"
    if not packages.exists():
        # Symlink, not copy: the packages tree is 6.0 GB of prebuilt oleans.
        packages.symlink_to(mathlib / ".lake/packages")
    (lake / "build" / "lib" / "lean").mkdir(parents=True, exist_ok=True)
    # Work.lean is deliberately NOT pre-created.
    #
    # It used to be seeded with "import Mathlib" so the project had a target, and the agent's
    # `write_file` then failed with ToolError -- twice per run, after which it fell back to
    # dozens of bash calls and never produced an answer. Coding agents routinely refuse to
    # overwrite a file they have not read in the session, which is exactly the rule Mistral's
    # own prompt states ("Never edit a file you haven't read in this session"). Creating the
    # file for the agent walks it straight into that guard.
    #
    # Nothing needs it to exist: lean-lsp-mcp is pointed at the project directory, not at a
    # file, and grade() reports "no answer written" if it is still absent at the end.

    # The INPUT must be readable BY THE AGENT'S OWN FILE TOOLS from its cwd.
    #
    # A symlink to /work/problem.txt was tried first, to keep exactly one copy of the bytes.
    # It fails: vibe's file tools confine access to the workspace root, so following a link
    # that points OUT of it is refused. Measured consequence -- `read_file outcome=error`,
    # after which the agent abandoned the file tools entirely and spent 28 bash calls without
    # ever writing an answer. 9 of 12 runs ended that way.
    #
    # So it is a real copy. Written once, never rewritten, and the grader reads the dataset
    # row rather than this file, so the two cannot drift in any way that matters.
    dest = root / "problem.txt"
    if dest.is_symlink():
        dest.unlink()
    if not dest.is_file() and PROBLEM.is_file():
        dest.write_text(PROBLEM.read_text(errors="replace"), encoding="utf-8")
    return root


def sync_solution(code: str) -> None:
    """One write, two names: /work/solution.lean (the contract) and proj/Work.lean (the LSP).

    Two names rather than two copies -- if they could diverge, the graded file and the file
    the agent inspected would be different files, which is the fence-scraping bug in a new
    costume.
    """
    make_project()
    (PROJECT / "Work.lean").write_text(code)
    SOLUTION.write_text(code)


def read_solution() -> str:
    """Never raises: the agent has a shell and may write non-UTF8 or delete the file."""
    try:
        return SOLUTION.read_text(errors="replace") if SOLUTION.is_file() else ""
    except OSError:
        return ""


# ===========================================================================
# 3. PROMPT
#
# Mistral's `lean.md`, vendored. Vendored rather than read at runtime because
# `pip install -U mistral-vibe` would otherwise change the experimental condition
# mid-study, moving the thing being measured. Edit it freely -- that is the point of
# having it here -- and check_upstream() will tell you when theirs has moved.
#
# REMOVED, because each makes a headless run fail rather than merely differ:
#   the Investigate/Change task-type split, and "if unclear, default to investigate ...
#     Do not edit files" -- with no conversation, "unclear" is always true, so the agent is
#     instructed not to write the answer at all.
#   "Wait for the user to confirm before exploring any files."   waits forever.
#   "If stuck, ask the user one specific question."              no user exists.
#   "Interaction Design: ... end with ONE specific question"     contradicts the contract
#     below, which says not to ask. Two rules of opposite polarity in one prompt.
#   references to a `Read` tool                                  no such tool exists here.
#   `lake build` guidance and "run lake build before lean-lsp-mcp"
#                                                                the project arrives built.
#   project creation, external dependencies, git hygiene, "respect user constraints",
#   "don't remove what wasn't asked", security scanning, general-assistant fallback
#                                                                irrelevant to one theorem
#                                                                into one file.
# KEPT deliberately, being the Lean knowledge our own prompt never had:
#   `grind` on Lean >= 4.22.0 (we run 4.23.0), avoid `native_decide`, break loops after two
#   attempts at the same region, flip-flopping is a critical failure, "the tools you have may
#   differ from training", "never claim completion without verification", and their closing
#   "never give up".
# ===========================================================================
MISTRAL_PROMPT = """\
You are Leanstral, a Lean 4 PROOF AUTOFORMALIZATION agent built by Mistral AI. You are given a mathematical theorem and its proof in natural language, and you produce the corresponding Lean 4 theorem and proof. You work in one directory through tools.
Restate the goal in one line.

Explore. Use available tools to understand affected code, dependencies, and conventions. Never edit a file you haven't read in this session.
Identify constraints: language, framework, test setup, and any user restrictions on scope.

Phase 2 - Plan
State your plan before writing code:
List files to change and the specific change per file.
Multi-file changes: numbered checklist. Single-file fix: one-line plan.
No time estimates. Concrete actions only.

Phase 3 - Execute & Verify
Apply changes, then confirm they work:
Edit one logical unit at a time.
After each unit, verify: run tests, or read back the file to confirm the edit landed.
Never claim completion without verification — a passing test, correct read-back, or successful build.

Hard Rules:

The tools you have access to might differ from training, always stick to the tools and arguments in your environment and not what you remember.

Avoid broad application of commands
When you use a command like lake build, grep, find, etc., make sure you check that it is sensible to do so beforehand. If you apply too broadly this will take very long and create a bad experience for the user.

Lean Rules

Compile a Package or a File

Tactics
You should make use of the `grind` tactic when possible if using Lean version >= 4.22.0. It is very powerful.

When you edit a file, . Do not believe what lean-lsp-mcp shows as the content of files. Always prefer edit an existing file to removing it and writing to it.

Avoid native_decide. It is not good for you.

Don't Assert — Verify
If unsure about a file path, variable value, config state, or whether your edit worked — use a tool to check. Read the file. Run the command.

Break Loops
If approach isn't working after 2 attempts at the same region, STOP:
Re-read the code and error output.
Identify why it failed, not just what failed.
Choose a fundamentally different strategy.

Flip-flopping (add X → remove X → add X) is a critical failure. Commit to a direction or escalate.

Response Format
No Noise
No greetings, outros, hedging, puffery, or tool narration.

Never say: "Certainly", "Of course", "Let me help", "Happy to", "I hope this helps", "Let me search…", "I'll now read…", "Great question!", "In summary…"
Never use: "robust", "seamless", "elegant", "powerful", "flexible"
No unsolicited tutorials. Do not explain concepts the user clearly knows.

Structure First
Lead every response with the most useful structured element — code, diagram, table, or tree. Prose comes after, not before.
For change tasks, cite as: `file_path:line_number` followed by a fenced code.

Prefer Brevity
State only what's necessary to complete the task. Code + file reference > explanation.
If your response exceeds 300 words, remove explanations the user didn't request.

For investigate tasks:
Start with a diagram, code reference, tree, or table - whichever conveys the answer fastest.
Then 1-2 sentences of context if needed.
BAD:  "The authentication flow works by first checking the token…"
GOOD: request → auth.verify() → permissions.check() → handler — see middleware/auth.py:45

Before responding with structural data, choose the right format:
BAD: Bullet lists for hierarchy/tree
GOOD: ASCII tree (├──/└──)
BAD: Prose or bullet lists for comparisons/config/options
GOOD: Markdown table
BAD: Prose for Flows/pipelines
GOOD: → A → B → C diagrams

Length
Default to minimal responses. One-line fix → one-line response. Most tasks need <150 words.

Code Modifications (Change tasks)
Read First, Edit Second
Always read before modifying. Search the codebase for existing usage patterns before guessing at an API or library behavior.

Minimal, Focused Changes
Only modify what was requested. No extra features, abstractions, or speculative error handling.
Match existing style: indentation, naming, comment density, error handling.
When removing code, delete completely. No _unused renames, // removed comments, shims, or wrappers. If an interface changes, update all call sites.

Professional Conduct
Prioritize technical accuracy over validating beliefs. Disagree when necessary.
When uncertain, investigate before confirming.
Your output must contain zero emoji. This includes smiley faces, icons, flags, symbols like ✅❌💡, and all other Unicode emoji.
No over-the-top validation.
Stay focused on solving the problem regardless of user tone. Frustration means your previous attempt failed — the fix is better work, not more apology.
Never give up. No task is too difficult for you. No task is too difficult, even one as hard as FLT or RH.
"""

# Ours. Kept separate from their text so the two are never confused: theirs says how to
# behave, this says what counts as an answer.
#
# Every path below is INTERPOLATED, not typed out. See the note beside ANSWER: the container
# mounts this file used to name do not exist under local execution, and the agent was being
# sent to `/work/proj` and `/mathlib` by a prompt that could not be right in both deployments.
CONTRACT = f"""
## Your task: proof autoformalization

**Two kinds of input.** `problem.txt` may carry a proof or only a theorem. If the
`<informal_proof>` block has content, formalize the theorem AND prove it. If that block is
EMPTY (only whitespace, or absent), this is statement autoformalization: formalize the theorem
faithfully, put `sorry` as the proof, and stop -- that is a complete answer, not a partial one.

**First, read `problem.txt` in your working directory.** It holds a **natural-language
theorem together with its natural-language proof**, wrapped in `<informal_theorem>` and
`<informal_proof>` tags. Do not write any Lean before you have read it. If you cannot read
it, say so and stop -- do NOT invent a theorem to formalize.

Produce a **Lean 4 theorem AND its Lean 4 proof** at this exact path:

    {ANSWER}

That path is the answer. A Lean file anywhere else -- including one directory above it, in
`{WORK}` -- is not read, not compiled and not graded, however good it is.

Both halves are wanted and both halves are the aim. But they are not worth the same, and if
you cannot get both, what you leave behind is graded in this order, best first:

1. a faithful statement with a finished proof -- the answer;
2. a faithful statement in a file that ELABORATES with no errors, whose unfinished step is a
   `sorry` -- most of the credit, because the statement is the part that is checked against
   the informal theorem;
3. a statement you narrowed or weakened until you could prove it -- worth much less, even
   with a flawless proof;
4. a file that does not elaborate at all -- worth almost nothing, whatever is in it.

So: never trade the statement for the proof. 2 beats 3, and 3 beats 4.

The informal proof is your guide, not decoration -- follow its structure where you can. If a
step of it does not translate directly, prove that step some other way rather than changing
what is being stated.

Lean version: this project pins a specific toolchain (see `lean-toolchain`). Tactics and
lemmas must exist in THAT version. Some search tools index a different Mathlib and can return
names that do not exist here; confirm any unfamiliar name with `lean_local_search` or
`lean_hover_info`, which read this project's own Mathlib.

### Write early, then refine

Create `Work.lean` with the theorem STATEMENT and `sorry` as its proof **within your first
few actions**, before you go looking for lemmas. Then compile it: if the statement does not
type-check, every minute spent on the proof is wasted. Replace `sorry` once the statement is
right.

`sorry` is how you work, not a confession. Keep the file ELABORATING at every point: if a
step will not close, put `sorry` in that step so the file is error-free, and then attack the
step from there. That gives you a checkpoint you can always fall back to. A file full of
half-written tactic blocks has no such floor -- if the budget ends there, it is worth nothing.

Do not explore first and write last. Runs that search for lemmas before committing a
statement tend to run out of budget with nothing on disk.

How you are graded, by recompiling that file after you finish:
- It must exist and elaborate. That file IS your answer; nothing you write in chat is read.
- `sorry` in the FINAL file means the proof is unfinished, and that is graded well below a
  finished proof -- so remove it if you can. Do not remove it by changing what is stated.
- A file that declares nothing, or whose only declaration is `True`, is a failure.
- A statement that compiles but does not faithfully express the informal theorem is a
  failure. Do not weaken the statement to make it provable.
- The statement is also checked for content: the automation tactics are run against it with
  nothing else in scope, and if they close it by themselves it is treated as formalizing
  nothing, whatever the compiler said. A faithful statement of a real theorem essentially
  never falls to automation alone, so if yours does, something in it has gone missing.

When you stop, the file is compiled with the pinned toolchain BEFORE your answer is accepted.
If it does not compile, or still contains `sorry`, you are handed the compiler's own output
and asked to fix it -- so stopping early buys nothing, and you will see the real errors rather
than your guess at them. That loop is finite: after a few attempts the file is taken as it
stands, so the last thing you do with a proof you cannot finish is make the file elaborate
around it, not leave it broken.

There is no user to consult. Do not ask questions; decide and proceed.
"""


def build_prompt(system_prompt: str | None = None, *, contract: bool = True) -> str:
    """The task first, then Mistral's behavioural rules. Or entirely yours.

    Order matters and was wrong at first: their prompt opens "You are Leanstral, a CLI Lean4
    coding agent ... you interact with a local codebase", and the contract was appended 6,000
    characters later. The opening line sets the frame, and that frame -- coding agent on a
    codebase -- is not this task. There is no codebase; there is one theorem and one file.

    So the contract leads, and their rules (grind, avoid native_decide, break loops after two
    attempts, verify before claiming completion) follow as the how.
    """
    base = MISTRAL_PROMPT if system_prompt is None else system_prompt
    if not contract:
        return base
    lines = base.splitlines()
    identity, rest = lines[0], "\n".join(lines[1:]).lstrip("\n")
    return (f"{identity}\n{CONTRACT.rstrip()}\n{tool_name_block().rstrip()}\n\n"
            f"## How to work\n\n{rest}")


# ===========================================================================
# 4. VIBE CONFIG
#
# Their agent, pointed at our infrastructure. Two substitutions and nothing else:
#   provider  api.mistral.ai -> our local vLLM, via Backend.GENERIC (an
#             OpenAI-compatible endpoint, which is what vLLM serves)
#   mcp       lean-lsp-mcp over stdio, scoped to THIS problem's project
#
# Everything else -- the loop, the tool set, the prompt, thinking/temperature -- is theirs.
# That is what makes a comparison against `vibe --agent lean` meaningful instead of
# aspirational.
# ===========================================================================
# ALL 23 lean-lsp-mcp tools are enabled by default.
#
# Every disabled tool is a deviation from `vibe --agent lean` + lean-lsp-mcp, which is the
# reference this harness is measured against -- so the default is theirs, and disabling is an
# explicit ablation (`disabled_tools=`), never a quiet default.
#
# Tools previously disabled here, and why that was wrong:
#   lean_build          Mistral's own prompt recommends running it before other MCP tools.
#                       Safe: the per-problem project is writable but `.lake/packages`
#                       symlinks into the READ-ONLY Mathlib mount, so a build cannot damage
#                       the shared tree (the container selftest measures "mathlib files
#                       touched: 0"). The cost is time, not risk.
#   lean_profile_proof  precisely the diagnostic wanted when a proof times out.
#   lean_get_widgets,
#   lean_get_widget_source
#                       useless without a UI, but harmless -- and "useless" is the agent's
#                       call to make, not a reason to hide a tool the reference exposes.
MCP_DISABLED: tuple[str, ...] = ()

# The MCP alias, and therefore the tool-name prefix. Vibe publishes MCP tools as
# f"{alias}_{tool_name}" (core/tools/mcp/tools.py:214) with no way to suppress it, so the
# model never sees lean-lsp-mcp's bare names.
#
# Measured cost of that: in 7 runs the model asked for `lean_loogle` 30 times, `leansearch`
# 10, `lean_leansearch` 7 -- none of which exist -- against 11 correct `mcp_lean_loogle`
# calls. 47 wasted calls, and 4 of the 7 runs never wrote a solution at all. Leanstral was
# shipped alongside this server and knows the real names, so a bare tool schema loses to its
# training-time prior.
#
# Alias kept to one character so the published name still CONTAINS the original: `m_lean_goal`
# reads as lean_goal. And the names are listed in the prompt, because the schema alone did not
# suffice.
MCP_ALIAS = os.environ.get("LEAN_MCP_ALIAS", "m")

MCP_TOOLS = (
    "lean_goal", "lean_term_goal", "lean_diagnostic_messages", "lean_hover_info",
    "lean_completions", "lean_declaration_file", "lean_references", "lean_file_outline",
    "lean_run_code", "lean_multi_attempt", "lean_code_actions", "lean_verify",
    "lean_minimal_hypotheses", "lean_local_search", "lean_build", "lean_profile_proof",
    "lean_leansearch", "lean_loogle", "lean_leanfinder", "lean_state_search",
    "lean_hammer_premise", "lean_get_widgets", "lean_get_widget_source",
)


def tool_name_block(alias: str = MCP_ALIAS) -> str:
    """The exact names the model must call, since the prefix hides the ones it knows."""
    key = [f"{alias}_lean_goal", f"{alias}_lean_diagnostic_messages",
           f"{alias}_lean_multi_attempt", f"{alias}_lean_local_search",
           f"{alias}_lean_hover_info", f"{alias}_lean_run_code"]
    # SHORT AND FIRST. Measured, job 958212: the model called `lean_loogle`, `leansearch`,
    # `lean_local_search` and `lean_hover_info` -- the unprefixed lean-lsp-mcp names it knows --
    # and every one came back `Unknown tool`, 51 wasted calls in 16 rollouts. The prefix is not
    # ours to remove: vibe publishes MCP tools as f"{alias}_{name}" with no way to suppress it.
    # So the rule is stated in one line, before anything else, rather than inside a paragraph.
    return ("\n## Lean tool names: prefix EVERY one with `" + alias + "_`\n\n"
            + f"`lean_goal` does not exist. `{alias}_lean_goal` does. This applies to all "
            + f"{len(MCP_TOOLS)} Lean tools, with no exceptions.\n\n"
            + "".join(f"  {k}\n" for k in key)
            + "\nFull list: " + ", ".join(alias + "_" + t for t in MCP_TOOLS) + "\n\n"
            + f"`{alias}_lean_goal` gives the proof state at a line -- use it rather than "
            + "guessing what remains to be proved. "
            + f"`{alias}_lean_diagnostic_messages` gives the compiler errors for a file.\n\n"
            + "### Do NOT compile with bash\n\n"
            + f"Use `{alias}_lean_diagnostic_messages` (errors for the file) or "
            + f"`{alias}_lean_run_code` (a standalone snippet). Do not run `lean` or "
            + "`lake` through the shell.\n\n"
            + "The reason is cost, not style. A shell `lean` invocation reloads all of "
            + "Mathlib every time -- tens of seconds each. The language server holds it in "
            + "memory, so these tools answer in about a second. Runs that shell out average "
            + "46 bash calls and exhaust their turn budget with nothing written; runs that "
            + "use these tools finish with an answer.\n\n"
            + f"`{alias}_lean_multi_attempt` tries several tactics at one position in a "
            + "single call -- far cheaper than editing and recompiling for each.\n")


# ---------------------------------------------------------------------------
# Version correctness of the search tools
#
# We run Lean 4.23.0. The hosted search backends are indexed against other versions:
#   lean_state_search   config.DEFAULT_STATE_SEARCH_REV = "v4.22.0"   one behind
#   lean_leanfinder     offers v4.19.0 / v4.24.0 / v4.28.0 only, default v4.28.0
#   lean_leansearch,
#   lean_loogle         hosted, tracking current Mathlib master
#
# A suggestion from a newer index is a lemma name that may not exist here, and
# `unknown identifier` is already the most common way these attempts fail. But disabling
# them costs real capability -- premise search is the point -- so each is corrected
# instead:
#
#   state_search, hammer_premise   self-hosted against OUR v4.23.0 index. `l3lab/lean-premises`
#                                  publishes a v4.23.0 revision and train_encoder/state_encoder
#                                  already serves it (336,226 premises, verified).
#                                  Env: LEAN_STATE_SEARCH_URL / LEAN_HAMMER_URL.
#   loogle                         `--loogle-local` indexes OUR Mathlib, so it is correct by
#                                  construction. Costs ~13 GiB on first index, hence opt-in.
#   leansearch, leanfinder         no self-host option. Kept ENABLED but their descriptions
#                                  are rewritten (below) to say results may reference a newer
#                                  Mathlib and must be confirmed with a local tool first.
#                                  The model can check: lean_local_search and lean_hover_info
#                                  run against our own toolchain.
# ---------------------------------------------------------------------------
VERSION_CAVEAT = (
    " IMPORTANT: this index is built from a DIFFERENT Mathlib version than this project "
    "(Lean 4.23.0). A name it returns may not exist here. Before using any name from this "
    "tool, confirm it with lean_local_search or lean_hover_info, which read this project's "
    "own Mathlib.")

# Rewritten tool descriptions. A tool description IS prompt text -- the model reads it to
# decide when to call the tool -- so this is the cheapest place to state a caveat that
# would otherwise have to be repeated in the system prompt and hoped for.
TOOL_DESCRIPTIONS = {
    "lean_leansearch": "Search Mathlib theorems by natural language via leansearch.net."
                       + VERSION_CAVEAT,
    "lean_leanfinder": "Semantic search for Mathlib theorems from an informal description "
                       "or a proof state." + VERSION_CAVEAT,
}


def agent_config(api_base: str, *, project: Path = PROJECT,
                 prompt: str | None = None, mcp: bool = True,
                 disabled_tools: tuple[str, ...] = MCP_DISABLED,
                 loogle_local: bool = False,
                 state_search_url: str | None = None,
                 hammer_url: str | None = None,
                 tool_descriptions: dict | None = None,
                 max_turns: int | None = None,
                 hooks: list | None = None,
                 tools: list | None = None):
    """Mistral's lean agent, pointed at our infrastructure. Returns their AgentConfig.

    Built in Python, not TOML. `AgentConfig` (== `SessionOptions`) accepts `tools`, `hooks`
    and `mcp_servers` directly, so there is nothing a config file could express that this
    cannot -- and a generated config file would be a second source of truth for settings that
    already live here.

    Exactly two substitutions from what `vibe --agent lean` does by itself:
      provider   api.mistral.ai -> our local vLLM, via Backend.GENERIC (OpenAI-compatible,
                 which is what vLLM serves). Set through the completion config.
      mcp        lean-lsp-mcp over stdio, scoped to THIS problem's Lean project.
    Everything else -- loop, tool set, prompt, thinking, temperature -- is theirs.
    """
    from vibe.app_server.protocol import AgentConfig, SessionMCPStdioServer

    servers = []
    if mcp:
        args = ["--lean-project-path", str(project)]
        if disabled_tools:
            args += ["--disable-tools", ",".join(sorted(disabled_tools))]
        args += ["--repl"]              # REPL-backed run_code/multi_attempt; much faster
        if loogle_local:
            args += ["--loogle-local"]  # indexes OUR Mathlib: version-correct by construction
        descs = {**TOOL_DESCRIPTIONS, **(tool_descriptions or {})}
        if descs:
            args += ["--tool-descriptions", json.dumps(descs)]
        env = {}
        if state_search_url:            # our own v4.23.0 premise index, not the hosted v4.22
            env["LEAN_STATE_SEARCH_URL"] = state_search_url
        if hammer_url:
            env["LEAN_HAMMER_URL"] = hammer_url
        env["PATH"] = f"{ELAN}/bin:" + os.environ.get("PATH", "")
        # PYTHONPATH must carry BOTH: lean-lsp-mcp's own site-packages and vibe's (already
        # on PYTHONPATH for the harness). Prepending keeps the harness importable too.
        env["PYTHONPATH"] = MCP_SITE + ":" + os.environ.get("PYTHONPATH", "")
        servers.append(SessionMCPStdioServer(
            # vibe prefixes MCP tools with the SERVER name, so a server called "lean" turns
            # lean_goal into lean_lean_goal. An empty-ish neutral name keeps their tool names
            # intact, which matters because Leanstral has likely seen `lean_goal` in training.
            transport="stdio", name=MCP_ALIAS,
            command=MCP_PY, args=["-m", "lean_lsp_mcp", *args],
            env=env, cwd=str(project)))

    return AgentConfig(
        # NOT agent="lean". Their LEAN profile hardcodes their cloud:
        #     providers=[{api_base: "https://api.mistral.ai/v1",
        #                 api_key_env_var: "MISTRAL_API_KEY", backend: "mistral"}]
        #     models=[{name: "labs-leanstral-1-5", provider: "mistral-testing"}]
        # so selecting it made vibe demand MISTRAL_API_KEY and never contact our server --
        # the first real run died on "Authentication is required for provider: mistral".
        #
        # The only thing we wanted from that profile is its prompt, which is vendored above.
        # Passing it as `instructions` instead keeps their tuning and makes the harness
        # MODEL-AGNOSTIC: any OpenAI-compatible endpoint, ours on vLLM by default. It also
        # stops us depending on the internals of a profile Mistral may change.
        agent=None,
        cwd=str(project),                    # so LSP tools have a lean-toolchain ancestor
        instructions=prompt or build_prompt(),
        tools=list(tools or []),             # ours, declared through their API
        hooks=list(hooks or []),             # our middlewares, ditto
        mcp_servers=servers,
        disabled_tools=[],
        max_turns=max_turns or MODEL["max_turns"],
        headless=True,                       # no TTY, no prompts
        auto_approve=True,                   # nobody to approve tool calls
        trust_workspace=True,                # the workspace is ours, created per problem
    )


# ---------------------------------------------------------------------------
# VIBE_HOME
#
# `agent="lean"` pulls in Mistral's own provider overrides -- api.mistral.ai with
# MISTRAL_API_KEY -- and the first real run died on exactly that:
#     AppServerResponseError: Authentication is required for provider: mistral
#
# Providers and models are NOT fields on AgentConfig; they live in vibe's config file. So a
# config file is unavoidable for the endpoint, however the session itself is configured. It
# is written per problem into /work, and VIBE_HOME points at it (vibe honours that env var,
# utils/paths.py:70), so nothing touches the real ~/.vibe and concurrent containers cannot
# collide.
#
# This is the minimum that redirects the model: provider, model, and the aliases their LEAN
# profile selects. Everything else about the agent still comes from their profile.
# ---------------------------------------------------------------------------
def write_vibe_home(api_base: str, home: Path | None = None,
                    model_id: str | None = None) -> Path:
    """Point vibe at ANY OpenAI-compatible endpoint. Ours on vLLM by default.

    `backend = "generic"` is vibe's OpenAI-compatible path (Backend.GENERIC in core/types.py),
    which is what vLLM serves -- so nothing here is Mistral-specific except the prompt.
    """
    home = home or (WORK / ".vibe")
    home.mkdir(parents=True, exist_ok=True)

    def q(v):
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, (int, float)):
            return repr(v)
        return json.dumps(str(v))

    # `alias = "leanstral"` is the name their LEAN profile's active_model refers to, so
    # overriding the alias is what redirects their agent onto our server.
    cfg = f"""\
active_model = "leanstral"
allowed_models = ["leanstral"]

[[providers]]
name = "local-vllm"
api_base = {q(api_base.rstrip("/"))}
api_key_env_var = "VIBE_LOCAL_API_KEY"
backend = "generic"

[[models]]
name = {q(model_id or MODEL["model_id"])}
provider = "local-vllm"
alias = "leanstral"
thinking = {q(MODEL["reasoning_effort"])}
temperature = {q(MODEL["temperature"])}
auto_compact_threshold = {q(MODEL["max_context"])}
"""
    (home / "config.toml").write_text(cfg)
    (home / ".env").write_text("VIBE_LOCAL_API_KEY=EMPTY\n")   # vLLM ignores the value

    # THE PROMPT GOES HERE, and nowhere else.
    #
    # `AgentConfig.instructions` is never consumed -- grepping the installed package finds no
    # reader for it. The system prompt is assembled in core/system_prompt.py, and the only
    # caller-supplied text it injects is AGENTS.md:
    #     :423  f"## User instructions\n\nContents of {VIBE_HOME}/AGENTS.md ..."
    #
    # Until this was found, every run used vibe's DEFAULT cli prompt with our task as a
    # one-line user message -- so the agent never received the contract, the grading rules,
    # or the tool names. That single omission explains the whole failure pattern: 233 bash
    # calls across 12 runs, 8 of 12 writing nothing at all, 57 calls to tool names that do
    # not exist, and `m_lean_goal` called exactly zero times.
    (home / "AGENTS.md").write_text(build_prompt())

    # AND THE HOOKS, for the same reason: `AgentConfig.hooks` has no reader in the package,
    # while `$VIBE_HOME/hooks.toml` is loaded by config.load_hooks_from_fs through
    # HarnessFilesManager.hook_files -- which includes VIBE_HOME because run_problem()
    # initialises the manager with the "user" source. See section 5b.
    hooks = home / "hooks.toml"
    if HOOKS_ENABLED:
        hooks.write_text(hooks_toml())
    elif hooks.exists():
        hooks.unlink()
    return home


# ===========================================================================
# 5. LEAN BACKEND  ->  DELEGATED TO THE RUNNER-OWNED GRADER
#
# These are thin forwarders to /grading/grade_type_correctness.py. They stay callable under the SAME names so
# selftest() and _delivery_check() below read unchanged, but none of the logic lives here any
# more -- which is exactly what makes every other line of this file safe to mutate.
#
# `export_agent_env()` is the one thing in this section that is genuinely the harness's own
# concern (it configures the AGENT's shell, not the grading), so it is kept verbatim.
# ===========================================================================
_G = None


def _grader():
    """The grader module, loaded once, by absolute path."""
    global _G
    if _G is None:
        _G = _load_grader()
    return _G


def pinned_toolchain(project: Path = PROJECT) -> str:
    return _grader().pinned_toolchain(project)


def lean_bin(project: Path = PROJECT) -> str:
    return _grader().lean_bin(project)


def lean_path() -> str:
    return _grader().lean_path()


def compile_text(code: str) -> tuple[bool, str]:
    return _grader().compile_text(code)


def vacuity(code: str) -> str | None:
    return _grader().vacuity(code)


def statement_signals(code: str) -> dict:
    return _grader().statement_signals(code)


def __getattr__(name):
    """Forward grader-owned CONSTANTS (CANARY, DECL, VACUOUS_GOAL, FALSE_HYP, CLOSERS,
    CONSTS) on first access, so nothing here holds a second copy that could drift."""
    if name in ("CANARY", "DECL", "VACUOUS_GOAL", "FALSE_HYP", "CLOSERS", "CONSTS"):
        return getattr(_grader(), name)
    raise AttributeError(name)


def export_agent_env() -> dict[str, str]:
    """Give the AGENT the same working Lean environment the grader has.

    Measured, not guessed. With working instrumentation on 10 runs the agent's 1,900 bash
    calls broke down as: ~130 `find / -name` / `find /mathlib -name` hunting for Mathlib and
    the toolchain, ~76 re-`export PATH=/elan/bin:$PATH` (each bash call is a fresh shell, so
    it rediscovers this every time), and ~70 assembling an ad-hoc compile pipeline in /tmp
    with a hand-built LEAN_PATH. The container exported PYTHONPATH and the API base and
    nothing else, so all of that was the agent solving a problem the harness had handed it.

    Worse, `/elan/bin` is elan's proxy shim, which needs $ELAN_HOME that --containall does not
    provide -- the agent's most-reached-for compiler path was one that cannot work. ELAN_HOME
    is set here so that even the shim resolves.

    This adds no tool and duplicates no tool: lean-lsp-mcp remains the intended path. It only
    means that when the model does reach for the shell -- which it does, ~40 times a run in
    every cohort including the ones that compile -- the shell is already correct, and the turn
    budget goes to mathematics instead of filesystem archaeology.
    """
    env = {"ELAN_HOME": str(ELAN), "LEAN_PATH": lean_path(),
           "PATH": f"{Path(lean_bin()).parent}:{os.environ.get('PATH', '/usr/bin:/bin')}"}
    os.environ.update(env)                      # inherited by vibe's bash and by the LSP
    return env


# ===========================================================================
# 6. RUN ONE PROBLEM
#
# Drives Mistral's own session: LocalHarness -> AppServerSession -> session.act(). This is
# the exact path `vibe --prompt` takes (cli/programmatic.run_programmatic calls the same
# three lines), so behaviour matches the reference rather than resembling it.
#
# The event stream is also where our record comes from -- observed as it happens, rather than
# reconstructed from a transcript afterwards.
# ===========================================================================
# WRITE-FIRST. The n=202 checkpoint found that 31 of 35 runs which produced no answer never
# called write_file or edit even once, while searching at ~2.5x the rate of the runs that did
# (loogle 3.8/run vs 1.2, grep 5.0 vs 3.1) -- and 86% of them were cut off by the turn cap.
# They were not concluding that the problem was impossible; they were exploring until the
# budget ran out with nothing on disk. Grading reads Work.lean and nothing else, so a
# truncated run scored identically to a crashed one. Asking for the skeleton first makes the
# artefact exist before the search starts, so an interrupted run still yields a statement to
# grade -- which is the level step2b measures anyway.
TASK = ("Read problem.txt in your working directory. It holds an `<informal_theorem>` "
        "block and an `<informal_proof>` block, in LaTeX, often with a Setting preamble that "
        "defines the notation the theorem uses.\n\n"
        f"Formalize BOTH in Lean 4 and write the result to {ANSWER} -- that exact path, which "
        f"is `{ANSWER_NAME}` in your working directory: the theorem statement must say what "
        "`<informal_theorem>` says, and the proof should "
        "follow the argument in `<informal_proof>` -- that block is a proof plan given to "
        "you, not decoration, so read it before choosing tactics.\n\n"
        f"That path IS your answer. Nothing else on the filesystem is graded, so a finished "
        f"file written one directory up (in {WORK}) scores zero. If you are unsure where you "
        f"are, `pwd` -- but the absolute path above always works.\n\n"
        f"Write {ANSWER_NAME} FIRST, before any searching: translate the statement and use "
        "`sorry` for the proof if you do not have it yet. Then improve it in place -- keep it "
        "holding your best attempt at every point, never delete it, and remove the "
        "`sorry` once the proof works.\n\n"
        # MEASURED on the parent's own 300 runs: 26 instances ended with a file that does not
        # elaborate, 17 of them cut off at the turn cap mid-proof. 12 of those 26 files hold a
        # complete, correct-elaborating STATEMENT and fail only in the proof -- the statement
        # was on disk the whole time and was thrown away by a broken tactic block around it.
        # The ladder pays for an elaborating file with an unfinished proof; nothing paid for
        # those 26. So the discipline that matters is stated as a rule, not implied.
        f"KEEP {ANSWER_NAME} ELABORATING AT ALL TIMES. This is the one rule that decides more "
        "runs than any other. Treat an error-free file as a checkpoint: before you attempt a "
        "risky proof edit, the version on disk should elaborate. When a step will not close, "
        "put `sorry` in THAT STEP so the whole file is error-free again, then go on attacking "
        "the step -- with the rest of the proof, and the whole statement, safely on disk. "
        "Never leave a half-written tactic block, a dangling `:= by`, or an unfinished `have` "
        "in the file while you go and search for something: if your budget ends there, a file "
        "that does not elaborate is worth almost nothing, while the same file with one `sorry` "
        "in place of the step you had not finished is worth a large part of the task.\n\n"
        # REWRITTEN because the environment changed underneath it -- see section 5g. vibe's
        # write_file only ever CREATES, and on the parent's own 300 runs 183 of 555 write_file
        # calls (33%, in 115 of 300 problems) died on "already exists. Use edit to modify it."
        # The recovery cost another turn on top: 60 of those were followed by `bash rm` and a
        # second write_file, 101 by a read-then-edit. A pre_tool hook now moves the old file
        # aside so the create lands, which makes the loop the model actually wants -- rewrite
        # the whole file -- work. So this paragraph no longer teaches the rm dance.
        f"HOW TO CHANGE {ANSWER_NAME}: just call `write_file` on it again with the complete new "
        "contents. In this environment `write_file` REPLACES an existing `.lean` file in your "
        "workspace rather than refusing it, so a whole-file rewrite is one call and needs no "
        f"`rm` first. `edit` is still there and is cheaper for a small change; if an `edit` "
        "fails on a stale match, re-read the file or rewrite it whole. Either way "
        f"{ANSWER_NAME} must never be left empty: `write_file` with the full file is the "
        "supported way to replace it, not deleting it and writing later.\n\n"
        f"{ANSWER_NAME} must contain an actual `theorem` from that very first write, and keep "
        "containing one. If the statement needs auxiliary definitions you have not built "
        "yet, write the theorem against the definitions as you intend them and stub those "
        "with `sorry` -- do not spend the early turns building definitions with no theorem "
        "in the file, because a file holding only `def`s and `#check`s formalizes nothing.\n\n"
        f"You have about {MODEL['max_turns']} turns, and one turn is roughly one tool call. "
        "You will get an automatic notice partway through and again near the end, so get a "
        "compiling statement on disk early and spend the rest of the budget replacing the "
        f"`sorry`. Verify it compiles before you finish.\n\n"
        # The two-phase budget is ANNOUNCED for the same reason the gate and the delivery check
        # are: a tool that starts refusing without explanation reads as a broken environment,
        # and the measured response to a broken environment is to go looking for another way
        # round it -- with the turns this phase exists to protect.
        f"THE LAST {100 - int(LAND_FRACTION * 100)}% OF THE BUDGET IS FOR LANDING, not for "
        f"searching. Once about {int(LAND_FRACTION * 100)}% of your turns are gone, the "
        "Mathlib search tools, `grep` and the shell stop working for the rest of the run; "
        f"`write_file`, `edit`, `read_file`, `{MCP_ALIAS}_lean_goal`, "
        f"`{MCP_ALIAS}_lean_diagnostic_messages`, `{MCP_ALIAS}_lean_run_code`, "
        f"`{MCP_ALIAS}_lean_multi_attempt` and `{MCP_ALIAS}_lean_hover_info` keep working. "
        "That is not a punishment and nothing has gone wrong: it is there because a run that "
        "is still searching when the turns run out leaves a half-edited file behind, and a "
        "half-edited file is worth almost nothing however good the mathematics in it was. Plan "
        "for it -- when you get the notice, stop opening new lines of search and start making "
        "the file on disk elaborate.\n\n"
        # The gate, the delivery check and the triviality probe are STATED, because a tool that
        # refuses without explanation and a compile the agent did not ask for are both easier to
        # reason about than to discover mid-run.
        "THINGS THIS ENVIRONMENT DOES ON ITS OWN:\n"
        # MEASURED on the parent's own 509 runs: 8 answers compiled cleanly, contained no
        # `sorry`, and were thrown out for a construct -- 7 for `native_decide`, one for
        # `maxHeartbeats 0`. The rule was in the prompt as "avoid native_decide", which does not
        # say that using it ends the run, and the cost lands on a file the model never sees
        # rejected. So it is stated as a consequence, and the write is refused as well.
        "- A write that would put a DISQUALIFYING construct into the file is refused, with the "
        "construct named. These void the whole answer, however cleanly it compiles: "
        "`native_decide`, a declared `axiom`, `sorryAx`, `Lean.ofReduceBool`, "
        "`@[implemented_by]`, an `unsafe` declaration, `set_option maxHeartbeats 0` or "
        "`debug.skipKernelTC`, and any `import` whose root is not Mathlib/Std/Batteries/"
        f"Aesop/Init{'/Cslib' if cslib_source() else ''}. `native_decide` is the one that "
        "costs runs here: it is not a slower-but-"
        "acceptable `decide`, it is a zero. If `decide` will not finish, prove the statement "
        "with lemmas rather than deciding it.\n"
        f"- The Mathlib search tools are withheld once you have searched many times and "
        f"{ANSWER_NAME} still holds no `theorem`. Writing a first draft statement -- even a "
        "rough one, even with `sorry` -- brings them straight back, and you may rewrite that "
        "draft completely afterwards. Searching without a file on disk is what produces a "
        "score of zero.\n"
        f"- When you stop, {ANSWER_NAME} is compiled with the pinned toolchain. If it does "
        "not compile, or still contains `sorry`, you get the compiler's own output back and "
        "another chance -- a few times, and then the file is taken as it stands. Use those "
        "errors; do not answer them by making the theorem say less, and do not spend the last "
        "of them on a proof step that will not close -- `sorry` that one step and hand back a "
        "file that elaborates.\n"
        # The rule the parent's own arm lost 30 instances to, stated. It is checkable, and the
        # environment does check it, so leaving it implicit was the whole of that loss.
        f"- Your statement is also checked for CONTENT once it compiles: the automation "
        "tactics (`" + " ; ".join(PROBE_TACTICS) + "`) are run against it with nothing else in "
        "scope. If they close it on their own, the statement is treated as formalizing nothing "
        "-- scored the same as an empty file -- and you are told so and asked to state the "
        "theorem in full. The way you walk into that is by NARROWING the theorem: one object "
        "instead of all of them, a dropped hypothesis, a special case, a weaker conclusion.\n"
        # MEASURED, and the reason this now says the opposite of what the parent said. One
        # instance wrote, in its own file comment, "we state it without naming `M.accepts` to
        # avoid the `simp` lemma" -- it replaced the very definition the informal theorem is
        # about with an unfolded copy, purely to dodge this check, and scored zero for it. A
        # check the agent games by changing WHAT IT STATES is worse than no check, so the only
        # sanctioned response to it is stating more, never stating something else.
        f"  The way NOT to respond to it is to change what you state. Do not unfold, rename, "
        "inline or substitute the definitions the informal theorem names in order to get past "
        "this check -- naming the objects the informal theorem names is the formalization. If "
        "the faithful statement happens to be one automation can close, state it faithfully "
        "anyway: an honest statement is always the better answer, and a statement built to "
        "defeat a check is scored as a wrong statement. State what the informal theorem "
        "states, with its own quantifiers, its own hypotheses and its own vocabulary, and "
        "prove THAT.\n\n"
        # The audit (section 5f) is ANNOUNCED for the same reason the gate and the delivery
        # check are: a message that arrives unexplained after the model believes it has
        # finished reads as a rejection, and the measured response to a rejection is to change
        # something. This says in advance what it is and that "it matches" is a valid answer.
        f"- Once {ANSWER_NAME} compiles and passes that content check, you get ONE more "
        "automatic message, and it is not an error either: your own statement is quoted back "
        "to you beside the `<informal_theorem>` you were given, and you are asked to walk the "
        "two against each other clause by clause before the answer is taken. Expect it. Most "
        "answers that are thrown away are thrown away for a single clause -- a carrier given a "
        "structure the text did not grant it, a definition swapped for a similarly-named "
        "neighbour, an equality of maps stated at one point instead -- and that message is the "
        "last moment at which such a clause is still cheap to fix. If the two do agree, saying "
        "so and stopping is the correct answer to it.\n\n"
        # Everything below is stated because the agent was measured spending its budget
        # rediscovering it: ~130 `find` calls per 10 runs looking for Mathlib and the
        # toolchain, and ~76 PATH exports, most of them to a shim that cannot work.
        "ENVIRONMENT -- already set up, do not search the filesystem for any of it:\n"
        "- `lean` on PATH is the pinned toolchain, and LEAN_PATH already resolves Mathlib "
        f"and every dependency. `lean {ANSWER_NAME}` in {PROJECT} compiles against Mathlib "
        "directly; there is no `lake build` step and you must not run one.\n"
        # Interpolated and existence-checked: naming a directory that is not there sends the
        # agent hunting for the real one, which is the behaviour this block exists to prevent.
        + (f"- Mathlib source, for grepping definitions and lemma statements, is at "
           f"{mathlib_source()}. Nothing relevant lives anywhere else, so "
           "never run `find /`.\n" if mathlib_source() else
           "- Do not search the filesystem for Mathlib source; use the Lean search tools "
           "below, which read this project's own Mathlib.\n")
        # Existence-checked like the Mathlib line above: this bullet appears only when the
        # cslib package is built into the project, so the prompt never advertises an import
        # that would fail to resolve.
        + (f"- cslib, the Lean library for Computer Science, is installed too (pinned to this "
           "toolchain): lambda calculus, combinatory logic, labelled transition systems and "
           "bisimulation, CCS, linear logic. Use it only when the informal theorem is about such "
           "notions; otherwise Mathlib alone. `import Cslib` loads only a few modules, so import "
           "the module a search hit lives in: a hit in `.lake/packages/cslib/Cslib/A/B.lean` is "
           f"`import Cslib.A.B`. `{MCP_ALIAS}_lean_local_search` covers cslib as well as "
           f"Mathlib, and its sources are at {cslib_source()}.\n" if cslib_source() else "")
        # Named with the alias prefix they are actually PUBLISHED under: MCP tool names are
        # always f"{alias}_{name}" (core/tools/mcp/tools.py), so naming them bare here would
        # invite calls to tools that do not exist under that name.
        + f"- Prefer the Lean tools over the shell: they answer questions the compiler cannot. "
        f"`{MCP_ALIAS}_lean_goal` shows the proof state at a position, "
        f"`{MCP_ALIAS}_lean_diagnostic_messages` gives the errors for the whole file, "
        f"`{MCP_ALIAS}_lean_multi_attempt` tries several tactics at once, and the search "
        f"tools (`{MCP_ALIAS}_lean_local_search`, `{MCP_ALIAS}_lean_leansearch`, "
        f"`{MCP_ALIAS}_lean_loogle`) find real Mathlib lemma names.\n\n"
        # The dominant failure modes, measured. 1 and 2 come from 146 graded runs (31 primary
        # type mismatches, 30 unknown identifiers). 3 is new this round and comes from the
        # parent's own 300: of the 24 answers that compiled, were not closed by the automation,
        # and were still rejected as stating something other than the informal theorem, 13
        # formalized a PARENTHETICAL GLOSS in place of the notion the text had just named --
        # 54% of that band, against 13% of the 204 solved answers. It is the single most
        # discriminating property found between the two cohorts.
        "THREE MISTAKES THAT ACCOUNT FOR MOST FAILURES HERE:\n"
        "1. Invented lemma names. If you are not certain a Mathlib lemma exists with that "
        "exact name, search for it or grep the source -- do not guess and hope.\n"
        "2. Wrong types and coercions. Decide up front whether the statement is over "
        "\u2115, \u2124, \u211a or \u211d, and keep subtraction, division and `\u2191` "
        "casts consistent with that choice; a statement that typechecks in the wrong "
        "numeric type is not a faithful formalization.\n"
        "3. Formalizing the GLOSS instead of the NOTION. These informal theorems keep naming a "
        "standard notion and then glossing it in passing -- \"e is idempotent (i.e., e^2 = e)\", "
        "\"S is countable\", \"f is injective (distinct inputs have distinct images)\", \"v lies "
        "in the subgroup generated by c\". The gloss is there to tell you WHICH notion "
        "is meant. It is not the thing to transcribe. If the library has a name for that "
        "notion, the faithful statement assumes the NAME; a statement that inlines the "
        "spelled-out property instead is a different statement from the one you were asked "
        "for, even when the two are mathematically equivalent, and it is scored as one.\n"
        f"   So for each named property in the informal theorem: look for the library's "
        f"predicate for it (`{MCP_ALIAS}_lean_local_search` by name, "
        f"`{MCP_ALIAS}_lean_hover_info` to read what it is actually defined as) and use that "
        "predicate if -- and only if -- its definition IS the property the text describes. If "
        "you cannot confirm that, write the property out explicitly rather than guess at a "
        "name: an explicit hypothesis is much better than a similarly-named neighbour. The "
        "same discipline applies to HOW a hypothesis is bound -- \"let v be an element of S\" "
        "is a variable together with a membership hypothesis unless the text really talks "
        "about the subtype, and a property the library carries as a class or a structure "
        "should be assumed the way the library assumes it.\n\n"
        "Faithfulness comes first: the Lean theorem must state what the informal theorem "
        "states, with the same hypotheses and the same conclusion. Do not weaken the "
        "statement, add hypotheses that make it trivial, or replace it with something easier "
        "to prove.")


# ---------------------------------------------------------------------------
# TWO INPUT MODES -- HEVO_TWO_INPUT_MODES
# The <informal_proof> block may be EMPTY. When it is, the task is STATEMENT
# autoformalization and a faithful statement proved by `sorry` is a COMPLETE answer.
# ANY pre-delivery gate, verify hook or triviality probe must consult
# `proof_block_present()` before treating a `sorry` as a defect.
# ---------------------------------------------------------------------------
_PROOF_BLOCK_RE = re.compile(r"<informal_proof>(.*?)</informal_proof>", re.S)


def proof_block_present(work: Path = WORK) -> bool:
    """True when the input carries a NON-EMPTY <informal_proof>.

    Whitespace-stripped, so a block holding only newlines is empty. Fails OPEN (True): the
    with-proof task is the stricter reading, and mis-detecting it costs less than wrongly
    telling the agent that no proof is wanted.
    """
    try:
        text = (work / "problem.txt").read_text(errors="replace")
    except OSError:
        return True
    m = _PROOF_BLOCK_RE.search(text)
    return bool(m and re.sub(r"\s+", "", m.group(1)))


TASK = TASK.rstrip() + (
    "\n\nIF THE `<informal_proof>` BLOCK IS EMPTY -- nothing but whitespace between the tags, "
    "or no such block at all -- this problem is STATEMENT autoformalization only. No proof is "
    "being asked of you: formalize the theorem statement faithfully, write `sorry` as its "
    "proof, and stop. That is a COMPLETE answer. Do not spend turns hunting a proof and do not "
    "remove the `sorry`. Everything above about following the proof plan applies only when "
    "that block has content."
)


# Pre-delivery verification. Bounded, and off the reference path when set to 0.
#
# The first real run showed why this is worth having: the agent's mathematics was correct --
# it found `natMul_eq_nsmul`, `add_nsmul`, `neg_nsmul`, `add_zsmul` -- and the whole thing
# failed on `open Nat` where it needed `Int`, because `ofNat`/`negSucc` are Int constructors.
# Lean's own error names the fix ("Hint: These are similar: ... 'Int.ofNat'"). The agent
# called lean_diagnostic_messages ONCE in a 39-entry session and never called lean_goal, then
# stopped. That is a verification-discipline failure, not a capability gap, and Mistral's own
# prompt already says "never claim completion without verification".
#
# So before accepting an answer we compile it OURSELVES, with the pinned toolchain, and hand
# the real errors back. Authoritative rather than self-reported.
# DEFAULT 0 -- disabled, on evidence that it does harm.
#
# The verifier re-calls session.act() to hand compiler errors back. Measured effect of those
# re-acts: the MCP tool namespace is re-registered each time, so ONE run showed the same tool
# under three names --
#     lean_local_search 6, lean_mcp_lean_local_search 3, mcp_lean_local_search 1
# and the agent, seeing its tools renamed mid-session, searched 57 entries deep (loogle 17,
# leansearch 14) and never wrote a solution at all. 5 of 6 runs ended with Work.lean still at
# its 15-byte stub. The idea is sound -- the failure it targeted was real, a one-token
# `open Nat` bug Lean itself diagnosed -- but re-acting is the wrong mechanism.
#
# Set to N>0 to re-enable. The right implementation is a POST_AGENT hook, which vibe supports
# (deny -> injected retry, with its own retry cap) and which does NOT re-register tools.
MAX_DELIVERY_CHECKS = int(os.environ.get("AGENT_DELIVERY_CHECKS", "0"))


# ===========================================================================
# 5b. THE TWO HOOKS  --  the mechanism the re-act() verifier should have been
#
# Read from the installed source, not guessed (core/hooks/):
#   * hooks are loaded from FILES: `$VIBE_HOME/hooks.toml` and a trusted project's
#     `.vibe/hooks.toml` (config.load_hooks_from_fs -> HarnessFilesManager.hook_files).
#     `AgentConfig.hooks` has NO reader anywhere in the package -- passing it changes nothing.
#   * `HookConfig.command` is a SHELL COMMAND (executor.HookExecutor uses
#     create_subprocess_shell), fed the invocation as json on stdin, with `timeout` seconds
#     (default 60.0 -- far below one `import Mathlib` compile, hence the explicit value below).
#   * the reply is "exit 0 + one JSON object on stdout": {"decision": "deny", "reason": "..."}.
#     Anything else fails OPEN (a warning, no effect), which is the right failure direction.
#   * pre_tool deny  -> `reason` becomes the tool error the model reads (_pre_tool.py).
#     post_agent deny -> `reason` is injected as a retry user message and the agent loop
#     CONTINUES, capped at 3 retries per hook per user turn (_handler._MAX_RETRIES).
#   * `match` (pre_tool only) accepts `re:` + a regex, fullmatched case-insensitively against
#     the tool name (utils.matching.name_matches).
#
# Why hooks and not another session.act(): re-acting re-registers the MCP namespace, so the
# model saw one tool under three names and stopped writing anything. Hooks run inside the same
# session, so the tool set never moves.
#
# post_agent does NOT fire when the run ends by hitting the turn cap (TurnLimitMiddleware stops
# in before_turn), which is why finalize_answer() below is a separate, harness-side safety net
# rather than a duplicate of this.
# ===========================================================================
HOOKS_ENABLED = os.environ.get("AGENT_HOOKS", "1") != "0"

# The tools that answer "what is in Mathlib" or "would this tactic work". Gated -- never
# removed -- because the runs that scored zero were runs that used these ~30-40 times with an
# empty disk, while the runs that solved the problem used them 2-5 times and then wrote a file.
# Withdrawal is therefore keyed on BUDGET SPENT WITHOUT AN ARTEFACT, not on the search itself.
GATE_TOOLS = ("grep", "m_lean_loogle", "m_lean_leansearch", "m_lean_leanfinder",
              "m_lean_local_search", "m_lean_state_search", "m_lean_hammer_premise",
              "m_lean_references", "m_lean_declaration_file", "m_lean_completions",
              "m_lean_file_outline", "m_lean_run_code", "m_lean_multi_attempt")
# Free searches before a theorem must exist. The three solved trajectories read for this round
# used 2, 3 and 5 of these tools before their first write; the two runs that explored until the
# turn cap and wrote nothing used 31 and 48. 14 is above the former and below the latter.
GATE_FREE_SEARCHES = int(os.environ.get("AGENT_GATE_FREE", "14"))
# And the gate gives up rather than deadlocking a run that will not write.
GATE_MAX_DENIALS = int(os.environ.get("AGENT_GATE_DENIALS", "6"))
# Delivery denials, and how many of them may spend a full compile. vibe's own cap is 3, so
# three of each lets every denial carry fresh compiler output rather than a stale verdict.
#
# MEASURED before choosing these, because the parent's comments assume a compile is expensive:
# `lean` on a file that is `import Mathlib` plus one small theorem takes 5.8 s wall with a warm
# page cache -- and 5.3 GB peak RSS. So the cost of this mechanism is memory pressure at 24
# concurrent workers, NOT wall clock, and the bound that matters is how many compiles can be in
# flight at once rather than how long they take. Each compile inside the hook is additionally
# capped in TIME (below) so one pathological proof cannot sit on 5 GB for ten minutes.
VERIFY_MAX_DENIALS = int(os.environ.get("AGENT_VERIFY_DENIALS", "3"))
VERIFY_MAX_COMPILES = int(os.environ.get("AGENT_VERIFY_COMPILES", "3"))
# Per-compile seconds INSIDE a hook only. The hook is its own process and loads the grader
# lazily, so setting this before the first compile_text() call is what makes it take effect --
# and it cannot affect the grade() compile in the harness process or the host re-grade.
HOOK_COMPILE_TIMEOUT = os.environ.get("AGENT_HOOK_COMPILE_TIMEOUT", "240")
# Diagnostics arrive against the grader's scratch copy; see the use below.
SCRATCH_NAME = re.compile(r"\S*_grade\.[0-9a-f]+\.lean")

# ---------------------------------------------------------------------------
# 5d. THE TRIVIALITY PROBE  --  "does this statement say anything?", asked with `lean`
#
# THE FAILURE, MEASURED ON THIS PARENT'S OWN 300 RUNS. 30 instances wrote a file that
# elaborates, carries a real `theorem` and contains no `sorry` -- and earned NOTHING for it,
# because the grader's own guard found the statement closed by its solver tactics alone. One
# read in full (`rightHom_comp_inl_eq_one`) is the shape: the model restates a Mathlib lemma in
# exactly the form Mathlib tags `@[simp]` and proves it by citing that lemma, so
# `simp_all_arith!` discharges the goal without using any hypothesis, the equivalence verdict is
# voided as possibly vacuous, and 30 files sit at 0.15 instead of at 1.00. Nothing in the run
# told the agent this rule exists; it stopped believing it was finished.
#
# THE MECHANISM. Before accepting an answer that compiles, rebuild it as a PROBE -- the same
# context, the same statement, the proof replaced by the guard's own tactic block -- and compile
# that. If `lean` closes it, the statement is one the grader will not credit, and the agent is
# told so, in the same post_agent channel that already hands back compiler errors, with the
# `<informal_theorem>` quoted back beside it.
#
# The tactic list and the way it is assembled mirror the grader's `GUARD_TACTICS` /
# `_solver_proof()` so this cannot disagree with the thing that scores the run. `import Mathlib`
# is prepended because the guard runs against full Mathlib whatever the agent imported.
#
# EVERY UNCERTAIN ANSWER IS "NOT TRIVIAL". A probe that will not parse, will not compile for any
# other reason, or cannot be built at all returns None or False and the answer is accepted --
# the harness must never deny an answer on the strength of its own failed parse.
# ---------------------------------------------------------------------------
PROBE_NAME = "__hevo_probe"
PROBE_MAX_DENIALS = int(os.environ.get("AGENT_PROBE_DENIALS", "1"))

_BR_OPEN, _BR_CLOSE = "([{⟨", ")]}⟩"
_DECL_KW = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(?:theorem|lemma)\b", re.M)
_DECL_NAME = re.compile(
    r"\A([ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(?:theorem|lemma)[ \t]+)([^\s(){}\[\]:⟨]+)")
_END_LINE = re.compile(r"^[ \t]*end\b.*$", re.M)


def _solver_block() -> str:
    """The guard's tactic block, assembled the way the semantic grader assembles it."""
    independent = " ; ".join(f"(all_goals try {t})" for t in PROBE_TACTICS)
    combined = "all_goals (" + " ; ".join(f"(try {t})" for t in PROBE_TACTICS) + ")"
    return "all_goals intros\nfirst | (" + independent + ") | (" + combined + ")"


def _signature_end(text: str) -> int:
    """Index of the `:=` that ends a declaration's SIGNATURE, or -1.

    Depth-aware and comment-aware, because `:=` also appears inside default-valued binders
    (`(n : Nat := 5)`), inside doc comments, and inside string literals -- and taking one of
    those would silently probe a statement the agent never wrote.
    """
    depth, i, n = 0, 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c in _BR_OPEN:
            depth += 1
        elif c in _BR_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return i
        i += 1
    return -1


def split_statement(code: str) -> tuple[str, str, str] | None:
    """(context, statement, indent) for the LAST theorem/lemma in the file, or None.

    `context` is everything above that declaration -- imports, `open`s, `variable`s, earlier
    declarations -- because the guard is asked against the file's OWN context, not against a
    stripped statement.
    """
    ms = list(_DECL_KW.finditer(code or ""))
    if not ms:
        return None
    m = ms[-1]
    context, decl = code[:m.start()], code[m.start():]
    k = _signature_end(decl)
    if k < 0:
        return None
    stmt = decl[:k].rstrip()
    if ":" not in stmt or len(stmt.strip()) < 20:
        return None
    indent = m.group(0)[:len(m.group(0)) - len(m.group(0).lstrip())]
    return context, stmt, indent


def probe_text(code: str) -> str | None:
    """The agent's statement with the guard's proof, ready to compile. None if not buildable."""
    parts = split_statement(code)
    if parts is None:
        return None
    context, stmt, indent = parts
    if "sorry" in context or "sorry" in stmt:
        return None                      # a stubbed context would compile for the wrong reason
    named = _DECL_NAME.sub(lambda mm: mm.group(1) + PROBE_NAME, stmt, count=1)
    body = "\n".join(indent + "  " + ln for ln in _solver_block().splitlines())
    # Any `end` lines that followed the declaration must follow the probe too, or a namespace
    # the agent opened above is left unclosed and the probe cannot compile at all.
    tail = "\n".join(_END_LINE.findall(code[len(context):]))
    head = "" if re.search(r"^\s*import\s+Mathlib\s*$", context, re.M) else "import Mathlib\n"
    return f"{head}{context}{named} := by\n{body}\n{tail}\n"


def sorry_text(code: str) -> str | None:
    """The agent's own file with the proof of its LAST declaration replaced by `sorry`.

    THE ONE EDIT. Everything above that declaration is kept byte for byte -- imports, `open`s,
    `variable`s, earlier lemmas -- and the declaration's SIGNATURE is kept byte for byte too.
    The only thing removed is the tactic block or proof term the agent did not manage to
    finish. So this is neither a rewrite of the agent's Lean nor a synthesis of new Lean: it is
    the agent's statement with the unfinished proof taken out, which is precisely the artefact
    the ladder scores between "does not elaborate" and "compiles".

    Unlike `probe_text` this does NOT prepend `import Mathlib` and does NOT refuse a
    file whose context already holds a `sorry`: the file must stay the agent's own (a missing
    import is the agent's error to own, not ours to paper over), and a stubbed definition plus
    a broken proof is exactly the case where removing the proof is what makes the file elaborate.

    Returns None when there is no declaration to keep.
    """
    parts = split_statement(code)
    if parts is None:
        return None
    context, stmt, indent = parts
    tail = "\n".join(_END_LINE.findall(code[len(context):]))
    return f"{context}{stmt} := by\n{indent}  sorry\n{tail}\n"


# ---------------------------------------------------------------------------
# THE SAME DEGRADE, FILE-WIDE  --  for the answers `sorry_text` cannot reach
#
# `sorry_text` edits the LAST declaration only. That is the right shape for a file that is one
# theorem whose proof ran out of road, and it is the wrong shape for the cohort that actually
# dominates the non-elaborating band. Measured on the parent's 509 instances, per rung:
#
#     rung                 theorems/file   own defs/file   mean chars
#     solved                        1.09            0.12        1,006
#     incomplete_faithful           1.04            0.13          581
#     compiles                      1.83            0.93        1,663
#     incomplete                    2.18            1.20        1,553
#     no_elaborate                  4.80            2.63        4,263
#
# The 65 files that did not elaborate carry nearly five theorems and two and a half definitions
# each, 72% of them declare more than one theorem, and 49 of the 65 were cut off at the turn
# cap. In a file like that the step that will not compile is very rarely in the last
# declaration, so replacing only that one leaves the error exactly where it was and the run
# keeps the bottom rung with a complete statement sitting on disk above the break.
#
# So: every declaration that has a body gets `:= sorry`, and every SIGNATURE is kept byte for
# byte. It is the same trade `sorry_text` makes -- the equivalence grader ignores proofs
# entirely, so dropping one cannot weaken a statement -- applied to the whole file.
#
# WHAT IS PRESERVED. Everything between declarations (`open`, `variable`, `namespace`,
# `section`, `end`, `notation`, comments) stays where it is, and a declaration's body is taken
# to end at the first following line that starts in column 0 -- Lean's own layout rule for a
# tactic block or a term written under its signature. A declaration with no top-level `:=` (a
# `structure`, an `inductive`, an equation-style `def` with `|` alternatives, an
# `instance ... where`) is copied through untouched rather than guessed at.
#
# AND IT CANNOT COST ANYTHING. It is offered to `finalize_answer` only after every version the
# agent wrote has already failed to compile, and it reaches the graded path only if it compiles
# itself. A mis-parse just produces another file that does not compile, which is the situation
# it was called in. In statement-only mode it is if anything more apt than with a proof: the
# `sorry` it leaves behind is the answer that mode asks for.
# ---------------------------------------------------------------------------
_ANY_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local|partial|unsafe|nonrec)[ \t]+)*"
    r"(theorem|lemma|example|def|abbrev|instance|structure|inductive|class)\b", re.M)
# The keywords whose body is a proof or a value, i.e. the ones `:= sorry` is valid for.
_SORRYABLE = ("theorem", "lemma", "example", "def", "abbrev", "instance")


def _body_end(block: str, k: int) -> int:
    """Index in `block` just past the body whose `:=` is at `k`.

    The body runs to the first following line that begins in column 0 and is not blank. That
    is deliberately Lean's layout rule rather than a bracket count: a tactic block is indented
    under its signature, and the next top-level thing -- another declaration, an `end`, an
    `open` -- is not.
    """
    nl = block.find("\n", k)
    if nl < 0:
        return len(block)
    pos = nl + 1
    while pos < len(block):
        nxt = block.find("\n", pos)
        line = block[pos:] if nxt < 0 else block[pos:nxt]
        if line.strip() and not line[:1].isspace():
            return pos
        if nxt < 0:
            return len(block)
        pos = nxt + 1
    return len(block)


def file_sorry_text(code: str, *, definitions: bool = True) -> str | None:
    """Every declaration's body replaced by `sorry`, signatures kept byte for byte.

    `definitions=False` spares `def`/`abbrev`/`instance` bodies and is the gentler of the two,
    so it is tried first: a definition stubbed with `sorry` still elaborates, but it can make
    the theorem above it unprovable for a reason that was never the agent's.

    Returns None when there is nothing to change or nothing worth keeping.
    """
    src = code or ""
    ms = list(_ANY_DECL.finditer(src))
    if not ms:
        return None
    starts = [m.start() for m in ms]
    kws = [m.group(1) for m in ms]
    bounds = starts + [len(src)]
    out = [src[:starts[0]]]
    changed = False
    for i, kw in enumerate(kws):
        block = src[bounds[i]:bounds[i + 1]]
        touch = kw in _SORRYABLE and (definitions or kw in ("theorem", "lemma", "example"))
        k = _signature_end(block) if touch else -1
        if k < 0 or "sorry" in block[:k]:
            out.append(block)
            continue
        out.append(block[:k].rstrip() + " := sorry\n" + block[_body_end(block, k):])
        changed = True
    if not changed:
        return None
    text = "".join(out)
    return text if HAS_THEOREM.search(text) else None


def statement_is_trivial(code: str) -> bool | None:
    """True if the solver tactics close this statement alone; False if not; None if unknown.

    None is never collapsed into False: "the probe could not ask the question" and "the answer
    is no" are different, and only the second one is evidence about the agent's statement.
    """
    probe = probe_text(code)
    if probe is None:
        return None
    ok, out = compile_text(probe)
    if ok:
        return True
    low = str(out).lower()
    if "unexpected" in low or "unknown tactic" in low or "could not" in low:
        return None                      # our reconstruction, not the agent's statement
    return False


def informal_theorem(limit: int = 2500) -> str:
    """The `<informal_theorem>` block as the agent was given it, for quoting back at it."""
    for p in (PROJECT / "problem.txt", PROBLEM):
        text = _read_text(p)
        m = re.search(r"<informal_theorem>(.*?)</informal_theorem>", text, re.S)
        if m:
            return m.group(1).strip()[:limit]
        if text.strip():
            return text.strip()[:limit]
    return ""


# ---------------------------------------------------------------------------
# 5f. THE FAITHFULNESS AUDIT  --  the one question nothing in the run ever asks
#
# MEASURED, on this parent's own 300 runs. 69 instances produced a file that elaborates, holds a
# real `theorem`, contains no `sorry` and is NOT closed by the automation -- and states something
# the equivalence grader does not accept as the informal theorem (30 over-generalised or
# unrelated, 18 under-specified, the rest unclassified). That is the largest failure band left in
# this harness, larger than every compile failure and every truncation put together, and no
# mechanism in the run touches it.
#
# Three of those files were read end to end and the shape is the same in each: ONE clause of the
# English is not in the Lean, and everything else -- including the proof -- is right.
#   * the text calls a carrier a monoid; the binder gives it a group,
#   * the text names a decorated variant of a structure; the statement binds the undecorated
#     neighbour of nearly the same name,
#   * the text asserts that two homomorphisms are equal; the statement asserts it at one fixed
#     argument.
#
# And every one of them stopped EARLY: 3, 11 and 12 tool calls against a budget of 90, and 86,
# 102 and 98 seconds against a per-problem limit of 7200. The budget was never the constraint
# here. What is missing is that nothing in the run ever puts the statement and the informal
# theorem side by side and asks whether they agree, so the model's first reading of the English
# is also its last -- and the post_agent hook, which is the one channel that could ask, accepts
# the file the moment it compiles.
#
# THE MECHANISM is exactly that question, asked ONCE, through the channel that already carries
# compiler errors, on the cohort that currently sails through unchallenged. The harness supplies
# only the two things it can supply without judging mathematics: the `<informal_theorem>`
# verbatim, and the agent's OWN signature, lifted out with `split_statement` and quoted back
# unmodified. It asks for a clause-by-clause correspondence in both directions, and it says
# first and plainly that a statement which already matches must be left exactly as it is.
#
# IT WRITES NO LEAN AND EDITS NOTHING -- it asks a question and the agent answers it. The risk it
# does carry is the opposite one: an agent that responds by rewriting a statement that was
# already correct. That is why it fires once, why "change nothing" leads the instruction, and why
# the erosion signals (distinct_constants, chars, one_tactic_proofs) plus the `solved` count are
# what to read if this round loses.
# ---------------------------------------------------------------------------
AUDIT_MAX_DENIALS = int(os.environ.get("AGENT_AUDIT_DENIALS", "1"))


def audit_reason(code: str, *, statement_only: bool = False,
                 informal: str | None = None) -> str | None:
    """The faithfulness question, ready to send -- or None when it cannot be asked honestly.

    None whenever either half is missing: no `<informal_theorem>` to quote, or no signature this
    harness can lift out of the file. A review that quotes a statement the agent did not write,
    or an empty theorem, would send it hunting for a mismatch that is ours and not its own.

    `informal` is an override for selftest, which has no problem.txt on disk; the hook always
    lets it default to the block the agent was actually given.
    """
    informal = informal if informal is not None else informal_theorem()
    parts = split_statement(code)
    if not informal or parts is None:
        return None
    _, stmt, _ = parts
    proof_note = (
        "This problem carries no informal proof, so the `sorry` in that file is the finished "
        "answer and stays. Only the statement is in question."
        if statement_only else
        "The proof is done and is not in question here -- only what it proves is.")
    keep_sorry = " (leave `sorry` as the proof)" if statement_only else ""
    return (
        # The opening line is deliberately NOT "not accepted yet". Every other message this
        # environment sends is a rejection with a defect attached, and the measured response to
        # a rejection is to change something -- which is the one thing that can turn a correct
        # answer into a wrong one here. This one is a review that every answer gets, and it says
        # so before it asks anything.
        f"Automatic statement review. Every answer gets this one; it is not a verdict on yours "
        f"and it is not a compile error. {ANSWER} elaborates, declares a theorem, and is not "
        f"closed by the automation. {proof_note}\n\n"
        "One question is left, and it decides more answers here than the compiler does: does "
        "that theorem SAY what the informal theorem says? Both halves are below, so you do not "
        "have to remember either of them.\n\n"
        "THE THEOREM YOU WERE ASKED TO FORMALIZE, verbatim:\n\n"
        f"<informal_theorem>\n{informal}\n</informal_theorem>\n\n"
        "THE STATEMENT YOU WROTE, as it stands in that file:\n\n"
        f"```lean\n{stmt.strip()}\n```\n\n"
        "Walk the English one clause at a time and say, for each clause, which part of that "
        "signature carries it:\n"
        "1. every object it introduces, AND the structure it gives that object -- the structure "
        "named, not a stronger or a weaker one;\n"
        "2. every hypothesis it assumes, including ones stated in passing mid-sentence rather "
        "than after an `if`;\n"
        "3. every quantifier, and whether it ranges over what the English says it ranges over;\n"
        "4. the conclusion, whole: both sides of it, and its exact form.\n\n"
        "Then the reverse direction, which is the half that gets skipped: is there anything in "
        "your signature the English does not ask for -- an added hypothesis, a stronger "
        "structure, a fixed value where the text quantifies?\n\n"
        "These mismatches all survive the compiler, so they are worth checking with a tool "
        "rather than from memory:\n"
        f"- The structure on a carrier is not the one named. `{MCP_ALIAS}_lean_hover_info` on "
        "your own binder says what it actually assumes.\n"
        "- A named definition replaced by a neighbour with nearly the same name -- a variant "
        "with or without a decoration, a prime, a prefix, a different arity. Hover the constant "
        "you used and read what it is defined as: if the informal theorem names a particular "
        "object, the constant in your statement has to BE that object.\n"
        # The mismatch this round measured: 13 of the 24 rejected-as-unrelated answers on the
        # parent's arm had a parenthetical gloss in the informal theorem and had formalized the
        # gloss. The review has to be able to NAME that, or the clause walk reads as a match --
        # the gloss and the notion say the same thing in English, so nothing looks missing.
        "- A named notion replaced by its own parenthetical gloss. Where the text says \"P "
        "(i.e., <the property spelled out>)\", the statement should assume the library's "
        "predicate for P, not the spelled-out property; the gloss identifies the notion and is "
        "not what to transcribe. Search for the predicate by name, hover it to confirm its "
        "definition is that property, and only then use it -- and if you cannot confirm it, "
        "leave the explicit form alone rather than swap in a name you are unsure of. The same "
        "goes for how the hypothesis is BOUND: an element of a set is normally a variable plus "
        "a membership hypothesis, not a subtype.\n"
        "- An equality of two functions or homomorphisms stated at one fixed argument instead "
        "of as an equality of the maps, or the other way round.\n"
        "- A hypothesis needed to state the theorem quietly dropped, or a conclusion stated for "
        "one object where the English states it for all of them.\n"
        "- The numeric type. ℕ subtraction truncates and ℕ division floors, so a statement that "
        "mentions either in the wrong type is true and is not what was meant.\n\n"
        "Name the clause you are LEAST sure of and check that one with a tool before you "
        "decide.\n\n"
        "THEN, one of two things:\n"
        "- A clause is missing, or an object is not the object named: fix the STATEMENT in "
        f"{ANSWER} and bring the proof back into line with it{keep_sorry}. A matching statement "
        "with an unfinished proof is worth far more than a finished proof of the wrong theorem.\n"
        "- Every clause maps: CHANGE NOTHING. Do not rephrase it, generalise it, tidy it, or "
        "swap a definition for an equivalent one. Say in one line that it matches, and stop. "
        "Nothing further will be asked, and a correct statement rewritten for its own sake is "
        "the most expensive mistake available to you now.")


# ---------------------------------------------------------------------------
# 5e. THE BUDGET  --  a searching phase and a landing phase, with the switch in the harness
#
# Two separate budgets can end a run, and the parent watched only one of them.
#
#   SECONDS. The container is killed at 5400 s and a killed problem produces NO result, which
#           is strictly worse than any answer. This fence was built for that and it works: 0 of
#           509 runs were killed. It is also, measurably, the fence that never fires -- p90 was
#           2410 s against a soft threshold of 2900 s, so the TOOL WITHDRAWAL wired up here was
#           reached by a handful of runs at most, and the forced landing it implements was in
#           practice dead code.
#   TURNS.  Which is the budget that actually binds. 123 of 509 runs ended on `Turn limit of 90
#           reached`, and that cohort holds nearly all the remaining failure mass: 49 of them
#           ended with a file that does not elaborate, 42 with an unfinished one, 21 with a
#           verified statement and no proof -- and 2 with a solved problem. Mean value 0.195
#           against 0.608 for the runs that ended on their own terms.
#
# THE CHANGE IS TO KEY THE EXISTING WITHDRAWAL ON THE BUDGET THAT BINDS. Past LAND_FRACTION of
# the turn budget the run enters a LANDING PHASE: the search-and-shell tools are refused, and
# the model is told, in the same breath, to make the file on disk elaborate around whatever will
# not close. Nothing about the mechanism is new -- the parent already refuses those tools past
# RESERVE_HARD_SECONDS, with almost the same words -- what is new is a threshold that a
# truncated run actually crosses, at a point where there are still turns left to land in.
#
# Why a landing is worth turns at all: the distance from `no_elaborate` to `incomplete` is one
# `sorry` in the step that will not close, and the distance from there to `incomplete_faithful`
# is nothing at all -- the statement is already written. 49 runs held a broken file when the
# counter ran out. None of them was being asked to stop.
#
# COUNTED IN TOOL CALLS, NOT IN EXPLORATION CALLS (see TICKS). That is what makes the threshold
# mean what it says: the parent's counter ignored every write, every compile and every
# diagnostic, so a run that had spent 70 turns proving things looked like a run that had spent
# 25. This hook is now matched against EVERY tool so that it sees them all.
#
# Both phases speak through a pre_tool deny, because that is the only channel vibe gives a hook
# for putting text in front of the model mid-session (`reason` becomes the tool error the model
# reads). The notices are rationed to one per threshold and the landing denials are capped, so
# the cost of being told is bounded in turns.
#
# NOTHING OUTSIDE `LAND_WITHDRAW` IS EVER REFUSED. The hook now matches every tool in order to
# COUNT it, and the very first thing it does with a tool that is not in that tuple is allow it.
# `write_file`, `edit` and the diagnostics therefore cannot be blocked by any threshold here,
# including the last one -- a budget notice must never be able to refuse the write it is asking
# for.
#
# BOTH INPUT MODES. The landing message is the only text here that could be wrong in
# statement-only mode, and it asks `proof_block_present()` before it is built: with an empty
# `<informal_proof>` it says to leave the `sorry` and check the statement, not to go on hunting
# a proof. The withdrawal itself is mode-independent -- the searching phase is over either way.
# ---------------------------------------------------------------------------
# THE TOOLS THE LANDING PHASE WITHDRAWS, and the ones it deliberately keeps.
#
# Narrower than the parent's list by two entries, and both omissions are load-bearing. Landing
# means editing the file you already have: `read_file` is how the model re-reads its own answer
# before an `edit` (its own prompt forbids editing a file it has not read this session, so
# refusing this can refuse the repair itself), and `m_lean_hover_info` is how it checks one
# identifier's type while fixing a coercion. Neither opens a new line of search.
#
# Everything the model uses to LOOK FOR SOMETHING NEW is withdrawn: the shell, the file
# searches, and every premise-search backend. What remains -- write_file, edit, lean_goal,
# lean_diagnostic_messages, lean_run_code, lean_multi_attempt, lean_verify, read_file,
# hover_info -- is exactly the toolkit for making a file elaborate.
LAND_WITHDRAW = ("bash", "grep", "glob", "m_lean_loogle", "m_lean_leansearch",
                 "m_lean_leanfinder", "m_lean_local_search", "m_lean_state_search",
                 "m_lean_hammer_premise", "m_lean_references", "m_lean_declaration_file",
                 "m_lean_completions", "m_lean_file_outline", "m_lean_profile_proof")
# Fractions of the turn budget at which the two INFORMATIONAL notices fire, counted in total
# tool calls (see TICKS) rather than in exploration calls. A tool call is very close to a turn
# here: the run that hit the 90-turn cap hardest made 92 of them.
#
# The parent counted exploration calls only and fired at 0.55/0.80 of the budget, which put the
# first notice past three quarters of a real run and the second one after there was nothing left
# to do with it. Measured tool-call medians on its arm: 28 for solved, 95-97 for every truncated
# band. 0.50 and 0.70 sit above the former and below the latter.
RESERVE_FRACTIONS = (0.50, 0.70)
# LAND_FRACTION and LAND_MAX_DENIALS are in section 1, beside PROBE_TACTICS, because the task
# text announces the phase and this hook enforces it and the two must not disagree. 0.82 of 100
# turns leaves 18 for the landing -- several write/diagnose cycles -- and touches 7 of the
# parent's 182 solved runs (which used >= 82 tool calls) against 112 of its 148 truncated
# non-solved ones.
# Seconds. SOFT: one notice that the clock, not the turn counter, is what will end this run.
# HARD: every exploration call is refused from here on, which starves the search loop and
# leaves only writing, editing and diagnostics -- a forced landing well inside the 7200 s kill,
# with room for the verifier's compile and the final grade behind it.
RESERVE_SOFT_SECONDS = int(os.environ.get("AGENT_RESERVE_SOFT", "2900"))
RESERVE_HARD_SECONDS = int(os.environ.get("AGENT_RESERVE_HARD", "3700"))


# ---------------------------------------------------------------------------
# 5g. WRITE-THROUGH  --  `write_file` creates only, and that breaks the main loop
#
# THE FAILURE, MEASURED ON THIS PARENT'S OWN 300 RUNS, and it is the most widespread mechanical
# waste in the arm: 183 of 555 `write_file` calls FAILED -- 33% of every write attempted -- with
# "File '.../Work.lean' already exists. Use edit to modify it." 181 of the 183 were aimed at the
# graded file. 115 of 300 problems hit it at least once, one hit it nine times.
#
# It is not a prompt failure and it cannot be fixed by prose: the parent's TASK already spelled
# out both the rule and the `rm`-then-write escape hatch, and the model walked into it anyway 183
# times, because rewriting the whole file is the loop autoformalization actually has. vibe's
# WriteFileArgs has no overwrite flag and `_prepare_and_validate_path` raises unconditionally
# (core/tools/builtins/write_file.py:138), so the tool as published cannot do what is wanted.
#
# The recovery costs a SECOND turn, and its shape is the interesting part: 60 of the 183 were
# followed by `bash` (the rm) and another `write_file`, and 101 by `edit`, 32 of those after a
# re-`read_file`. So the failure does not only burn ~275 turns across the arm; on 101 occasions
# it converted a whole-file rewrite the model had already composed into a patch applied to a copy
# it was no longer sure of -- and `edit` itself failed 28 times on stale matches.
#
# THE MECHANISM. A pre_tool hook on `write_file`: if the target is an ordinary `.lean` file
# inside this workspace and the call carries real content, the existing file is moved aside
# (`os.replace`, atomic) and the call is ALLOWED, so the create finds nothing in its way. The
# model's own `write_file` therefore behaves as a replace. No new tool, no tool description
# change, nothing for the model to learn beyond the one prompt paragraph that used to teach the
# `rm` dance.
#
# IT CAN NEVER DENY ANYTHING, in either input mode. It has one decision -- "allow" -- and one
# side effect, and it does not read the file's contents, does not look for `sorry`, and does not
# know or care whether the input carried an informal proof. Nothing about the two input modes
# reaches it.
#
# WHY THE ANSWER CANNOT BE LOST. Four guards, in order of how much they matter:
#   * the clear is REFUSED unless `tool_input` carries a non-empty `content` no larger than
#     vibe's own `max_write_bytes`, so the two ways the following write could still fail
#     (empty path, oversized content) never see a cleared file;
#   * only a real, non-symlink `*.lean` file strictly under WORK, outside `.lake`, is ever
#     touched -- never `problem.txt`, never the grader's `_grade.*` scratch, never Mathlib;
#   * the previous bytes are kept at a dot-prefixed sidecar which `stray_answers()`'s `*.lean`
#     glob deliberately does NOT match, so it can never be resurrected as an answer by accident;
#   * and `Snapshots.observe()` in the harness process has already read every version that
#     reached disk through a tool call, so `finalize_answer` retains the full ladder of previous
#     answers whatever happens here.
# ---------------------------------------------------------------------------
WRITE_TOOLS = ("write_file",)
# A bound, not a policy: a run that rewrites the file sixty times has a different problem, and
# past the cap this hook stops acting and the model sees vibe's ordinary error again.
WRITE_MAX_CLEARS = int(os.environ.get("AGENT_WRITE_CLEARS", "60"))
# vibe's WriteFileConfig.max_write_bytes default. Mirrored so a call that will be refused for
# size does not get a cleared file first.
WRITE_MAX_BYTES = int(os.environ.get("AGENT_WRITE_MAX_BYTES", "64000"))


def write_match() -> str:
    """The `match` expression for the write-through hook."""
    return "re:(" + "|".join(re.escape(t) for t in WRITE_TOOLS) + ")"


def _hook_tool_path(inv: dict) -> Path | None:
    """The path a pre_tool invocation is aimed at, resolved the way the tool resolves it.

    `ToolPath` is a plain (normalised) string, so the model may hand over a relative path;
    `resolve_tool_path` anchors it to the session cwd, and the invocation carries that cwd.
    Both the snake_case field name (what `model_dump()` emits) and the camelCase one (what the
    UI projection uses) are accepted, because only one of them is guaranteed by the code read.
    """
    ti = inv.get("tool_input")
    if not isinstance(ti, dict):
        return None
    raw = None
    for k in ("file_path", "filePath", "path"):
        v = ti.get(k)
        if isinstance(v, str) and v.strip():
            raw = v.strip()
            break
    if raw is None:
        return None
    cwd = inv.get("cwd")
    try:
        p = Path(raw)
        if not p.is_absolute():
            p = Path(str(cwd) if isinstance(cwd, str) and cwd else str(PROJECT)) / p
        return Path(os.path.abspath(str(p)))
    except (OSError, ValueError):
        return None


def _hook_write_content_ok(inv: dict) -> bool:
    """True only when the pending write would itself succeed once the path is free."""
    ti = inv.get("tool_input")
    if not isinstance(ti, dict):
        return False
    content = ti.get("content")
    if not isinstance(content, str) or not content.strip():
        return False
    try:
        return len(content.encode("utf-8")) <= WRITE_MAX_BYTES
    except (UnicodeError, ValueError):
        return False


def clearable(path: Path) -> bool:
    """True when this harness may move `path` aside so a create-only write can land.

    Deliberately narrow. The one thing this must never do is destroy something that is not a
    version of the answer, so the predicate is a whitelist: an ordinary file, not a symlink, a
    `.lean` suffix, strictly inside WORK, not under `.lake` (the read-only Mathlib mount seen
    through the project's symlink) and not the grader's own scratch copy.
    """
    try:
        p = Path(os.path.abspath(str(path)))
        if p.suffix != ".lean" or p.name.startswith("_grade."):
            return False
        if p.is_symlink() or not p.is_file():
            return False
        if ".lake" in p.parts:
            return False
        return Path(os.path.abspath(str(WORK))) in p.parents
    except OSError:
        return False


def hook_write() -> int:
    """pre_tool: let a whole-file rewrite land, by moving the previous version aside first."""
    real, sys.stdout = sys.stdout, sys.stderr
    try:
        inv = _hook_stdin()
        target = _hook_tool_path(inv)
        if target is None or not clearable(target) or not _hook_write_content_ok(inv):
            return _hook_reply({"decision": "allow"}, real)
        st = state_read()
        cleared = int(st.get("write_clears", 0))
        if cleared >= WRITE_MAX_CLEARS:
            return _hook_reply({"decision": "allow"}, real)
        # Dot-prefixed and NOT `*.lean`, so `stray_answers()` cannot pick it up: the previous
        # version is kept for forensics, not offered back as an answer.
        prev = target.with_name(f".{target.name}.hevo-prev")
        try:
            os.replace(str(target), str(prev))
        except OSError as e:
            print(f"[hook-write] {type(e).__name__}: {e}", file=sys.stderr)
            return _hook_reply({"decision": "allow"}, real)
        st["write_clears"] = cleared + 1
        st["write_cleared_last"] = str(target)
        state_write(st)
        return _hook_reply({"decision": "allow",
                            "system_message": f"replacing {target.name}"}, real)
    except Exception as e:                          # noqa: BLE001 - fail OPEN, never block
        print(f"[hook-write] {type(e).__name__}: {e}", file=sys.stderr)
        return _hook_reply({"decision": "allow"}, real)
    finally:
        sys.stdout = real


# ---------------------------------------------------------------------------
# 5h. THE SOUNDNESS GUARD  --  the constructs that void the answer, refused at the keyboard
#
# MEASURED, on the parent's own 509 graded instances: 8 answers were DISQUALIFIED. Seven of
# them used `native_decide` and one set `maxHeartbeats 0`. Every one of them compiled cleanly,
# had no `sorry`, and was scored as if no theorem had been proved -- all eight landed on
# `incomplete` or below, and one of them used `native_decide` fifty-one times.
#
# That is not a mathematics failure and it is not a budget failure. It is the model reaching for
# a tactic it knows works, in an environment where the graded artefact is scanned for it
# afterwards and thrown away. The parent's prompt says `native_decide` "is not good for you",
# which is true and does not say that the run is over if you use it -- and prose is the wrong
# instrument anyway, because the cost falls on a file the model never sees rejected.
#
# THE MECHANISM is a pre_tool hook on the two tools that put text on disk. The content of the
# pending write is scanned for the disqualifying constructs, and if one is there the call is
# refused with the construct named and the consequence stated. The model then writes the file
# without it, which is the only outcome anyone wants.
#
# THE PATTERNS ARE A MIRROR, not a policy of ours. They are transcribed from the scan the
# runner applies to the finished file, exactly as `PROBE_TACTICS` mirrors the grader's
# triviality guard -- so this refuses what is actually thrown away, and nothing else. A
# construct that is merely inadvisable is not in this list.
#
# IT CANNOT COST AN ANSWER. Bounded at SOUND_MAX_DENIALS refusals per problem, after which the
# hook allows everything: a model that insists still gets its file on disk (disqualified, which
# is exactly where it already was), and the guard can never be the reason nothing was written.
# Both input modes are identical here -- none of these constructs is a `sorry` and none of them
# depends on whether an informal proof was supplied.
# ---------------------------------------------------------------------------
SOUND_TOOLS = ("write_file", "edit")
SOUND_MAX_DENIALS = int(os.environ.get("AGENT_SOUND_DENIALS", "3"))

# Transcribed from the runner's own disqualifier scan. Each entry is (pattern, what it costs).
DISQUALIFIERS: tuple[tuple[re.Pattern, str], ...] = (
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private|protected|scoped|local)?\s*axiom\b", re.M),
     "declares an `axiom` -- a new axiom can prove anything, so the file is not a proof"),
    (re.compile(r"\bsorryAx\b"),
     "names `sorryAx`, the constant `sorry` elaborates to"),
    (re.compile(r"\bnative_decide\b"),
     "uses `native_decide`, which trusts compiled code instead of the kernel"),
    (re.compile(r"\bLean\.ofReduceBool\b|\bLean\.ofReduceNat\b"),
     "names the `native_decide` trust axioms directly"),
    (re.compile(r"@\[\s*implemented_by\b"),
     "uses `@[implemented_by]`, which swaps a definition for unverified code"),
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*unsafe\b", re.M),
     "declares something `unsafe`, which escapes the termination and soundness checks"),
    (re.compile(r"set_option\s+(?:debug\.skipKernelTC|maxHeartbeats\s+0|"
                r"trace\.Meta\.synthInstance)\b"),
     "sets an option that disables or unbounds a soundness check"),
)
# Import roots the graded file may use. Anything else could resolve to a module built on the
# writable mount, so the runner treats it as a disqualifier too.
IMPORT_ROOTS = ("Mathlib", "Init", "Std", "Batteries", "Aesop", "Qq", "ImportGraph",
                "ProofWidgets", "Plausible", "LeanSearchClient", "Cli",
                # cslib is a pinned dependency of the project (setup/lean_project/), built into
                # the same read-only packages tree as Mathlib, so an import of it resolves to
                # prebuilt oleans exactly as Mathlib's do.
                "Cslib")
_IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][\w.]*)", re.M)


def disqualifier(text: str) -> str | None:
    """Why this Lean would be thrown out whatever the compiler says, or None.

    The first reason only, so the message names one concrete thing to remove rather than a
    list. Comments are NOT stripped before scanning, deliberately: the scan that decides the
    score does not strip them either, so a `native_decide` parked in a comment costs the run
    just the same and had better be refused just the same.
    """
    if not text or not text.strip():
        return None
    for pat, why in DISQUALIFIERS:
        if pat.search(text):
            return why
    for m in _IMPORT_LINE.finditer(text):
        if m.group(1).split(".")[0] not in IMPORT_ROOTS:
            return (f"imports {m.group(1)!r}, which is outside the allowed roots "
                    f"{list(IMPORT_ROOTS)}")
    return None


def sound_match() -> str:
    """The `match` expression for the soundness guard: the tools that put text on disk."""
    return "re:(" + "|".join(re.escape(t) for t in SOUND_TOOLS) + ")"


def _hook_new_text(inv: dict) -> str:
    """The text a pending `write_file` or `edit` would put into the file.

    `content` is WriteFileArgs'; `new_string` is EditArgs'. Only the NEW text is read -- an
    `edit` whose `old_string` holds a forbidden construct is REMOVING it, and refusing that
    would be exactly backwards.
    """
    ti = inv.get("tool_input")
    if not isinstance(ti, dict):
        return ""
    parts = [ti.get(k) for k in ("content", "new_string", "newString", "new_str")]
    return "\n".join(p for p in parts if isinstance(p, str))


def hook_sound() -> int:
    """pre_tool: refuse a write that would put a disqualifying construct into the answer."""
    real, sys.stdout = sys.stdout, sys.stderr
    try:
        inv = _hook_stdin()
        target = _hook_tool_path(inv)
        if target is None or target.suffix != ".lean":
            return _hook_reply({"decision": "allow"}, real)
        why = disqualifier(_hook_new_text(inv))
        if why is None:
            return _hook_reply({"decision": "allow"}, real)
        st = state_read()
        denials = int(st.get("sound_denials", 0))
        if denials >= SOUND_MAX_DENIALS:
            return _hook_reply({"decision": "allow"}, real)
        st["sound_denials"] = denials + 1
        state_write(st)
        return _hook_reply({"decision": "deny", "reason": (
            f"Not written. That text {why}.\n\n"
            f"A file containing it is DISQUALIFIED when your answer is graded: it is scored as "
            f"if the theorem had never been proved, however cleanly it compiles and however "
            f"correct the mathematics is. This is not a style note and it is not negotiable by "
            f"proving that the computation is right -- the construct itself is what voids the "
            f"file.\n\n"
            f"Write the same file without it. If a `decide` will not finish in time, prove the "
            f"statement with lemmas instead of deciding it; if a definition needs "
            f"well-foundedness you cannot show, state the theorem about the library's version "
            f"of the object instead of defining your own. Removing the construct is always "
            f"possible and is never a reason to weaken the statement.")}, real)
    except Exception as e:                          # noqa: BLE001 - fail OPEN, never block
        print(f"[hook-sound] {type(e).__name__}: {e}", file=sys.stderr)
        return _hook_reply({"decision": "allow"}, real)
    finally:
        sys.stdout = real


def gate_match() -> str:
    """The `match` expression for the pre_tool gate: an anchored alternation of tool names."""
    return "re:(" + "|".join(re.escape(t) for t in GATE_TOOLS) + ")"


def reserve_match() -> str:
    """The `match` expression for the budget hook: EVERY tool, so that every call is counted.

    Matching is not permission. The hook refuses only tools in `LAND_WITHDRAW`; everything
    else is counted and allowed on the first branch of hook_reserve(). Matching narrowly --
    which is what the parent did -- is what made its counter blind to two thirds of the run.

    `re:` + a regex is vibe's own form (utils/matching.name_matches), fullmatched
    case-insensitively against the tool name, so `.*` matches every published name including
    the MCP ones.
    """
    return "re:.*"


def hooks_toml(python: str | None = None, script: str | None = None) -> str:
    """The hooks file, pointing all five hooks back at THIS harness file.

    Self-referential on purpose: the harness is staged into a directory whose path it does not
    choose (and which differs between the container and the local-execution shim), so
    `__file__` is the only reliable way to name the script that must run. `sys.executable` is
    likewise the interpreter that was able to import this file in the first place.

    THE ORDER IS LOAD-BEARING, and it is file order: vibe runs the matching hooks in the order
    they appear here and STOPS the chain at the first `deny` (hooks/manager.py:191). So
    `answer_sound` must come before `write_through` -- if the order were reversed, a refused
    write would arrive after the previous version had already been moved aside, and the run
    would spend a turn with nothing at the graded path. `budget_reserve` leads because it
    counts every call and its own denials never touch a write.
    """
    import shlex
    py = shlex.quote(python or sys.executable or "python3")
    me = shlex.quote(script or str(Path(__file__).resolve()))
    return f"""\
[[hooks]]
name = "budget_reserve"
type = "pre_tool"
match = {json.dumps(reserve_match())}
command = "{py} {me} hook-reserve"
timeout = 30.0
description = "Count every tool call; notice, then withdraw search near the end of the budget."

[[hooks]]
name = "answer_sound"
type = "pre_tool"
match = {json.dumps(sound_match())}
command = "{py} {me} hook-sound"
timeout = 30.0
description = "Refuse a write that would put a disqualifying construct into the answer."

[[hooks]]
name = "write_through"
type = "pre_tool"
match = {json.dumps(write_match())}
command = "{py} {me} hook-write"
timeout = 30.0
description = "Move the previous version aside so a create-only write_file can replace a file."

[[hooks]]
name = "answer_gate"
type = "pre_tool"
match = {json.dumps(gate_match())}
command = "{py} {me} hook-gate"
timeout = 30.0
description = "Withhold Mathlib search while no theorem has been written."

[[hooks]]
name = "answer_verify"
type = "post_agent"
command = "{py} {me} hook-verify"
timeout = 900.0
description = "Compile the answer with the pinned toolchain, and probe that it says something."
"""


def _hook_reply(payload: dict, out) -> int:
    """The only writer of the real stdout in hook mode.

    Stdout is the wire: one JSON object, nothing else. Everything in between -- the grader
    import, `lean` itself, our own prints -- is pointed at stderr for the duration, because a
    stray line on stdout is parsed as the response, fails the schema, and silently reduces the
    hook to a no-op.
    """
    out.write(json.dumps(payload))
    out.flush()
    return 0


def _hook_stdin() -> dict:
    """Drain stdin and parse it. Draining is not optional: vibe awaits drain() on the hook's
    stdin, so a hook that never reads can block until its timeout and fail open."""
    try:
        raw = sys.stdin.read()
    except (OSError, ValueError):
        return {}
    try:
        return json.loads(raw) if raw.strip() else {}
    except (json.JSONDecodeError, ValueError):
        return {}


def hook_gate() -> int:
    """pre_tool: deny a search once the budget is spent and there is still no theorem."""
    real, sys.stdout = sys.stdout, sys.stderr
    try:
        _hook_stdin()
        if HAS_THEOREM.search(answer_text()):
            return _hook_reply({"decision": "allow"}, real)   # the gate is over, for good
        st = state_read()
        st["gate_calls"] = calls = int(st.get("gate_calls", 0)) + 1
        denials = int(st.get("gate_denials", 0))
        if calls <= GATE_FREE_SEARCHES or denials >= GATE_MAX_DENIALS:
            state_write(st)
            return _hook_reply({"decision": "allow"}, real)
        st["gate_denials"] = denials + 1
        state_write(st)
        return _hook_reply({
            "decision": "deny",
            "reason": (
                f"Withheld: {calls} searches have been made and {ANSWER} still contains no "
                f"`theorem`. Write your current best statement there now -- `sorry` for the "
                f"proof is fine, a rough statement is fine, and you may rewrite it completely "
                f"afterwards. The search tools come back as soon as that file holds a "
                f"theorem. Searching with nothing on disk is scored the same as writing "
                f"nothing at all."),
        }, real)
    except Exception as e:                          # noqa: BLE001 - fail OPEN, never block
        print(f"[hook-gate] {type(e).__name__}: {e}", file=sys.stderr)
        return _hook_reply({"decision": "allow"}, real)
    finally:
        sys.stdout = real


def landing_reason(calls: int, turns: int, *, short: bool = False,
                   statement_only: bool | None = None) -> str:
    """What the model is told when the searching phase is over.

    Mode-aware: with an EMPTY `<informal_proof>` a `sorry` is the finished proof, so the
    landing asks for a complete statement and nothing else. `proof_block_present()` fails open
    (True), so an unreadable input is treated as the stricter with-proof task.
    """
    if statement_only is None:
        statement_only = not proof_block_present()
    left = max(0, turns - calls)
    if short:
        return (f"Still landing: about {left} turns remain and the search tools stay closed "
                f"until this run ends. Put your work into {ANSWER} and make it elaborate.")
    keep = (
        "This problem gives you no informal proof, so `sorry` IS the proof to leave behind. "
        "Spend what is left making sure the statement is the whole informal theorem and that "
        "the file elaborates around it."
        if statement_only else
        "Keep the statement exactly as it stands -- every binder, every hypothesis, the whole "
        "conclusion -- and put `sorry` in each proof step that will not close, as many as it "
        "takes, until the file is error-free. A file that elaborates with the right statement "
        "and an unfinished proof is scored as real progress; a file that does not elaborate is "
        "scored as almost nothing. Do NOT make the theorem say less to make the errors go "
        "away: that is scored as a wrong statement, which is worse than an unfinished one.")
    return (
        f"Budget: you have made {calls} tool calls of about {turns}, so roughly {left} turns "
        f"remain and the run simply stops when they are gone -- whatever is in {ANSWER} at that "
        f"moment is your answer, and no further warning comes.\n\n"
        f"The searching phase is over. Mathlib search, `grep` and the shell are refused from "
        f"here on. `write_file`, `edit`, `read_file`, `{MCP_ALIAS}_lean_diagnostic_messages`, "
        f"`{MCP_ALIAS}_lean_goal`, `{MCP_ALIAS}_lean_run_code`, "
        f"`{MCP_ALIAS}_lean_multi_attempt` and `{MCP_ALIAS}_lean_hover_info` all still work -- "
        f"everything you need to finish with what you already have.\n\n"
        f"{keep}\n\n"
        f"Confirm with {MCP_ALIAS}_lean_diagnostic_messages that the file is error-free, then "
        f"stop.")


def hook_reserve() -> int:
    """pre_tool: count every tool call, then run the two-phase budget policy.

    Ordered by severity, and the FIRST branch is the one that makes this safe: a tool that is
    not in `LAND_WITHDRAW` is counted and allowed, whatever any threshold says, so no notice
    and no landing can ever refuse a write, an edit or a diagnostic.

      * past RESERVE_HARD_SECONDS -- the wall-clock fence, uncapped, because a container killed
        with no result is worse than any answer.
      * past LAND_FRACTION of the turn budget -- the landing phase: search and shell refused,
        capped at LAND_MAX_DENIALS so the landing itself cannot be spent on refusals.
      * past RESERVE_SOFT_SECONDS -- one notice that the clock will end this run.
      * past a fraction of the turn budget -- one notice of where it is, with what to do next.
    """
    real, sys.stdout = sys.stdout, sys.stderr
    try:
        inv = _hook_stdin()
        calls = tick()                       # EVERY call, including the ones never refused
        name = str(inv.get("tool_name") or "")
        if name not in LAND_WITHDRAW:
            return _hook_reply({"decision": "allow"}, real)
        st = state_read()
        if calls <= 0:                       # the byte log is unavailable; degrade, never guess
            st["reserve_calls"] = calls = int(st.get("reserve_calls", 0)) + 1
            state_write(st)
        turns = int(st.get("max_turns") or MODEL["max_turns"])
        t0 = float(st.get("t0") or 0.0)
        spent = time.time() - t0 if t0 else 0.0
        seen = list(st.get("reserve_notices") or [])

        def notice(tag: str, reason: str) -> int:
            st["reserve_notices"] = seen + [tag]
            state_write(st)
            return _hook_reply({"decision": "deny", "reason": reason}, real)

        endgame = (
            f"Land it now: {ANSWER} is compiled exactly as it stands when you stop. Make sure "
            f"it holds the FULL statement of the informal theorem and as much of the proof as "
            f"you have. If one step will not close, leave `sorry` in that step only and keep "
            f"the statement complete -- an unfinished proof of the right theorem is worth far "
            f"more than a finished proof of a weaker one. Check it with "
            f"{MCP_ALIAS}_lean_diagnostic_messages, then stop.")

        if t0 and spent > RESERVE_HARD_SECONDS:
            return _hook_reply({
                "decision": "deny",
                "reason": (f"Wall clock exhausted: {int(spent)}s of this problem's limit are "
                           f"gone and the whole run is discarded if it overruns -- a discarded "
                           f"run scores zero however good the file is. Searching and shell "
                           f"commands are refused from here on; writing, editing, reading and "
                           f"the Lean diagnostics still work. " + endgame)}, real)
        if calls >= max(8, int(LAND_FRACTION * turns)):
            dn = int(st.get("land_denials", 0))
            if dn >= LAND_MAX_DENIALS:
                return _hook_reply({"decision": "allow"}, real)
            st["land_denials"] = dn + 1
            state_write(st)
            return _hook_reply({"decision": "deny",
                                "reason": landing_reason(calls, turns, short=dn > 0)}, real)
        if t0 and spent > RESERVE_SOFT_SECONDS and "soft" not in seen:
            return notice("soft", (
                f"Budget notice (automatic, not an error): {int(spent)}s of wall clock spent, "
                f"and it is the clock rather than your turn count that will end this run. Stop "
                f"opening new lines of search. " + endgame))
        for i, frac in enumerate(RESERVE_FRACTIONS):
            tag = f"turns{i}"
            if calls >= max(4, int(frac * turns)) and tag not in seen:
                return notice(tag, (
                    f"Budget notice (automatic, not an error): you have made {calls} tool "
                    f"calls against a budget of about {turns} turns, so roughly "
                    f"{max(0, turns - calls)} remain. Nothing is wrong with the call you just "
                    f"made -- repeat it if you still need it. But from here, finishing beats "
                    f"exploring, and once {int(LAND_FRACTION * 100)}% of the budget is gone "
                    f"the search tools close for the rest of the run. " + endgame))
        return _hook_reply({"decision": "allow"}, real)
    except Exception as e:                          # noqa: BLE001 - fail OPEN, never block
        print(f"[hook-reserve] {type(e).__name__}: {e}", file=sys.stderr)
        return _hook_reply({"decision": "allow"}, real)
    finally:
        sys.stdout = real


def hook_verify() -> int:
    """post_agent: compile the answer with the pinned toolchain; deny with the real errors.

    The failure this exists for was measured: a run whose mathematics was right and whose file
    died on `open Nat` where it needed `Int`, after calling lean_diagnostic_messages once in a
    39-entry session. The compiler already knew; nobody asked it.

    Bounded on both axes -- at most VERIFY_MAX_DENIALS denials and VERIFY_MAX_COMPILES full
    compiles per problem, each capped at HOOK_COMPILE_TIMEOUT seconds -- because an
    `import Mathlib` compile peaks at ~5 GB and this one runs while the LSP is still resident.
    """
    real, sys.stdout = sys.stdout, sys.stderr
    try:
        os.environ.setdefault("AGENT_COMPILE_TIMEOUT", HOOK_COMPILE_TIMEOUT)
        _hook_stdin()
        st = state_read()
        denials = int(st.get("verify_denials", 0))
        if denials >= VERIFY_MAX_DENIALS:
            return _hook_reply({"decision": "allow"}, real)
        text = answer_text()

        def deny(reason: str) -> int:
            s = state_read()
            s["verify_denials"] = int(s.get("verify_denials", 0)) + 1
            state_write(s)
            return _hook_reply({"decision": "deny", "reason": reason}, real)

        head = (f"Not accepted yet. {ANSWER} is your answer and it is checked with this "
                f"project's pinned toolchain before you are finished.\n\n")
        # TWO INPUT MODES, and this hook is the gate that has to know the difference. With an
        # EMPTY `<informal_proof>` the task is statement autoformalization: a faithful statement
        # proved by `sorry` is the COMPLETE answer, so denying delivery over that `sorry` -- which
        # is what this hook did, three times, on every such input -- would burn the whole run
        # hunting a proof nobody asked for. `proof_block_present()` fails OPEN (True), so a
        # problem whose mode cannot be read is treated as the stricter with-proof one.
        statement_only = not proof_block_present()
        # THE LAST CALL. vibe injects at most _MAX_RETRIES (3) retries per hook per user turn,
        # so the denial made when `denials` has already reached VERIFY_MAX_DENIALS - 1 is the
        # final thing this environment will ever say to the model. Repeating "fix the proof"
        # there is the wrong instruction: the parent's own arm shows 26 runs whose last word
        # was a repair request and whose file was still broken when the clock stopped, and 12
        # of those files held a complete statement that would have elaborated with one `sorry`
        # in it. On the last call the ask therefore changes from repair to LANDING -- keep the
        # statement, make the file elaborate around the step that will not close.
        last_call = denials >= VERIFY_MAX_DENIALS - 1
        land = ("\nThis is the LAST automatic check of this run: whatever is in that file when "
                "you stop next is the answer, and nothing will ask you again. So stop "
                "repairing and LAND it. Keep the statement exactly as it stands -- every "
                "binder, every hypothesis, the whole conclusion, the same names -- and replace "
                "each proof step that will not close with `sorry`, as many as it takes, until "
                "the file elaborates with no errors. A file that elaborates with the right "
                "statement and an unfinished proof is scored as real progress; a file that "
                "does not elaborate is scored as nothing at all. Do NOT change the statement "
                "to make the errors go away -- that is scored as a wrong statement, which is "
                f"worse. Confirm with {MCP_ALIAS}_lean_diagnostic_messages that the file is "
                "error-free, then stop.")
        tail = ("\nFix it in that file. Repair the PROOF and the syntax -- do not make the "
                "theorem say less in order to make it compile, and do not delete hypotheses "
                "or specialise the statement. A file that elaborates with a `sorry` in the "
                "step you cannot close is worth more than a file that does not elaborate at "
                "all, and much less than a finished proof, so prefer that over weakening what "
                f"is stated. Lean often names the right identifier in its hint. Check with "
                f"{MCP_ALIAS}_lean_diagnostic_messages before you stop again.")
        if statement_only:
            # Same repair request, with the one instruction that would be wrong here removed:
            # in statement-only mode there is no proof to finish and `sorry` is not a defect.
            tail = ("\nFix it in that file. This problem gives you no informal proof, so "
                    "`sorry` is the proof to leave behind -- do not go hunting for one. Repair "
                    "whatever stops the file from elaborating, keep the statement complete and "
                    "faithful, and do not make the theorem say less in order to make it "
                    f"compile. Check with {MCP_ALIAS}_lean_diagnostic_messages before you stop "
                    "again.")
            land = tail

        if not text.strip():
            return deny(head + f"That file is missing or empty. Write the Lean 4 theorem and "
                               f"its proof to {ANSWER} now." + tail)
        if not HAS_THEOREM.search(text):
            return deny(head + "That file declares no `theorem` or `lemma`, so it formalizes "
                               "nothing. Definitions alone are not an answer." + tail)

        # Cheap syntactic verdict first; a compile is only spent when it can change the answer.
        why = vacuity(text)
        # ... and in statement-only mode the `sorry` the vacuity check objects to IS the answer,
        # so that one objection is dropped. Only that one: any other complaint still stands.
        if statement_only and why and "sorry" in why.lower():
            why = None
        ok = verdict_get(text)
        if ok is None:
            if int(st.get("verify_compiles", 0)) >= VERIFY_MAX_COMPILES:
                return _hook_reply({"decision": "allow"}, real)
            st["verify_compiles"] = int(st.get("verify_compiles", 0)) + 1
            state_write(st)
            ok, out = compile_text(text)
            verdict_put(text, ok)
        else:
            out = "(already compiled: this exact file did not pass)"
        if ok and why is None:
            # It compiles and it is not syntactically vacuous. One question left, and it is the
            # one that decided 30 of this parent's 300 instances: does the statement say
            # anything the automation cannot supply by itself? Asked at most PROBE_MAX_DENIALS
            # times per problem, and only here -- on a file that already compiles, so the probe
            # is never spent on a run that has a compile error to fix first.
            s = state_read()
            trivial = (int(s.get("probe_denials", 0)) < PROBE_MAX_DENIALS
                       and statement_is_trivial(text) is True)
            if not trivial:
                # THE FAITHFULNESS AUDIT (section 5f). This is where the parent said `allow`, and
                # where 69 of its 300 instances were accepted with a statement the equivalence
                # grader rejects. Asked at most AUDIT_MAX_DENIALS times per problem, only on a
                # file that already compiles and already passed the triviality probe, and never
                # on a file whose statement this harness could not lift out cleanly.
                if int(s.get("audit_denials", 0)) < AUDIT_MAX_DENIALS:
                    reason = audit_reason(text, statement_only=statement_only)
                    if reason:
                        s["audit_denials"] = int(s.get("audit_denials", 0)) + 1
                        state_write(s)
                        return _hook_reply({"decision": "deny", "reason": reason}, real)
                return _hook_reply({"decision": "allow"}, real)
            s["probe_denials"] = int(s.get("probe_denials", 0)) + 1
            state_write(s)
            informal = informal_theorem()
            return _hook_reply({"decision": "deny", "reason": (
                f"{head.rstrip()}\n\n"
                f"It compiles, and that part is done. The problem is the STATEMENT: with the "
                f"same context and its own hypotheses available, `"
                + " ; ".join(PROBE_TACTICS) + "` closes it on its own, without using anything "
                f"you assumed. A statement the automation proves by itself carries no "
                f"mathematical content, so it is scored as if no theorem had been formalized --"
                f" the same as an empty file -- however cleanly it compiled.\n\n"
                f"This is what it usually means: the statement has been narrowed to a special "
                f"case, a hypothesis it needs has been dropped, the conclusion has been stated "
                f"for one object instead of all of them, or the whole thing has been restated "
                f"in the exact shape of a library lemma that the simp set already knows and "
                f"then proved by citing it.\n\n"
                + (f"Here is the theorem you were asked to formalize, again, verbatim:\n\n"
                   f"<informal_theorem>\n{informal}\n</informal_theorem>\n\n" if informal else "")
                + f"Go clause by clause: every object it quantifies over, every hypothesis it "
                f"assumes, and the whole conclusion -- and put all of them into the statement "
                f"in {ANSWER}, then prove that. Do NOT bolt on an extra hypothesis or a "
                f"decoration to defeat this check; that makes the statement weaker, not "
                f"stronger, and it is scored as a wrong statement. State the theorem that was "
                f"actually given to you.")}, real)

        parts = [head.rstrip()]
        if why:
            parts.append(f"Problem: {why}.")
        if not ok:
            # The grader compiles a uniquely-named scratch copy, so every diagnostic is
            # reported against `_grade.<hex>.lean` -- a file the agent has never heard of and
            # cannot open. Renamed to the path the errors actually belong to; the line and
            # column numbers are identical.
            parts.append("Compiler output:\n" + SCRATCH_NAME.sub(str(ANSWER), str(out))[:4000])
        # `land` only replaces `tail` when the file DOES NOT ELABORATE. If it elaborates and was
        # only refused for a `sorry`, telling it to add more `sorry` would be nonsense -- that
        # file is already at the rung `land` exists to reach, and the ordinary tail (which asks
        # for the proof and forbids weakening the statement) is the right thing to send.
        parts.append((land if (last_call and not ok) else tail).strip())
        return deny("\n\n".join(parts))
    except Exception as e:                          # noqa: BLE001 - fail OPEN
        print(f"[hook-verify] {type(e).__name__}: {e}", file=sys.stderr)
        return _hook_reply({"decision": "allow"}, real)
    finally:
        sys.stdout = real


# ===========================================================================
# 5c. THE ANSWER OF RECORD  --  snapshots, and what is left on disk at exit
#
# Only `<PROJECT>/Work.lean` is graded, and only as it stands when this process exits. Two
# measured ways that lost work which existed:
#   * a run wrote a complete file to WORK/Work.lean, one level above the graded path, and was
#     recorded as having written nothing at all;
#   * files that compiled with a `sorry` mid-run were edited into files that did not compile,
#     and the run scored as if nothing had ever elaborated -- the whole distance from
#     "elaborates" back to "does not" thrown away in the last two turns.
#
# So every distinct version of the answer seen during the run is kept in memory (a few hundred
# bytes each), and at exit the best one that COMPILES is what gets left on disk. Never a
# rewrite of the agent's Lean and never a synthesis: one of the versions the agent itself
# wrote, chosen newest-first, and only when what is currently there is worse.
#
# AND, NEW THIS ROUND, ONE LAST BAND WHEN NO VERSION COMPILES AT ALL.
#
# The parent's arm ended 26 of 300 runs with a file that does not elaborate -- 17 of them cut
# off at the turn cap, median 95 history entries, so these are not runs that gave up early but
# runs that fought the compiler until the budget ran out. Their final files were taken off this
# very record and re-run through `lean` for this round, one edit applied to each: the proof of
# the last declaration replaced by `sorry`. TWELVE OF THE TWENTY-SIX THEN ELABORATED. The
# statement was complete and type-correct the whole time; a broken tactic block around it took
# the file from `incomplete`/`incomplete_faithful` down to `no_elaborate`.
#
# That edit is what `sorry_text` does, and the band below is where it is spent -- last, only
# when nothing the agent wrote compiles, so a real proof is never traded for a stub. It cannot
# weaken a statement: the signature is copied byte for byte and only the proof is dropped, and
# the equivalence grader ignores proofs entirely.
# ===========================================================================
SNAPSHOT_LIMIT = int(os.environ.get("AGENT_SNAPSHOTS", "40"))
FINALIZE_COMPILES = int(os.environ.get("AGENT_FINALIZE_COMPILES", "3"))
# The `sorry`-degrade band gets its OWN compile budget rather than sharing FINALIZE_COMPILES.
# Sharing would let three failed full-file compiles starve the band entirely, which is the one
# case it exists for -- by construction it only runs when every full-file candidate failed.
# Raised from 2 to 4 with the two file-wide degrades: there are now three shapes to try per
# candidate rather than one, and an `import Mathlib` compile is ~6 s, so the whole band still
# costs well under half a minute inside a 3700 s fence.
SORRY_FALLBACK_COMPILES = int(os.environ.get("AGENT_SORRY_COMPILES", "4"))
# Wall-clock fence. The runner kills a problem at 7200 s and a killed problem produces NO
# result at all, which is worse than any answer -- so no compile is STARTED after this many
# seconds. The arithmetic is unchanged and still worst-case safe: the fence is re-checked
# BEFORE each compile, so at most one compile can begin after it, and 1400 + 600 (that compile
# at the grader's cap) + 600 (grade()'s own) stays inside 7200.
#
# 3700, aligned with RESERVE_HARD_SECONDS for the same reason it always was: the
# cohort this band exists for is the slowest one in the arm (no_elaborate ran to a median 639 s
# and four instances past 1200 s), so a fence set for the median would skip exactly the runs
# that need the net. Measured separately, an `import Mathlib` compile is ~6 s, not 600.
FINALIZE_DEADLINE = int(os.environ.get("AGENT_FINALIZE_DEADLINE", "3700"))


class Snapshots:
    """Every distinct version of the answer file, oldest first."""

    def __init__(self, paths: tuple[Path, ...] = ()) -> None:
        self.paths = paths or (ANSWER, WORK / ANSWER_NAME)
        self.texts: list[str] = []
        self._hashes: set[str] = set()
        self._stats: set[tuple] = set()

    def observe(self) -> None:
        """Cheap enough to call on every event: a stat per path, a read only on change."""
        for p in self.paths:
            try:
                stt = p.stat()
            except OSError:
                continue
            key = (str(p), stt.st_mtime_ns, stt.st_size)
            if key in self._stats:
                continue
            self._stats.add(key)
            self.add(_read_text(p))

    def add(self, text: str) -> None:
        if not text.strip():
            return
        h = _sha16(text)
        if h in self._hashes:
            return
        self._hashes.add(h)
        self.texts.append(text)
        if len(self.texts) > SNAPSHOT_LIMIT:
            self._hashes.discard(_sha16(self.texts.pop(0)))


def stray_answers() -> list[str]:
    """Lean the agent wrote somewhere that is not the graded path, newest first.

    Bounded and explicit: the workspace root and the project directory, one level, no
    recursion into `.lake` (6 GB of Mathlib) and never the grader's own scratch files.
    """
    found: list[tuple[float, str]] = []
    for d in (WORK, PROJECT):
        try:
            names = sorted(d.glob("*.lean"))
        except OSError:
            continue
        for p in names:
            if p == ANSWER or p.name.startswith("_grade."):
                continue
            try:
                mtime = p.stat().st_mtime
            except OSError:
                continue
            text = _read_text(p)
            if HAS_THEOREM.search(text):
                found.append((mtime, text))
    return [t for _, t in sorted(found, key=lambda x: -x[0])]


def finalize_answer(snaps: Snapshots, *, started: float) -> dict:
    """Leave the best version the agent produced at the graded path. Returns what it did.

    Order of preference, and the reason for it: a file that compiles with no `sorry` outranks
    one that compiles with a `sorry`, which outranks one that does not compile at all -- that
    is the grading ladder, and within each band the NEWEST version wins because it is the most
    developed. What is on disk is only replaced when something strictly better is found, so
    this can move a run up the ladder and never down it.

    The last band is the one addition: when NOTHING the agent wrote elaborates, the newest
    statements are re-offered with their unfinished proofs replaced by `sorry` (see
    `sorry_text` for the last declaration and `file_sorry_text` for the whole file). It is last
    precisely so that it can never displace a proof that works.

    A DISQUALIFIED version is skipped in the compiling bands, because it is not worth what it
    looks worth: a file that uses `native_decide` or declares an `axiom` compiles beautifully
    and is scored as if nothing had been proved, so an earlier clean version -- or the same
    file with its proofs dropped, which removes the construct with them -- ranks above it.
    """
    report: dict = {"restored": False, "compiles_run": 0, "sorry_compiles_run": 0,
                    "candidates": 0, "source": None, "skipped_disqualified": 0}
    current = answer_text()
    ordered: list[str] = []

    def push(text: str) -> None:
        if text.strip() and HAS_THEOREM.search(text) and text not in ordered:
            ordered.append(text)

    push(current)
    for text in reversed(snaps.texts):              # newest first
        push(text)
    for text in stray_answers():
        push(text)
    report["candidates"] = len(ordered)
    if not ordered:
        return report

    no_sorry = [t for t in ordered if "sorry" not in t]
    with_sorry = [t for t in ordered if "sorry" in t]
    for band, label in ((no_sorry, "compiles"), (with_sorry, "compiles_with_sorry")):
        for text in band:
            if disqualifier(text):
                # Compiles, and is scored as if it did not. Skipped here so a clean earlier
                # version, or the degraded band below (which drops the proofs, and the
                # construct with them), is what reaches the graded path.
                report["skipped_disqualified"] += 1
                continue
            ok = verdict_get(text)
            if ok is None:
                if (report["compiles_run"] >= FINALIZE_COMPILES
                        or time.time() - started > FINALIZE_DEADLINE):
                    continue
                report["compiles_run"] += 1
                ok, _ = compile_text(text)
                verdict_put(text, ok)
            if not ok:
                continue
            if text != current:
                sync_solution(text)
                report.update(restored=True, source=label)
            else:
                report["source"] = f"current:{label}"
            return report

    # NOTHING THE AGENT WROTE ELABORATES. Before settling for that, ask the cheaper question:
    # does the STATEMENT elaborate? Newest first, because the newest statement is the most
    # developed one, and bounded by its own small compile budget and by the same wall-clock
    # fence as every other compile here.
    #
    # `degraded == text` is skipped rather than compiled: that file was already tried, and
    # failed, in the `with_sorry` band above.
    #
    # THREE DEGRADES PER CANDIDATE, gentlest first, because the parent offered only the first
    # of them and the band it exists for is the one where it least applies. The last-declaration
    # edit fixes a single theorem whose proof ran out of road; the file-wide edits are for the
    # 4.8-theorem, 2.6-definition sprawls that make up 72% of the non-elaborating band, where
    # the broken step is somewhere in the middle. Sparing the definitions is tried before
    # stubbing them, since a definition replaced by `sorry` can make the theorem above it
    # unprovable for a reason that was never the agent's.
    for text in ordered:
        for build in (sorry_text,
                      lambda t: file_sorry_text(t, definitions=False),
                      file_sorry_text):
            if (report["sorry_compiles_run"] >= SORRY_FALLBACK_COMPILES
                    or time.time() - started > FINALIZE_DEADLINE):
                break
            try:
                degraded = build(text)
            except Exception:               # noqa: BLE001 - a bad parse must not lose the run
                degraded = None
            if not degraded or degraded == text or not HAS_THEOREM.search(degraded):
                continue
            ok = verdict_get(degraded)
            if ok is None:
                report["sorry_compiles_run"] += 1
                ok, _ = compile_text(degraded)
                verdict_put(degraded, ok)
            if ok:
                sync_solution(degraded)
                report.update(restored=True, source="statement_with_sorry")
                return report

    # Not even the statement. A theorem on disk still outranks an empty or declaration-less
    # file, which is the difference between the bottom rung and the one above it.
    if not HAS_THEOREM.search(current) and ordered:
        sync_solution(ordered[0])
        report.update(restored=True, source="declaration_only")
    return report


def _is_hook_notice(e: dict) -> bool:
    """Hook runs emit four UI notices each (projector._project_hook). They are not turns and
    not tool calls, so they are dropped from the record -- otherwise entry counts and tool
    mixes stop being comparable with a node that ran no hooks."""
    if e.get("type") != "notice":
        return False
    det = (e.get("raw") or {}).get("detail")
    return isinstance(det, dict) and str(det.get("kind") or "").startswith("hook_")


async def run_problem(api_base: str, problem_text: str, *,
                      max_turns: int | None = None, mcp: bool = True,
                      prompt: str | None = None, **cfg_kwargs) -> dict:
    """One problem, start to finish. Returns the record for this run."""
    import asyncio
    from contextlib import aclosing

    from vibe.app_server.events import (CallbackRequested, HistoryEntryAdded,
                                        HistoryEntryUpdated)
    from vibe.app_server.local import LocalHarness, LocalHarnessOptions
    from vibe.app_server._runtime import ResumeSessionIntent
    from vibe.core.config.harness_files import init_harness_files_manager

    # LocalHarness is not self-contained: vibe's own entry points initialise this global
    # first (app_server/stdio.py:49 does exactly this call), and without it session.open()
    # fails with "HarnessFilesManager not initialized". "user"/"project" are the two file
    # sources their CLI uses -- AGENTS.md and .vibe/ config discovery.
    init_harness_files_manager("user", "project")

    # A resumed session (AGENT_RESUME_SESSION, set by `aiprover resume`) continues the saved
    # vibe session of this workspace after its run was cut off, typically by a lost model
    # server: its conversation, Work.lean, tool-call log and clock carry on where they stopped.
    resume_id = os.environ.get("AGENT_RESUME_SESSION", "").strip()
    make_project()
    if not resume_id:
        PROBLEM.write_text(problem_text, encoding="utf-8")
    # After make_project(): pinned_toolchain() reads the project's lean-toolchain.
    agent_env = export_agent_env()
    # Before importing anything that reads config: VIBE_HOME is resolved at import time in
    # places, and their agent profile would otherwise point at api.mistral.ai.
    os.environ["VIBE_HOME"] = str(write_vibe_home(api_base))
    os.environ.setdefault("VIBE_LOCAL_API_KEY", "EMPTY")

    cfg = agent_config(api_base, prompt=prompt, mcp=mcp, max_turns=max_turns, **cfg_kwargs)
    # On resume the clock counts the time already spent, not the time the server was down.
    t0 = time.time() - (float(os.environ.get("AGENT_RESUME_ELAPSED") or 0) if resume_id else 0)
    # The reserve hook runs as its own process and cannot see this one's clock or config, so
    # both go into the shared state file BEFORE the session opens. Written, not merged into a
    # default, because a hook that guesses the budget would report the wrong number to the model.
    st0 = state_read()
    st0.update(t0=t0, max_turns=int(cfg.max_turns or MODEL["max_turns"]))
    state_write(st0)
    # And the tool-call log starts empty. The workspace is per problem, so this is belt and
    # braces -- but a stale byte log would put a fresh run straight into its landing phase,
    # which is the one failure of this mechanism that would be invisible in the record.
    if not resume_id:
        try:
            TICKS.unlink(missing_ok=True)
        except OSError:
            pass
    # Keyed by entry id, insertion-ordered. An entry is ADDED in its "running" state and
    # then UPDATED in place as the tool executes and the model streams; the first version of
    # this recorded only HistoryEntryAdded, so every effect in every run was serialised
    # mid-flight: 9218 effects with `input: null`, `outputText: ""`, status "running", and
    # assistant text truncated to its first streamed chunk ("Let me"). That made the run
    # record undebuggable -- the 60-turn cap below was found by grepping message text, not
    # from any field -- so updates are applied and the settled entry is what gets stored.
    entries: dict[str, dict] = {}
    err = None
    history: list = []
    # Every version of the answer the agent commits to disk, so the last two turns cannot
    # throw away a version that compiled. Fed from the event stream: the file only changes
    # through a tool call, and a tool call always produces events.
    snaps = Snapshots()

    options = (LocalHarnessOptions(session_options=cfg, session=ResumeSessionIntent(resume_id))
               if resume_id else LocalHarnessOptions(session_options=cfg))
    session = await LocalHarness(options).start()
    checks = 0
    verifier_stopped = None
    try:
        await session.resources.runtime.wait_until_ready()
        message = TASK
        if resume_id:
            message = RESUME_TASK if (PROJECT / "Work.lean").is_file() else RESUME_TASK_LOST
        while True:
            async with aclosing(session.act(message)) as stream:
                async for event in stream:
                    snaps.observe()
                    if isinstance(event, (HistoryEntryAdded, HistoryEntryUpdated)):
                        e = _summarise(event.entry)
                        if _is_hook_notice(e):
                            continue
                        # id is the identity across add/update; fall back to a positional key
                        # so an id-less entry is still kept rather than collapsing onto None.
                        entries[e.get("id") or f"_{len(entries)}"] = e
                    elif isinstance(event, CallbackRequested):
                        # Headless: nobody to ask. Denying is what `vibe --prompt` does
                        # (cli/programmatic.py), so matching it keeps behaviour identical to
                        # the reference.
                        await session.deny_callback(event.callback)

            if checks >= MAX_DELIVERY_CHECKS:
                break
            verdict = _delivery_check()
            if verdict is None:
                break                            # it is an answer; accept it
            checks += 1
            print(f"[harness] delivery check {checks}: {verdict[:120]}", flush=True)
            # act() raises "A turn is already running" while turn_active. The stream is fully
            # consumed above so it should be false, but a race here would disable the verifier
            # for every run while looking like an ordinary agent error -- so it is waited for
            # and, if it persists, recorded as its own reason.
            for _ in range(30):
                if not session.turn_active:
                    break
                await asyncio.sleep(1)
            if session.turn_active:
                verifier_stopped = "turn still active after 30s; verifier gave up"
                print(f"[harness] {verifier_stopped}", flush=True)
                break
            message = verdict
    except Exception as e:                      # noqa: BLE001 - a crash still leaves its file
        err = f"{type(e).__name__}: {e}"
    finally:
        try:
            history = list(session.history)
        except Exception:                       # noqa: BLE001
            history = []
        await session.close()

    # session.history is the settled record; the streamed `entries` are a fallback for the
    # case where close() or the property raises and history comes back empty.
    def _safe(h) -> dict:
        # One unexpected entry shape must not cost the whole record: the verdict and the
        # solution matter more than any single history entry.
        try:
            return _summarise(h)
        except Exception as e:                  # noqa: BLE001
            return {"type": "unsummarisable", "error": f"{type(e).__name__}: {e}"}

    events = [_safe(h) for h in history] if history else list(entries.values())
    events = [e for e in events if not _is_hook_notice(e)]

    # LAST, and after the session is closed: whatever is at the graded path when this function
    # returns is the answer, and nothing else will touch it.
    snaps.observe()
    try:
        finalized = finalize_answer(snaps, started=t0)
    except Exception as e:                      # noqa: BLE001 - never lose a run to the net
        finalized = {"error": f"{type(e).__name__}: {e}"}

    res = grade(events=events, history_len=len(events), agent_error=err,
                elapsed=round(time.time() - t0, 1))
    res["delivery_checks"] = checks
    res["verifier_stopped"] = verifier_stopped
    res["finalized"] = finalized
    res["hook_state"] = state_read()
    res["tool_calls_seen"] = tick_count()        # what the budget policy was reading
    res["snapshots"] = len(snaps.texts)
    return res


RESUME_TASK = ("The session was interrupted (the model server restarted) and is now resumed. "
               "Your conversation so far is above and Work.lean holds what you last wrote. "
               "Continue the task from where you stopped.")
RESUME_TASK_LOST = ("The session was interrupted (the model server restarted) and is now "
                    "resumed. Your conversation so far is above, but Work.lean was lost: write "
                    "your latest version to Work.lean again, then continue the task from where "
                    "you stopped.")


def _delivery_check() -> str | None:
    """None if the answer is acceptable, else the message to send back.

    Deliberately uses the same grader that decides the score, so the agent cannot be failed
    by a check it was never shown. Only compile errors and vacuity are reported -- not
    faithfulness, which is a semantic question this cannot answer and must not pretend to.
    """
    answer = PROJECT / "Work.lean"
    text = answer.read_text(errors="replace") if answer.is_file() else ""
    if not text.strip():
        return ("Work.lean is empty or missing. Write the Lean 4 theorem and its proof to "
                "Work.lean now.")
    why = vacuity(text)
    ok, out = compile_text(text)
    if ok and why is None:
        return None
    parts = ["Your answer is not accepted yet. I compiled Work.lean with this project's "
             f"pinned toolchain ({pinned_toolchain()}) and it did not pass."]
    if why:
        parts.append(f"Problem: {why}.")
    if not ok:
        parts.append("Compiler output:\n" + out[:6000])
    parts.append("Fix it in Work.lean. Read the errors carefully -- Lean often names the "
                 "correct identifier in its hint. Use lean_diagnostic_messages and lean_goal "
                 "to check your work before finishing.")
    return "\n\n".join(parts)


def _summarise(entry) -> dict:
    """One history entry, reduced to what a harness fix is argued from.

    vibe's history is a UNION of entry types, discriminated by `type`, not a flat message
    list -- and the first version of this function guessed at `tool_name`/`reasoning` keys
    that do not exist on any of them. The result looked plausible and reported zero tool
    calls and zero reasoning for a run that had 39 entries. The types (app_server/models.py):

        message    role, content: list[ContentBlock]
        reasoning  text, summary          <- the model's thinking is its OWN entry
        effect     title, detail, state   <- a tool call and its outcome
        callback   callback_id, title, detail, state
        notice, checkpoint

    So counting tool calls means counting `effect` entries, and reasoning is never a field on
    a message.
    """
    d = entry.model_dump(mode="json") if hasattr(entry, "model_dump") else dict(entry)
    kind = d.get("type")
    out: dict = {"type": kind, "id": d.get("id"), "status": d.get("generation_status")}

    if kind == "message":
        out["role"] = d.get("role")
        blocks = d.get("content") or []
        # ContentBlock is itself a union; keep text and note anything else by its type.
        texts = [b.get("text") for b in blocks if isinstance(b, dict) and b.get("text")]
        out["text"] = ("\n".join(texts))[:20000]
        kinds = {b.get("type") for b in blocks if isinstance(b, dict)} - {"text"}
        if kinds:
            out["block_types"] = sorted(k for k in kinds if k)
    elif kind == "reasoning":
        out["text"] = (d.get("text") or "")[:20000]
        if d.get("summary"):
            out["summary"] = d["summary"]
    elif kind in ("effect", "callback"):
        out["title"] = d.get("title")
        out["state"] = d.get("state")
        det = d.get("detail")
        # detail carries the tool name and arguments; kept whole but bounded, because which
        # tool was called with what is the single most useful field for harness design.
        if isinstance(det, dict):
            out["detail"] = {k: (v[:8000] if isinstance(v, str) else v)
                             for k, v in det.items()}
        elif det is not None:
            out["detail"] = str(det)[:8000]
    else:
        out["raw"] = {k: v for k, v in d.items()
                      if k not in ("id", "session_id", "turn_id", "created_at",
                                   "updated_at", "generation_status")}
    return out


def _count_tools(events: list[dict]) -> dict[str, int]:
    """Tool calls, counted from `effect` entries.

    An effect's identity lives in `detail` (its shape varies by effect kind), so the name is
    taken from whichever of a few known keys is present, falling back to `title`. Counting
    something is better than reporting zero -- reporting zero tool calls for a run that made
    them is how a whole day went in the wrong direction once already.
    """
    out: dict[str, int] = {}
    for e in events:
        if e.get("type") not in ("effect", "callback"):
            continue
        det = e.get("detail") if isinstance(e.get("detail"), dict) else {}
        # `toolName` -- camelCase, verified against a real run. An earlier version guessed
        # `tool_name`/`tool`/`name` and collapsed six distinct MCP calls into one bucket
        # labelled "tool", which is indistinguishable from not knowing what ran.
        name = det.get("toolName") or e.get("title") or det.get("kind") or "unknown"
        out[str(name)] = out.get(str(name), 0) + 1
    return out


# ===========================================================================
# 7. GRADE  ->  DELEGATED TO THE RUNNER-OWNED GRADER
#
# `grade()` produces the round record: the type_correctness (type correctness, from the pinned
# toolchain) plus a pending semantic_equivalence that the post-round grade_semantic_equivalence.py pass fills in. It is
# deliberately NOT implemented here -- see the note beside _load_grader().
# ===========================================================================
def _stop_reason(events: list[dict]) -> str | None:
    return _grader()._stop_reason(events)


def grade(*, events: list, history_len: int, agent_error: str | None,
          elapsed: float) -> dict:
    """Recompile the produced file and return this instance's record. See grader.grade()."""
    return _grader().grade(
        events=events, history_len=history_len, agent_error=agent_error, elapsed=elapsed,
        project=PROJECT,
        model={k: MODEL[k] for k in ("model_id", "temperature", "reasoning_effort")},
    )


# ===========================================================================
# 8. CONTAINER
#
# One container per problem. Runs OUTSIDE the container (the `run` subcommand); the `agent`
# subcommand is what executes inside it.
#
# `--containall` denies the container everything not bind-mounted: no host home, no shared
# /tmp, no host environment, no other problem's workspace. That isolation is why thousands of
# agents can run concurrently without touching each other or the repo -- the previous harness
# wrote candidate snippets into the shared Lean project and accumulated 10,356 stale files
# there.
#
# Note on cost: lean-lsp-mcp keeps a `lake serve` alive per container, which loads Mathlib
# once (~2-4 GB resident) instead of paying that load on every compile. Per agent that is
# cheaper -- runs made 4-5 compiles at 51-192s each. The constraint is concurrent memory, so
# WORKERS may need to be lower than for the old harness. Mathlib itself is NOT duplicated:
# it is a read-only mount shared through the page cache.
# ===========================================================================
SIF = os.environ.get("AGENT_SIF", "/scratch/11428/pjana/py312.sif")
HOST_MATHLIB = os.environ.get(
    "AGENT_MATHLIB_HOST",
    "/work2/11428/pjana/stampede3/autoformalization-jtemb/tmpFolder/"
    "8d9a729d-dec6-452d-bb90-d63be139ee52/TmpProjDir")
HOST_ELAN = os.environ.get("AGENT_ELAN_HOST", str(Path.home() / ".elan"))
HOST_VIBE = os.environ.get("AGENT_VIBE_HOST",
                           "/work2/11428/pjana/stampede3/vibe_env")
HOST_MCP = os.environ.get("AGENT_MCP_HOST", "/work2/11428/pjana/stampede3/mcp_env")


def container_cmd(workspace: Path, api_base: str, extra: list[str] | None = None) -> list[str]:
    """The apptainer invocation for one problem. The single place mounts are defined."""
    here = Path(__file__).resolve().parent
    return [
        "apptainer", "exec", "--containall",
        "--bind", f"{HOST_MATHLIB}:/mathlib:ro",
        "--bind", f"{HOST_ELAN}:/elan:ro",
        "--bind", f"{HOST_VIBE}:/vibe:ro",       # mistral-vibe, the scaffold
        "--bind", f"{HOST_MCP}:/mcp:ro",         # lean-lsp-mcp, the tools
        "--bind", f"{here}:/scripts:ro",
        # The grader, read-only. Without this bind _load_grader() finds neither
        # /grading/grade_type_correctness.py nor the in-repo fallback (inside the container
        # `parents[1]` resolves to `/`), so every forwarder in this file raises and the
        # standalone path this function exists to provide cannot grade at all.
        "--bind", f"{here.parent / 'harness_runner'}:/grading:ro",
        "--bind", f"{workspace}:/work:rw",       # the ONLY writable mount
        "--env", "PYTHONPATH=/vibe/lib/python3.12/site-packages",
        "--env", "AGENT_GRADER=/grading/grade_type_correctness.py",
        "--env", "LEAN_MCP_SITE=/mcp/lib/python3.12/site-packages",
        "--env", "VIBE_LOCAL_API_KEY=EMPTY",
        "--env", f"AGENT_API_BASE={api_base}",
        "--pwd", "/work",
        SIF, "python3", "/scripts/lean_harness.py", "agent",
        "--api-base", api_base, *(extra or []),
    ]


# ===========================================================================
# 9. CLI
#
#   agent      run one problem INSIDE a container (what container_cmd invokes)
#   run        run a dataset, one container per problem (outside)
#   selftest   prove the environment before spending an API budget
#   config     print the resolved setup and where each value came from
# ===========================================================================
def selftest(api_base: str = "unused") -> int:
    """Prove the contract with no model call. Run this after ANY edit to this file."""
    checks: dict[str, bool] = {}
    print(f"work dir     : {sorted(p.name for p in WORK.iterdir())}")
    checks["problem readable"] = PROBLEM.is_file() and bool(PROBLEM.read_text().strip())

    make_project()
    checks["project created"] = (PROJECT / "lean-toolchain").is_file()

    # The prompt now TELLS the agent that `lean Work.lean` works from /work/proj with no
    # setup. That claim is asserted here rather than trusted: a false environment claim in
    # the prompt is worse than no claim, because the agent stops looking for the real answer.
    try:
        env = export_agent_env()
        which = shutil.which("lean")
        checks["lean on PATH is the pinned toolchain"] = which == lean_bin()
        print(f"agent PATH   : lean -> {which}")
        smoke = PROJECT / "Work.lean"
        smoke.write_text("import Mathlib\ntheorem env_ok (n : Nat) : n + 0 = n := by simp\n")
        # No env= and no explicit LEAN_PATH: exactly the invocation the prompt describes.
        r = subprocess.run(["lean", "Work.lean"], cwd=str(PROJECT), capture_output=True,
                           text=True, timeout=COMPILE_TIMEOUT)
        checks["agent can run `lean Work.lean` unaided"] = r.returncode == 0
        if r.returncode != 0:
            print(f"  lean said  : {((r.stdout or '') + (r.stderr or ''))[:300]}")
        smoke.unlink(missing_ok=True)
        checks["LEAN_PATH resolves Mathlib"] = "mathlib" in env["LEAN_PATH"].lower()
    except (RuntimeError, OSError, subprocess.SubprocessError) as e:
        print(f"agent env    : FAILED {type(e).__name__}: {e}")
        checks["lean on PATH is the pinned toolchain"] = False
    try:
        checks["toolchain pinned"] = "v4" in pinned_toolchain()
        print(f"pinned       : {pinned_toolchain()}  ->  {lean_bin()}")
    except RuntimeError as e:
        checks["toolchain pinned"] = False
        print(f"  {e}")

    # `_grader().CANARY`, NOT a bare `CANARY`. The constant lives in the grader module now, and
    # this file reaches grader attributes through the module-level __getattr__ below -- which
    # Python consults only for ATTRIBUTE access on the module object, never for a global lookup
    # inside a function in it. So `compile_text(CANARY)` raised NameError and took the whole
    # preflight down with it, which is the one check that must work before any SU is spent.
    ok, out = compile_text(_grader().CANARY)
    checks["lean canary"] = ok
    if not ok:
        print(out[:400])

    checks["vacuity rejects True"] = vacuity(
        "import Mathlib\ntheorem t : True := trivial\n") is not None
    checks["vacuity rejects sorry"] = vacuity(
        "import Mathlib\ntheorem t (n : Nat) : n + 0 = n := by sorry\n") is not None
    checks["vacuity accepts real"] = vacuity(
        "import Mathlib\ntheorem t (n : Nat) : n + 0 = n := by simp\n") is None

    # The probe's RECONSTRUCTION, asserted without `lean`: it must keep the binders and the
    # goal, rename the declaration, and drop the agent's own proof. A probe that silently
    # loses a hypothesis would answer "trivial" about a statement nobody wrote.
    demo = ("import Mathlib\n\nnamespace Demo\n\n/-- doc (n : Nat := 3) -/\n"
            "theorem demo (n : Nat) (h : 0 < n) : n + 0 = n := by\n  simp\n\nend Demo\n")
    p = probe_text(demo)
    checks["probe keeps the statement"] = bool(
        p and PROBE_NAME in p and "(h : 0 < n)" in p and "n + 0 = n" in p
        and "\n  simp\n" not in p and p.rstrip().endswith("end Demo")
        and "tauto" in p)
    checks["probe declines a stubbed file"] = probe_text(
        "import Mathlib\ntheorem t : True := by sorry\n") is None

    # The DEGRADE, asserted the same way and for the same reason: it must keep the context, the
    # binders and the goal, keep the declaration's own NAME (unlike the probe, this file is the
    # answer), drop the agent's proof, and close the namespace. A degrade that lost a binder
    # would leave a statement nobody wrote sitting at the graded path.
    s = sorry_text(demo)
    checks["degrade keeps the statement"] = bool(
        s and "theorem demo (n : Nat) (h : 0 < n) : n + 0 = n" in s
        and "sorry" in s and "\n  simp\n" not in s
        and "namespace Demo" in s and s.rstrip().endswith("end Demo"))
    checks["degrade declines a file with no declaration"] = sorry_text(
        "import Mathlib\n#check Nat\n") is None

    # THE FILE-WIDE DEGRADE. Same property as the one above and asserted the same way -- every
    # signature kept byte for byte, every proof dropped -- on the shape it exists for: several
    # declarations, with the break somewhere other than the last one.
    sprawl = ("import Mathlib\n\ndef myThing (n : Nat) : Nat := n + 1\n\n"
              "theorem first (n : Nat) : myThing n = n + 1 := by\n  rfl\n\n"
              "theorem second (n : Nat) (h : 0 < n) : 0 < myThing n := by\n  simp [myThing]\n")
    fs = file_sorry_text(sprawl, definitions=False)
    checks["file-wide degrade keeps every statement"] = bool(
        fs and "theorem first (n : Nat) : myThing n = n + 1 := sorry" in fs
        and "theorem second (n : Nat) (h : 0 < n) : 0 < myThing n := sorry" in fs
        and "def myThing (n : Nat) : Nat := n + 1" in fs and "rfl" not in fs)
    checks["file-wide degrade can stub definitions too"] = bool(
        (file_sorry_text(sprawl) or "").count(":= sorry") == 3)
    checks["file-wide degrade declines a file with no declaration"] = file_sorry_text(
        "import Mathlib\n#check Nat\n") is None
    # And end to end: a break in the MIDDLE declaration, which `sorry_text` cannot reach
    # because it only edits the last one.
    mid = ("import Mathlib\ntheorem a (n : Nat) : n = n := rfl\n"
           "theorem b (n : Nat) : 0 ≤ n := by\n  have step : n = n := by\n"
           "theorem c (n : Nat) : n + 0 = n := by simp\n")
    checks["file-wide degrade rescues a break in the middle"] = (
        not compile_text(mid)[0] and compile_text(file_sorry_text(mid) or "")[0])

    # THE SOUNDNESS GUARD (section 5h). What is asserted is that it mirrors the scan that
    # decides the score: every construct that scan rejects is rejected here, and ordinary Lean
    # is not. A guard that refused a legitimate write would cost the answer it was protecting.
    checks["soundness guard catches native_decide"] = bool(disqualifier(
        "import Mathlib\ntheorem t : 2 + 2 = 4 := by native_decide\n"))
    checks["soundness guard catches an axiom"] = bool(disqualifier(
        "import Mathlib\naxiom magic : False\n"))
    checks["soundness guard catches an unsound option"] = bool(disqualifier(
        "import Mathlib\nset_option maxHeartbeats 0 in\ntheorem t : True := trivial\n"))
    checks["soundness guard catches a foreign import"] = bool(disqualifier(
        "import MyOwnModule\ntheorem t : True := trivial\n"))
    checks["soundness guard passes ordinary Lean"] = disqualifier(
        "import Mathlib.Data.Nat.Basic\nset_option maxHeartbeats 400000 in\n"
        "theorem t (n : Nat) : n + 0 = n := by simp\n") is None
    checks["soundness guard reads only the NEW text of an edit"] = (
        disqualifier(_hook_new_text({"tool_input": {
            "old_string": "by native_decide", "new_string": "by decide"}})) is None)
    checks["soundness guard reads a write's content"] = bool(disqualifier(_hook_new_text(
        {"tool_input": {"file_path": str(ANSWER), "content": "by native_decide"}})))

    # THE BUDGET POLICY (section 5e). Two properties, both of which the parent got wrong in a
    # way that made the mechanism unreachable: the hook must match every tool so that it counts
    # every call, and it must refuse only the withdrawable ones.
    checks["budget hook matches every tool"] = reserve_match() == "re:.*"
    checks["landing never withdraws the writing tools"] = not (
        {"write_file", "edit", "read_file", "m_lean_diagnostic_messages", "m_lean_goal",
         "m_lean_run_code", "m_lean_multi_attempt"} & set(LAND_WITHDRAW))
    checks["landing withdraws search and the shell"] = {"bash", "grep", "m_lean_loogle",
                                                        "m_lean_local_search"} <= set(
                                                            LAND_WITHDRAW)
    checks["landing message is mode-aware"] = (
        "no informal proof" in landing_reason(80, 100, statement_only=True)
        and "no informal proof" not in landing_reason(80, 100, statement_only=False))
    before = tick_count()
    checks["turn counter counts"] = tick() == before + 1 and tick_count() == before + 1
    # And end to end: an unfinished tactic block is exactly the shape the parent's arm died on
    # 26 times, and the degraded file must elaborate where the original cannot.
    broken = ("import Mathlib\ntheorem t (n : Nat) (h : 0 < n) : 0 < n + 1 := by\n"
              "  have step : n + 1 = 1 + n := by\n")
    checks["degrade rescues an unfinished proof"] = (
        not compile_text(broken)[0] and compile_text(sorry_text(broken) or "")[0])
    # And end to end, through the compiler: `n = n` is exactly the shape the grader's guard
    # exists to catch, and it must come back True rather than None.
    checks["probe catches a content-free statement"] = statement_is_trivial(
        "import Mathlib\ntheorem t (n : Nat) : n = n := rfl\n") is True

    # THE AUDIT (section 5f). No compiler involved: what is asserted is that it quotes the
    # agent's OWN signature back and nothing else, that it declines when either half is
    # missing, and that in statement-only mode it does not ask for the `sorry` to go. A review
    # that quoted a statement the agent did not write would send it chasing our bug.
    informal_demo = "Let n be a positive natural number. Then n + 0 = n."
    a = audit_reason(demo, informal=informal_demo)
    checks["audit quotes the agent's own statement"] = bool(
        a and "theorem demo (n : Nat) (h : 0 < n) : n + 0 = n" in a
        and informal_demo in a and "CHANGE NOTHING" in a)
    checks["audit declines a file with no declaration"] = audit_reason(
        "import Mathlib\n#check Nat\n", informal=informal_demo) is None
    checks["audit declines with no informal theorem"] = audit_reason(
        demo, informal="") is None
    checks["audit is mode-aware"] = bool(
        (audit_reason(demo, statement_only=True, informal=informal_demo) or "").count("`sorry`")
        > (a or "").count("`sorry`"))
    # The mismatch this round added in both places it can be caught: the task message the model
    # reads before any Lean exists, and the review that holds the finished statement against the
    # English. Both are asserted, because a rule stated in only one of them is half a change.
    checks["audit names the gloss mismatch"] = bool(a and "parenthetical gloss" in a)
    checks["task names the gloss mismatch"] = (
        "GLOSS instead of the NOTION" in TASK and "THREE MISTAKES" in TASK)

    # WRITE-THROUGH (section 5g). Every assertion here is about WHAT MAY BE DESTROYED, because
    # that is the only way this mechanism can do harm: it has no `deny` branch at all. The
    # whitelist must accept a `.lean` file under WORK and refuse everything else.
    probe_dir = PROJECT
    keep = probe_dir / "_hevo_selftest_write.lean"
    keep.write_text("import Mathlib\n")
    checks["write-through clears a .lean answer file"] = clearable(keep)
    checks["write-through spares problem.txt"] = not clearable(probe_dir / "problem.txt")
    checks["write-through spares a missing file"] = not clearable(
        probe_dir / "_hevo_absent.lean")
    checks["write-through spares mathlib"] = not clearable(
        MATHLIB / ".lake/packages/mathlib/Mathlib/Init.lean")
    checks["write-through spares outside the workspace"] = not clearable(Path("/etc/hosts"))
    checks["write-through spares the grader scratch"] = not clearable(
        probe_dir / "_grade.deadbeef.lean")
    # The path and content readers: a relative path must anchor to the invocation's cwd, and a
    # call whose own write would fail (no content, or over vibe's byte cap) must not clear.
    checks["write-through resolves a relative path"] = _hook_tool_path(
        {"cwd": str(probe_dir), "tool_input": {"file_path": ANSWER_NAME}}) == Path(
            os.path.abspath(str(ANSWER)))
    checks["write-through accepts the camelCase key"] = _hook_tool_path(
        {"cwd": str(probe_dir), "tool_input": {"filePath": str(ANSWER)}}) == Path(
            os.path.abspath(str(ANSWER)))
    checks["write-through refuses an empty content"] = not _hook_write_content_ok(
        {"tool_input": {"file_path": str(ANSWER), "content": "   "}})
    checks["write-through refuses an oversized content"] = not _hook_write_content_ok(
        {"tool_input": {"file_path": str(ANSWER), "content": "x" * (WRITE_MAX_BYTES + 1)}})
    checks["write-through accepts a real write"] = _hook_write_content_ok(
        {"tool_input": {"file_path": str(ANSWER), "content": "import Mathlib\n"}})
    # And the sidecar must be invisible to the stray-answer sweep, or a previous version could
    # come back as the answer of record. Asserted against the real glob, not reasoned about.
    sidecar = keep.with_name(f".{keep.name}.hevo-prev")
    sidecar.write_text("import Mathlib\ntheorem hevo_stale_sidecar : True := trivial\n")
    checks["write-through sidecar is not a stray answer"] = (
        sidecar not in set(probe_dir.glob("*.lean"))
        and "hevo_stale_sidecar" not in "".join(stray_answers()))
    sidecar.unlink(missing_ok=True)
    keep.unlink(missing_ok=True)
    checks["mathlib read-only"] = not os.access(str(MATHLIB), os.W_OK)

    try:
        cfg = agent_config(api_base)
        # agent MUST be None, not "lean": naming their profile pulls in its provider block,
        # which points at api.mistral.ai and fails auth against our vLLM. This check asserted
        # == "lean" for a while after that was fixed, so it failed on correct config.
        checks["agent config builds"] = cfg.agent is None and cfg.headless
        # AGENTS.md is the ONLY channel that reaches the model: AgentConfig.instructions has
        # no consumer in vibe. Every run before this was discovered ran with no prompt at
        # all, so the delivery path is asserted here and not assumed.
        vh = Path(write_vibe_home(api_base))
        agents_md = vh / "AGENTS.md"
        checks["prompt is delivered via AGENTS.md"] = (
            agents_md.is_file() and len(agents_md.read_text()) > 1000)
        # The hooks arrive the same way -- through a FILE -- and the parse is vibe's own, so a
        # malformed toml would silently mean no hooks rather than an error.
        if HOOKS_ENABLED:
            import tomllib
            hk = vh / "hooks.toml"
            parsed = tomllib.loads(hk.read_text()) if hk.is_file() else {}
            names = {h.get("name") for h in parsed.get("hooks", [])}
            checks["hooks.toml written and parses"] = names == {"write_through", "answer_gate",
                                                                "budget_reserve", "answer_sound",
                                                                "answer_verify"}
            # ORDER, not just membership. vibe runs matching hooks in file order and stops at
            # the first deny, so `answer_sound` must be listed before `write_through`: the
            # other way round, a refused write arrives after the previous version has already
            # been moved aside and the graded path is left empty for that turn.
            order = [h.get("name") for h in parsed.get("hooks", [])]
            checks["soundness guard runs before write-through"] = (
                order.index("answer_sound") < order.index("write_through"))
            checks["hook command names this file"] = all(
                str(Path(__file__).resolve()) in h.get("command", "")
                for h in parsed.get("hooks", []))
            # The prompt must never name a path that is not there: that is the failure this
            # round is fixing, so it is asserted rather than reviewed. Note this cannot be
            # written as "does not mention /work/proj" -- under the container that IS the
            # right answer; the property is that every stated path resolves HERE.
            checks["prompt states the real answer path"] = (
                str(ANSWER) in TASK and ANSWER.parent.is_dir())
            checks["prompt states no absent mathlib"] = (
                mathlib_source() is None or Path(mathlib_source()).is_dir())
            checks["prompt names cslib iff it is built"] = (
                ("import Cslib.A.B" in TASK) == bool(cslib_source()))
        checks["no duplicate tools"] = not cfg.tools and not cfg.disabled_tools
        checks["all mcp tools"] = "--disable-tools" not in cfg.mcp_servers[0].args
        print(f"agent        : {cfg.agent}, {len(cfg.instructions)} char prompt, "
              f"mcp={[s.name for s in cfg.mcp_servers]}")
    except Exception as e:                       # noqa: BLE001
        checks["agent config builds"] = False
        print(f"  agent_config failed: {type(e).__name__}: {e}")

    for k, v in checks.items():
        print(f"  {'PASS' if v else 'FAIL'}  {k}")
    bad = [k for k, v in checks.items() if not v]
    print(f"SELFTEST: {len(checks) - len(bad)}/{len(checks)}"
          + (f"  FAILED: {bad}" if bad else ""))
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["agent", "run", "selftest", "config",
                                     # Invoked by vibe, not by us: these are the two hook
                                     # commands named in $VIBE_HOME/hooks.toml. They read the
                                     # invocation from stdin and answer with one JSON object.
                                     "hook-gate", "hook-reserve", "hook-write",
                                     "hook-sound", "hook-verify"])
    ap.add_argument("--api-base", default=os.environ.get("AGENT_API_BASE", ""))
    ap.add_argument("--result", type=Path, default=WORK / "result.json")
    ap.add_argument("--no-mcp", action="store_true", help="ablate the LSP tools entirely")
    ap.add_argument("--max-turns", type=int)
    a = ap.parse_args()

    # First, because a hook must not print anything else on stdout and must not be slowed by
    # work it does not need.
    if a.mode == "hook-gate":
        return hook_gate()
    if a.mode == "hook-reserve":
        return hook_reserve()
    if a.mode == "hook-write":
        return hook_write()
    if a.mode == "hook-sound":
        return hook_sound()
    if a.mode == "hook-verify":
        return hook_verify()

    if a.mode == "config":
        ok, msg = check_upstream()
        print(f"upstream : {msg}")
        print(f"prompt   : {len(build_prompt())} chars")
        # Resolved, not assumed. Every one of these was a hardcoded container path in the
        # parent, and under local execution none of those paths exist.
        print(f"answer   : {ANSWER}")
        print(f"mathlib  : {mathlib_source()}")
        print(f"cslib    : {cslib_source()}")
        print(f"hooks    : {'on' if HOOKS_ENABLED else 'off'} "
              f"(gate after {GATE_FREE_SEARCHES} searches, "
              f"{VERIFY_MAX_DENIALS} delivery denials, "
              f"{VERIFY_MAX_COMPILES} delivery compiles, "
              f"{PROBE_MAX_DENIALS} triviality denials)")
        print(f"reserve  : notices at {RESERVE_FRACTIONS} of the turn budget (counted in tool "
              f"calls), landing at {LAND_FRACTION} withdrawing {len(LAND_WITHDRAW)} tools "
              f"({LAND_MAX_DENIALS} denials max), soft {RESERVE_SOFT_SECONDS}s, "
              f"hard {RESERVE_HARD_SECONDS}s")
        print(f"sound    : {len(DISQUALIFIERS)} disqualifying constructs refused on "
              f"{list(SOUND_TOOLS)}, {SOUND_MAX_DENIALS} denials max")
        print(f"audit    : {AUDIT_MAX_DENIALS} statement-vs-informal review(s), "
              f"proof block present: {proof_block_present()}")
        print(f"write    : write-through on {list(WRITE_TOOLS)} for *.lean under {WORK}, "
              f"{WRITE_MAX_CLEARS} clears max, {WRITE_MAX_BYTES} byte cap")
        print(f"finalize : {FINALIZE_COMPILES} compiles + {SORRY_FALLBACK_COMPILES} "
              f"statement-with-`sorry` compiles, fence {FINALIZE_DEADLINE}s")
        for k, v in MODEL.items():
            print(f"  {k:18s} {v}")
        return 0

    if a.mode == "selftest":
        return selftest(a.api_base or "unused")

    if a.mode == "agent":
        import asyncio
        if not a.api_base:
            ap.error("--api-base is required (or set AGENT_API_BASE)")
        res = asyncio.run(run_problem(a.api_base, PROBLEM.read_text(errors="replace"),
                                      mcp=not a.no_mcp, max_turns=a.max_turns))
        a.result.write_text(json.dumps(res, indent=1))
        print(json.dumps({k: v for k, v in res.items()
                          if k not in ("events", "solution_lean", "compiler_output")}))
        return 0 if res.get("compiles") else 1

    ap.error(f"{a.mode} not implemented yet")
    return 2


if __name__ == "__main__":
    sys.exit(main())
