#!/usr/bin/env python3
"""The grader. RUNNER-OWNED, never candidate-owned.

This module exists so the harness can be evolved without limit. It used to live inside
`lean_harness.py`, which meant the proposer rewrote the grader and its own harness in one
file, and `meta_harness.admit` had to byte-compare ~10 frozen symbols to stop a candidate
weakening the metric it is scored on. That protected the metric at the cost of forbidding
whole regions of the harness from being touched at all.

Splitting it removes the tradeoff. The candidate is now free to rewrite 100% of the harness,
because the harness no longer contains the thing that judges it: the runner imports THIS file
(tracked in git, outside the candidate's mount) and the candidate cannot shadow it.

Two certificates are produced per instance, both intended to be read by the next round's
proposer as evidence:

  type_correctness   type correctness of the generated file, from the pinned toolchain.
                     Sound on its own: it needs no reference.
  semantic_equivalence    statement-level equivalence of the generated theorem against the
                     labeled gold theorem (BEq / BEqL / BEq+). Computed in `grade_semantic_equivalence.py`, out of
                     band, because it needs a Mathlib-loaded REPL. Absent when the row has no
                     gold (devset771), never silently false.

Type correctness cannot see unfaithfulness -- a weakened statement that compiles scores the
same as a correct one -- which is why the BEq certificate exists and why the two are reported
side by side rather than collapsed into one number.
"""
from __future__ import annotations

import glob
import hashlib
import os
import re
import subprocess
import uuid
from pathlib import Path

# Paths. Same env contract the harness uses, so in-container and local runs agree.
WORK = Path(os.environ.get("AGENT_WORK", "/work"))
SOLUTION = WORK / "solution.lean"
PROJECT = WORK / "proj"
MATHLIB = Path(os.environ.get("AGENT_MATHLIB", "/mathlib"))
ELAN = Path(os.environ.get("AGENT_ELAN", "/elan"))
COMPILE_TIMEOUT = int(os.environ.get("AGENT_COMPILE_TIMEOUT", "600"))

ANSWER_NAME = "Work.lean"

# Carried inside every semantic_equivalence block so a record is self-describing: whoever (or
# whatever) reads a rollout does not have to already know what "BEq" means to interpret it.
SEMANTIC_METRIC_DESC = (
    "BEq+ / BEqL: is each of (gold statement, generated statement) provable FROM the other? "
    "Proofs are ignored -- this judges the STATEMENT only, so a correct statement with an "
    "unfinished proof still scores equivalent. BEqL is the strict variant (the proof must "
    "actually use the other theorem); BEq+ is the headline one and is more permissive. "
    "Poiroux et al., EMNLP 2025."
)


# ===========================================================================
# TOOLCHAIN
# ===========================================================================
def pinned_toolchain(project: Path | None = None) -> str:
    """The Lean version the project pins, e.g. "leanprover/lean4:v4.23.0".

    Read from `lean-toolchain`, the same file `lake` and the LSP obey, so the grader compiles
    with exactly the toolchain the agent's tools were talking to.
    """
    project = project or PROJECT
    f = project / "lean-toolchain"
    if not f.is_file():
        f = MATHLIB / "lean-toolchain"
    return f.read_text(errors="replace").strip()


def lean_bin(project: Path | None = None) -> str:
    """The pinned toolchain's `lean` binary.

    NOT `/elan/bin/lean`: that is elan's proxy shim, which resolves through $ELAN_HOME, and
    `--containall` gives the container no home. NOT a glob over toolchains either -- with two
    installed, a glob takes whatever sorts first and the grader could silently compile against
    a different Lean than the project pins.
    """
    project = project or PROJECT
    want = pinned_toolchain(project)
    d = ELAN / "toolchains" / want.replace("/", "--").replace(":", "---")
    cand = d / "bin" / "lean"
    if cand.is_file() and os.access(cand, os.X_OK):
        return str(cand)
    have = sorted(x.name for x in (ELAN / "toolchains").glob("*")) \
        if (ELAN / "toolchains").is_dir() else []
    raise RuntimeError(
        f"project pins {want!r} -> expected {cand}, which is missing. "
        f"Installed toolchains: {have or 'none'}. Refusing to grade with a different Lean "
        f"than the agent compiled against.")


def lean_path(project: Path | None = None) -> str:
    """Olean search path over the prebuilt packages.

    Note the trailing `lean`: oleans live at `.lake/packages/<pkg>/.lake/build/lib/lean/`,
    one level deeper than the obvious guess.
    """
    project = project or PROJECT
    parts = sorted(glob.glob(str(MATHLIB / ".lake/packages/*/.lake/build/lib/lean")))
    own = project / ".lake/build/lib/lean"
    if own.is_dir():
        parts.append(str(own))
    if not parts:
        raise RuntimeError(f"no built packages under {MATHLIB}")
    return ":".join(parts)


def compile_text(code: str, *, work: Path | None = None,
                 project: Path | None = None) -> tuple[bool, str]:
    """Compile a string. Returns (ok, compiler output).

    THREAD SAFETY IS PART OF THE CONTRACT HERE, because runner.solve() calls the host re-grade
    from inside a 20-thread pool in ONE process. Two things were wrong when the workspace was
    carried in module globals instead of arguments:

      * the scratch file was a fixed `WORK/"_grade.lean"`, so concurrent grades wrote and read
        the SAME path -- one thread's answer could be compiled as another's, and the `finally`
        unlink deleted a file a third thread's `lean` was still opening, turning a genuine pass
        into a spurious failure;
      * `lean_bin()` / `lean_path()` were called with no argument, so the toolchain and olean
        path came from whichever workspace most recently entered the grader rather than the one
        being graded -- a record could truthfully report toolchain X while having compiled
        against Y.

    Both are gone: the workspace arrives as an argument and the scratch name is unique per
    call. The globals remain only as defaults, for the single-threaded in-container path.
    """
    work = work or WORK
    project = project or PROJECT
    scratch = work / f"_grade.{uuid.uuid4().hex}.lean"
    try:
        scratch.write_text(code)
    except OSError as e:
        return False, f"could not write scratch file: {e}"
    try:
        env = {**os.environ, "LEAN_PATH": lean_path(project), "ELAN_HOME": str(ELAN)}
        p = subprocess.run([lean_bin(project), str(scratch)], capture_output=True, text=True,
                           timeout=COMPILE_TIMEOUT, env=env, cwd=str(work))
        # A NEGATIVE returncode means a SIGNAL killed lean, and subprocess.run does not raise
        # for that -- it returns quietly with empty output. This box has no swap, so an OOM
        # burst (108 lean + 63 lake seen concurrently on 2026-08-29) makes the kernel SIGKILL a
        # compile; without this branch that arrives as (False, "(no output)"), indistinguishable
        # from a rejection and frozen as a real zero. Reuse the "could not execute lean" prefix
        # so LEAN_UNUSABLE already covers it.
        if p.returncode < 0:
            return False, f"could not execute lean: killed by signal {-p.returncode}"
        return p.returncode == 0, ((p.stdout or "") + (p.stderr or "")).strip() or "(no output)"
    except subprocess.TimeoutExpired:
        return False, f"compile timed out after {COMPILE_TIMEOUT}s"
    except OSError as e:
        return False, f"could not execute lean: {e}"     # ENVIRONMENT failure, not the agent's
    finally:
        scratch.unlink(missing_ok=True)


CANARY = "import Mathlib\n\ntheorem __harness_canary : True := trivial\n"


# ===========================================================================
# VACUITY
# ===========================================================================
# A declaration may carry attributes and modifiers before the keyword -- `noncomputable
# instance`, `@[simp] theorem`. Matching the bare keyword at line start once rejected a real
# `noncomputable instance` as "declares nothing", which under-reports as badly as the reverse.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(theorem|lemma|example|instance)\b", re.M)
VACUOUS_GOAL = re.compile(r":\s*\(?\s*True\s*\)?\s*(:=|$)", re.M)
# `theorem t (h : False) : P := h.elim` typechecks and proves nothing. No faithful
# formalization of a real theorem assumes False, so this is safe to reject outright.
FALSE_HYP = re.compile(r"\(\s*[\w\s]*:\s*False\s*\)")


def vacuity(code: str) -> str | None:
    """Why this file is not an answer, or None if it might be one.

    A compiling file is not a formalization. `lean` exits 0 on `import Mathlib` +
    `#check 1 + 1`, and on `theorem foo : True := by trivial`. Both were scored as passes in
    an earlier run: 10 of 20 reported passes were one of those two shapes, inflating the rate
    2-4x. Deliberately syntactic -- whether a statement is FAITHFUL is the BEq certificate's
    question, not this one's.
    """
    if not code.strip():
        return "empty"
    if not DECL.search(code):
        return "declares no theorem/lemma/example/instance"
    decls = [m.start() for m in DECL.finditer(code)]
    bounds = decls[1:] + [len(code)]
    # Reject only if EVERY declaration is trivial: one scratch `example : True` alongside a
    # real theorem is not a vacuous file.
    if decls and all(VACUOUS_GOAL.search(code[a:b]) for a, b in zip(decls, bounds)):
        return "every declaration states `True`, which is trivially provable"
    if decls and all(FALSE_HYP.search(code[a:b]) for a, b in zip(decls, bounds)):
        return "every declaration assumes False, which proves nothing"
    if "sorry" in code:
        return "contains sorry"
    return None


# Tactics that close a goal on their own. Used ONLY for reporting, never for rejection:
# `by simp` is a correct proof of many real lemmas, so rejecting it would throw away valid
# work. Tracked because "statement eroded until a decision procedure closes it" is the
# cheapest way to raise a type-correctness score without formalizing anything.
CLOSERS = re.compile(r":=\s*by\s+(trivial|rfl|simp|decide|norm_num|tauto|omega|aesop)\s*$",
                     re.M)
CONSTS = re.compile(r"\b([A-Z][A-Za-z0-9]*(?:\.[A-Za-z0-9_']+)+)\b")


def statement_signals(code: str) -> dict:
    """Cheap, judge-free signals that make statement erosion visible round over round."""
    decls = DECL.findall(code or "")
    return {
        "n_declarations": len(decls),
        "distinct_constants": len(set(CONSTS.findall(code or ""))),
        "one_tactic_proofs": len(CLOSERS.findall(code or "")),
        "chars": len(code or ""),
    }


# ===========================================================================
# INFRASTRUCTURE vs AGENT FAILURE
# ===========================================================================
# A run that failed because the model server was unreachable is NOT evidence about the
# harness, and must not be recorded as a graded failure: resume keys on result.json existing,
# so a server outage would otherwise permanently freeze a false negative for every problem
# in flight. These are matched against the agent_error string the harness reports.
# Every alternative is a named exception type or a quoted phrase. NOTHING here may be a bare
# number: an earlier version of this pattern listed `503`, which -- being unanchored -- matched
# "context length 15037 tokens", "aborted after 5030ms", "Work.lean line 503" and "exceeded
# 2503 seconds". Token counts, millisecond timings and line numbers routinely contain 503, so
# ordinary agent failures were being reclassified as outages. HTTP codes are matched only with
# their reason phrase attached.
INFRA_ERROR = re.compile(
    # --- named exception types from the openai / httpx / requests / aiohttp stack ---
    r"APIConnectionError|APITimeoutError|APIStatusError|"
    r"ConnectionRefusedError|ConnectionResetError|ConnectionError|"
    r"RemoteProtocolError|RemoteDisconnected|ReadTimeoutError|ReadTimeout|"
    r"ClientConnectorError|ServerTimeoutError|ServerDisconnectedError|"
    r"InternalServerError|RateLimitError|"
    # --- vLLM's own death signature. This is THE common one and it was missing entirely: a
    #     vLLM engine that dies mid-arm raises AsyncEngineDeadError for every later request,
    #     which was classified as the agent's own failure, so the rows were persisted as real
    #     zeros, `outstanding` stayed 0, the arm exited rc=0 and got CACHED as complete --
    #     freezing a whole arm of false negatives, potentially into `parent@core`, for the life
    #     of the experiment. ---
    r"AsyncEngineDeadError|EngineDeadError|Engine loop has died|"
    r"Background loop has errored|engine core (?:has died|proc died)|"
    # --- quoted phrases. No bare numbers, ever: an earlier version listed `503`, which being
    #     unanchored also matched "context length 15037 tokens", "aborted after 5030ms",
    #     "Work.lean line 503" and "exceeded 2503 seconds", reclassifying ordinary agent
    #     failures as outages. HTTP codes are matched only in the SDK's `Error code: NNN` form
    #     or with their reason phrase attached. ---
    r"ECONNREFUSED|Connection refused|Connection reset by peer|"
    r"Max retries exceeded|Cannot connect to host|Server disconnected|"
    r"peer closed connection|Remote end closed connection|"
    r"Service Unavailable|Bad Gateway|Gateway Time-?out|Too Many Requests|"
    r"Error code: 50[0-9]|Error code: 429|"
    r"Authentication is required|"
    # --- the tunnel bounce, which keeper.sh predicts in its own comments and which this
    #     pattern did not catch. `ssh -O cancel` re-points a forwarded port out from under
    #     every in-flight request on it, and httpx surfaces that as a bare `ReadError('')`
    #     with `provider_message: Network error` -- no exception name from the list above, no
    #     HTTP code, and vLLM logs nothing because the request never reached it. 79 rollouts
    #     across the step0val arms were persisted as real zeros this way. `ReadError` must
    #     stay AFTER `ReadTimeoutError|ReadTimeout` above only for readability; alternation
    #     is leftmost-first and these are disjoint strings.
    r"ReadError|Network error|"
    # --- a stream that stops mid-generation. vLLM ends the SSE without a terminal chunk when
    #     the engine or the tunnel drops it, so the agent has a truncated turn and no finish
    #     reason. This is the endpoint failing, not the agent reasoning badly. ---
    r"ended without a finish reason",
    re.I)

# The model emitted a tool call the SERVER refused to accept, so the request 400s and the
# rollout dies mid-trajectory. Two shapes, both from the Mistral tool-call parser rather than
# from anything the harness controls:
#
#     Function name was  edit but must be a-z, A-Z, ...   a leading space on the tool name
#     Expecting property name enclosed in double quotes   the arguments are not valid JSON
#     Unterminated string starting at / Extra data:       (same, other json.loads messages)
#
# Kept SEPARATE from INFRA_ERROR because the endpoint was up and answering -- calling it an
# outage would be a lie in the log -- but it gets the same treatment, because it says nothing
# about the harness under test. The harness registered `edit`; the serving layer handed back
# ` edit`. Freezing that as a 0.00 measures the tool-call parser, not the harness, and it hit
# both step0val arms at similar rates (init 45, best 29), i.e. it is pure added variance.
TOOLCALL_PROTOCOL = re.compile(
    # DO NOT length-bound the function name here. The original pattern bridged
    # `Function name was ... but must be` with `.{0,80}?`, which failed twice on step0val best
    # (2026-08-29): when the model breaks tool-call syntax it leaks control tokens and prose
    # INTO the name field, so vLLM echoes back whatever it got -- 348 and 883 chars, spanning
    # newlines, which `.` does not cross. Both rows persisted as real 0s: exactly the false
    # negative this function exists to prevent. The garbage is unbounded by nature, so match
    # vLLM's OWN fixed validation phrase, which no agent prose or Lean can produce, and keep a
    # generous two-sided anchor as a fallback for minor wording drift.
    r"must be a-z, A-Z, 0-9, or contain underscores and dashes|"
    r"Function name was [\s\S]{0,4000}? but must be|"
    r"Expecting property name enclosed in double quotes|"
    r"Unterminated string starting at|"
    r"Expecting ',' delimiter|"
    r"Extra data: line|"
    # An assistant message with neither content nor tool calls in the resent history (a
    # reply stopped by the token cap during reasoning).
    r"Invalid assistant message",
    re.I)

# Lean itself could not be run. Distinct from "Lean ran and rejected the file", which is a
# real result. Both phrases are produced by compile_text above.
# "LEAN ENVIRONMENT BROKEN" is what type_correctness() writes when the canary
# (import Mathlib + a trivial theorem) fails to compile: the toolchain, not the file, is at
# fault. It was recorded in diagnostics and even surfaced as `lean_broken`, but was NOT listed
# here -- so infra_failure() returned None and the row persisted as a real zero anyway. Seen on
# step0val init rollout4/Mizar_ModelTheory_046949, which carried lean_broken=True and a 7291-char
# solution that was never actually graded.
LEAN_UNUSABLE = ("could not execute lean", "could not write scratch file",
                 "LEAN ENVIRONMENT BROKEN")


def infra_failure(agent_error: str | None, compiler_output: str = "") -> str | None:
    """Name the infrastructure fault, or None if this run is the agent's own result.

    Deliberately conservative: only faults that clearly indicate the MODEL ENDPOINT or the
    LEAN INSTALL was unavailable count. An agent that wrote bad Lean, ran out of turns, hit a
    context limit, or crashed on its own logic is a real datum and must stay in the
    denominator.

    This does NOT affect the verdict -- see grade(). It is a separate signal, so the runner can
    decline to persist a row that says nothing about the harness, and let the problem be
    retried by a later pass instead of freezing a false negative.
    """
    if agent_error and INFRA_ERROR.search(agent_error):
        return f"model endpoint unreachable: {agent_error[:200]}"
    if agent_error and TOOLCALL_PROTOCOL.search(agent_error):
        return f"tool-call protocol rejected by the server: {agent_error[:200]}"
    out = compiler_output or ""
    for phrase in LEAN_UNUSABLE:
        if phrase in out:
            return f"lean unusable: {out[:200]}"
    return None


def _stop_reason(events: list[dict]) -> str | None:
    """vibe reports a forced stop by appending <vibe_stop_event>REASON</vibe_stop_event> to
    the history (TurnLimitMiddleware, PriceLimitMiddleware, ...). Absent means the agent ended
    on its own terms."""
    for e in reversed(events):
        m = re.search(r"<vibe_stop_event>(.*?)</vibe_stop_event>", e.get("text") or "",
                      re.S)
        if m:
            return m.group(1).strip()
    return None


def _count_tools(events: list[dict]) -> dict[str, int]:
    """Tool calls, counted from `effect` entries."""
    out: dict[str, int] = {}
    for e in events:
        if e.get("type") not in ("effect", "callback"):
            continue
        det = e.get("detail") if isinstance(e.get("detail"), dict) else {}
        name = det.get("toolName") or e.get("title") or det.get("kind") or "unknown"
        out[str(name)] = out.get(str(name), 0) + 1
    return out


# ===========================================================================
# GRADE
# ===========================================================================
def type_correctness(text: str, project: Path | None = None,
                     work: Path | None = None) -> dict:
    """The type-correctness certificate for one generated file.

    Self-contained and reference-free: everything here is a property of the produced Lean
    plus the pinned toolchain. `diagnostics` carries the compiler's own words, because the
    proposer's most useful signal is WHY a file failed, not merely that it did.

    `work` is where the scratch file goes; it must be passed by any CONCURRENT caller, so that
    two threads grading two workspaces cannot land on one directory. See compile_text().
    """
    project = project or PROJECT
    work = work or WORK
    empty = not text.strip()
    if empty:
        # No file to compile, but the canary is still checked below: "the agent wrote nothing"
        # and "Lean is broken so nothing could be graded" look identical in the record
        # otherwise, and a whole run of the latter would read as a genuine 0%.
        ok, out, why = False, "no answer written", "no answer written"
    else:
        ok, out = compile_text(text, work=work, project=project)
        why = vacuity(text)
    passed = bool(ok and why is None)

    # A failure re-checks the canary: a broken Lean install emits ordinary-looking compile
    # errors, so without this "the agent failed" and "the environment failed" are
    # indistinguishable and a whole run of real-looking failures reads as a genuine 0%.
    canary_ok = None
    if not passed:
        cok, cout = compile_text(CANARY, work=work, project=project)
        canary_ok = bool(cok)
        if not cok:
            out = f"LEAN ENVIRONMENT BROKEN, verdict not trustworthy:\n{cout[:600]}"

    try:
        toolchain = pinned_toolchain(project)
    except OSError:
        toolchain = None

    return {
        "compiles": passed and canary_ok is not False,
        "exit_ok": bool(ok),
        "rejected_because": why,
        "has_sorry": "sorry" in text,
        "diagnostics": out[:8000],
        "canary_ok": canary_ok,
        "toolchain": toolchain,
        "graded_sha256": hashlib.sha256(text.encode(errors="replace")).hexdigest()[:16],
        "graded_chars": len(text),
    }


def regrade_workspace(ws: Path) -> dict:
    """Grade a finished workspace FROM THE HOST, independently of the container.

    WHY THIS EXISTS, AND WHY IT IS THE ONLY VERDICT THAT COUNTS.

    Moving this module out of the harness file lets the proposer rewrite 100% of the harness.
    But the harness is what writes `result.json` inside the container, and the runner reads it
    -- so on its own, extraction still leaves a candidate able to score itself by having its
    `grade()` return `{"compiles": True}` and never calling Lean at all. Freezing symbols was
    the old defence, and it is exactly the constraint we removed.

    So the runner re-grades here instead of trusting the report. `{ws}` is a host bind mount,
    so `proj/Work.lean` -- the artefact, which the container cannot forge past this point -- is
    readable directly, and it is recompiled with the pinned toolchain on the host. The
    candidate's own verdict becomes advisory; this one is authoritative.

    Returns the same `type_correctness` shape, plus `regraded_on_host: True`.

    CALLED CONCURRENTLY -- runner.solve() runs this from a 20-thread pool in one process, so
    the workspace is passed down as arguments. It used to be assigned into the module globals
    `WORK`/`PROJECT`/`SOLUTION` under a try/finally, which was wrong three ways: threads
    overwrote each other's values mid-grade so a file could be compiled as another workspace's,
    the `finally` restored whatever the LAST thread happened to capture on entry (leaving the
    globals pointing at an arbitrary finished workspace afterwards), and the scratch filename
    was shared. Nothing here mutates module state now.
    """
    project = ws / "proj"
    answer = project / ANSWER_NAME
    text = ""
    if answer.is_file():
        try:
            text = answer.read_text(errors="replace")
        except OSError:
            text = ""
    cert = type_correctness(text, project, work=ws)
    cert["regraded_on_host"] = True
    # The exact bytes graded, handed back so the caller does not have to re-read the file and
    # risk grading one version while recording another. This is what the equivalence pass must
    # score, so that both metrics judge the same artefact.
    cert["graded_text"] = text
    return cert


def grade(*, events: list, history_len: int, agent_error: str | None,
          elapsed: float, project: Path | None = None, model: dict | None = None) -> dict:
    """Recompile the produced file and return the round record for one instance.

    Authoritative and independent: the file is recompiled regardless of what the agent
    reported. `semantic_equivalence` is left as a pending marker here and filled in by the
    post-round `grade_semantic_equivalence.py` pass, which needs a Mathlib-loaded REPL.
    """
    project = project or PROJECT
    answer = project / ANSWER_NAME
    text = ""
    if answer.is_file():
        try:
            text = answer.read_text(errors="replace")
        except OSError:
            text = ""
    if text:
        try:
            SOLUTION.write_text(text)           # the contract name, same bytes
        except OSError:
            pass

    cert = type_correctness(text, project)
    infra = infra_failure(agent_error, cert.get("diagnostics", ""))

    return {
        # WHY THE AGENT STOPPED. 90% of runs at the n=202 checkpoint were terminated by the
        # turn cap rather than by the agent deciding it was done -- a fact recoverable only by
        # grepping message text, so it was invisible in every summary.
        "stop_reason": _stop_reason(events),

        # ---- verdict: type correctness ----
        # IDENTICAL to the pre-split formula (`passed and not lean_broken`). `infra_failure`
        # deliberately does NOT enter here: a file that compiled clean compiled clean, even if
        # the model endpoint dropped on a later turn, and letting an outage flip a real pass to
        # a failure would corrupt the metric in the same direction it is meant to protect.
        # Whether to KEEP this row at all is the runner's decision, from `infra_failure`.
        "compiles": cert["compiles"],
        "compiles_raw": cert["exit_ok"],
        "rejected_because": cert["rejected_because"],
        "has_sorry": cert["has_sorry"],
        "type_correctness": cert,

        # ---- verdict: does the statement MEAN what the gold statement means? ----
        # Filled in after the round by harness_runner/grade_semantic_equivalence.py, which needs a Mathlib-loaded
        # REPL. `status` is a STRING sentinel, never False: a missing verdict that defaults to
        # a falsy value is exactly how "no answer written" once got counted as a real failure.
        "semantic_equivalence": {"status": "pending", "metric": SEMANTIC_METRIC_DESC},
        "faithful": "not_evaluated",

        # ---- excluded from the denominator: not evidence about the harness ----
        # An unreachable model endpoint is an outage, not a result. Recorded explicitly so the
        # runner can DECLINE to persist this row and let a later run retry the problem.
        "infra_failure": infra,
        "lean_broken": cert.get("canary_ok") is False,
        "agent_error": agent_error,

        # ---- the answer ----
        "solution_lean": text,
        "solution_chars": len(text),
        "statement_signals": statement_signals(text),
        "compiler_output": cert["diagnostics"][:4000],

        # ---- effort ----
        "elapsed_sec": elapsed,
        "history_entries": history_len,
        "tool_calls": _count_tools(events),
        "entry_types": {t: sum(1 for e in events if e.get("type") == t)
                        for t in sorted({e.get("type") for e in events if e.get("type")})},

        # ---- evidence ----
        "events": events,
        "model": model or {},
    }
