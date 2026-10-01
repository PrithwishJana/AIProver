#!/usr/bin/env python3
"""aiprover -- call the AIProver agent from a coding agent (Claude Code, Codex).

AIProver = our fine-tuned Leanstral-class model DRIVEN BY the evolved hevo harness
(`../harness/harness.py`, champion d01_r04 of hevo_mixed_v1). Every call is a full agentic
Lean session -- the model writes, compiles, searches Mathlib and repairs through lean-lsp-mcp,
for up to 200 turns by default (`[runtime].max_turns`, `submit --max-turns`) -- not a single
completion. A call takes minutes (median ~13 min, p90 ~40 min at the champion's 100-turn
setting), so calls are JOBS: submitted, run detached, waited on, read.

    aiprover doctor [--full]                 verify the whole environment (run this first)
    aiprover submit --problem P.txt ...      start a job; prints its id and returns at once
    aiprover wait JOB [JOB ...] [--timeout 540] [--any]
    aiprover result JOB [--json] [--all]     summary + the best Lean file
    aiprover status [JOB]  |  list  |  cancel JOB
    aiprover check FILE.lean [--statement-only]   mechanical checks (a) type-correct, (b) complete
    aiprover probe FILE.lean                 statement sanity: counterexample search + automation closers
    aiprover search QUERY [--lib cslib|mathlib|all|loogle|leansearch|leandex]   library search
    aiprover extract FILE.lean --line N      the goal at a `sorry` as a standalone lemma (Lean writes the binders)
    aiprover expand --problem P.txt [--out P2.txt]   rewrite the proof as explicit steps (writer + critic)
    aiprover backtranslate FILE.lean         say in plain English what each declaration of the Lean states
    aiprover ask "question" [--file F.lean]  one free-form question
      These three ask an LLM. --backend aiprover|claude|codex|auto (default auto): inside a Claude Code
      session `claude -p` answers on your Claude subscription, inside Codex `codex exec` on yours,
      standalone the AIProver model server. [helpers] in aiprover.toml sets the default.
    aiprover render ...                      print the problem.txt a submit would send
    aiprover tunnel [up|status|down]         the SSH tunnel to the model server
    aiprover workspace                       path of the Lean scratch project for YOUR files
    aiprover mcp-serve                       exec lean-lsp-mcp for the coding agent (MCP launcher)

Stdlib only (Python >= 3.11). Config: $AIPROVER_CONFIG, else the nearest `aiprover.toml`
walking up from this file, else ~/.config/aiprover/aiprover.toml.
"""
from __future__ import annotations

import argparse
import fcntl
import glob
import hashlib
import importlib.util
import json
import os
import random
import re
import shlex
import shutil
import signal
import socket
import string
import subprocess
import sys
import threading
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
SKILL_DIR = HERE.parent
HARNESS = SKILL_DIR / "harness" / "harness.py"
GRADER = SKILL_DIR / "harness" / "grade_type_correctness.py"
MANIFEST = SKILL_DIR / "harness" / "MANIFEST.json"

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT_ROOTS = ("Mathlib", "Init", "Std", "Batteries", "Aesop", "Qq", "ImportGraph",
                "Plausible", "ProofWidgets", "LeanSearchClient", "Lean",
                "Cslib")       # pinned dependency of the project, built next to Mathlib


class AIProverError(RuntimeError):
    pass


# =============================================================================
# CONFIG
# =============================================================================
def _find_config() -> Path:
    env = os.environ.get("AIPROVER_CONFIG")
    if env:
        p = Path(env).expanduser()
        if not p.is_file():
            raise AIProverError(f"$AIPROVER_CONFIG={env} does not exist")
        return p
    for base in [HERE, *HERE.parents]:
        cand = base / "aiprover.toml"
        if cand.is_file():
            return cand
    cand = Path("~/.config/aiprover/aiprover.toml").expanduser()
    if cand.is_file():
        return cand
    raise AIProverError("no aiprover.toml found: set $AIPROVER_CONFIG, or keep the skill inside "
                        "AIProver_plugin/ (symlinks are followed)")


class Config:
    def __init__(self) -> None:
        self.path = _find_config()
        raw = tomllib.loads(self.path.read_text())
        self.ep = raw.get("endpoint", {})
        self.rt = raw.get("runtime", {})
        self.paths = raw.get("paths", {})
        self.helpers = raw.get("helpers", {})

    def p(self, key: str) -> Path:
        v = self.paths.get(key, "")
        if not v:
            raise AIProverError(f"[paths].{key} is empty in {self.path}")
        return Path(os.path.expandvars(v)).expanduser()

    @property
    def work_root(self) -> Path:
        r = Path(os.path.expandvars(self.rt.get("work_root", "~/.aiprover"))).expanduser()
        r.mkdir(parents=True, exist_ok=True)
        return r

    @property
    def jobs(self) -> Path:
        d = self.work_root / "jobs"
        d.mkdir(parents=True, exist_ok=True)
        return d

    @property
    def max_parallel(self) -> int:
        return max(1, int(self.rt.get("max_parallel", 4)))

    @property
    def timeout(self) -> int:
        return int(self.rt.get("timeout_sec", 5400))

    @property
    def max_turns(self) -> int:
        return int(self.rt.get("max_turns", 100))

    @property
    def mode(self) -> str:
        return str(self.ep.get("mode", "ssh")).strip().lower()

    @property
    def api_base(self) -> str:
        if self.mode == "direct":
            b = str(self.ep.get("api_base", "")).strip()
            if not b:
                raise AIProverError("[endpoint].mode is 'direct' but api_base is empty")
            return b.rstrip("/")
        return f"http://127.0.0.1:{int(self.ep['local_port'])}/v1"

    @property
    def api_key(self) -> str:
        return str(self.ep.get("api_key", "EMPTY") or "EMPTY")

    def venv_python(self, key: str) -> Path:
        return self.p(key) / "bin" / "python3"

    def site_packages(self, key: str) -> Path:
        hits = sorted(glob.glob(str(self.p(key) / "lib" / "python3*" / "site-packages")))
        if not hits:
            raise AIProverError(f"no site-packages under {self.p(key)}")
        return Path(hits[-1])

    def rg_dir(self) -> str | None:
        v = self.paths.get("rg_dir", "")
        return str(Path(os.path.expandvars(v)).expanduser()) if v else None


# =============================================================================
# THE MODEL ENDPOINT AND ITS TUNNEL
# =============================================================================
def _http_json(url: str, *, data: dict | None = None, key: str = "EMPTY",
               timeout: float = 10.0) -> dict:
    body = json.dumps(data).encode() if data is not None else None
    req = urllib.request.Request(url, data=body, method="POST" if body else "GET",
                                 headers={"Content-Type": "application/json",
                                          "Authorization": f"Bearer {key}"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode())


def probe(cfg: Config, tries: int = 3) -> dict | None:
    """GET /v1/models. Three tries, because one dropped probe is not an outage."""
    for i in range(tries):
        try:
            return _http_json(cfg.api_base + "/models", key=cfg.api_key, timeout=10)
        except Exception:                                        # noqa: BLE001
            if i + 1 < tries:
                time.sleep(2)
    return None


def served_model(cfg: Config, models: dict | None) -> str:
    want = str(cfg.ep.get("model", "") or "").strip()
    ids = [m.get("id") for m in (models or {}).get("data", [])]
    if want:
        if ids and want not in ids:
            raise AIProverError(f"[endpoint].model={want!r} is not served; server has {ids}")
        return want
    if not ids:
        raise AIProverError("the server reports no models")
    return ids[0]


def _port_in_use(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(1)
        return s.connect_ex(("127.0.0.1", port)) == 0


def _kill_forwards(spec: str) -> int:
    """Kill only `ssh` processes whose argv carries exactly `-L <spec>`. Never `pkill -f`: that
    matches ANY command line containing the text -- including the shell that is running us."""
    n = 0
    for d in Path("/proc").iterdir():
        if not d.name.isdigit() or int(d.name) == os.getpid():
            continue
        try:
            argv = (d / "cmdline").read_bytes().split(b"\0")
        except OSError:
            continue
        argv = [a.decode(errors="replace") for a in argv if a]
        if not argv or Path(argv[0]).name != "ssh":
            continue
        if any(a == "-L" and i + 1 < len(argv) and argv[i + 1] == spec
               for i, a in enumerate(argv)) or f"-L{spec}" in argv:
            try:
                os.kill(int(d.name), signal.SIGTERM)
                n += 1
            except OSError:
                pass
    return n


def _control_path(cfg: Config) -> str:
    """The ControlMaster socket, whether given as control_socket or inside ssh_options."""
    sock = str(cfg.ep.get("control_socket", "") or "").strip()
    if sock:
        return str(Path(sock).expanduser())
    opts = [str(o) for o in cfg.ep.get("ssh_options", []) or []]
    for i, o in enumerate(opts):
        if o == "-S" and i + 1 < len(opts):
            return str(Path(opts[i + 1]).expanduser())
        m = re.match(r"(?:-o\s*)?ControlPath=(.+)", o)
        if m:
            return str(Path(m.group(1)).expanduser())
    return ""


def _ssh_base(cfg: Config) -> list[str]:
    ep = cfg.ep
    cmd = ["ssh", "-n", "-o", "BatchMode=yes", "-o", "ConnectTimeout=20",
           "-p", str(int(ep.get("ssh_port", 22) or 22))]
    sock = str(ep.get("control_socket", "") or "").strip()
    if sock:
        cmd += ["-S", str(Path(sock).expanduser())]
    cmd += [os.path.expanduser(str(o)) for o in ep.get("ssh_options", []) or []]
    return cmd


def _ssh_dest(cfg: Config) -> str:
    host = str(cfg.ep.get("ssh_host", "")).strip()
    if not host:
        raise AIProverError("[endpoint].ssh_host is empty")
    user = str(cfg.ep.get("ssh_user", "") or "").strip()
    return f"{user}@{host}" if user else host


def remote_target(cfg: Config) -> tuple[str, int, str]:
    """(host, port, where-it-came-from) of the model server, AS SEEN FROM ssh_host.

    With `server_handoff` set, both are read fresh from that file on ssh_host every time the
    tunnel is (re)opened -- our vLLM jobs write `node=<n> port=<p> job=<j>` there once the server
    answers -- so a server that moves to a new compute node is followed with no config edit.
    Otherwise remote_host/remote_port are used as written.
    """
    ep = cfg.ep
    handoff = str(ep.get("server_handoff", "") or "").strip()
    if handoff:
        r = subprocess.run(_ssh_base(cfg) + [_ssh_dest(cfg), f"cat {shlex.quote(handoff)}"],
                           capture_output=True, text=True, timeout=60)
        kv = dict(re.findall(r"(\w+)=(\S+)", r.stdout or ""))
        if (r.returncode != 0 or not kv.get("node") or not kv.get("port")) \
                and ep.get("remote_host") and ep.get("remote_port"):
            # Handoff unreadable but a fixed address is configured: use it.
            return (str(ep["remote_host"]), int(ep["remote_port"]),
                    f"config (handoff {handoff} unreadable)")
        if r.returncode != 0 or not kv.get("node") or not kv.get("port"):
            raise AIProverError(
                f"could not read server_handoff {handoff} on {_ssh_dest(cfg)} (rc={r.returncode}): "
                f"{((r.stdout or '') + (r.stderr or '')).strip()[:300]!r}. Is the model server job "
                f"running and has it announced itself?")
        return kv["node"], int(kv["port"]), f"handoff {handoff} (job {kv.get('job', '?')})"
    return (str(ep.get("remote_host", "127.0.0.1") or "127.0.0.1"), int(ep["remote_port"]),
            "config")


def _forward_spec(cfg: Config, target: tuple[str, int, str] | None = None) -> str:
    host, port, _ = target or remote_target(cfg)
    return f"127.0.0.1:{int(cfg.ep['local_port'])}:{host}:{port}"


def tunnel_up(cfg: Config) -> str:
    """Open the forward. Returns a one-line description. Never prompts (BatchMode)."""
    if cfg.mode != "ssh":
        return "direct mode: no tunnel"
    dest = _ssh_dest(cfg)
    target = remote_target(cfg)
    spec = _forward_spec(cfg, target)
    state = cfg.work_root / "tunnel.json"
    sock = _control_path(cfg)
    if sock:
        chk = subprocess.run(_ssh_base(cfg) + ["-O", "check", dest], capture_output=True,
                             text=True, timeout=30)
        if chk.returncode != 0:
            raise AIProverError(
                f"control socket {sock} is dead ({(chk.stderr or '').strip()[:200]}). Re-open it "
                f"by hand (it may need MFA): ssh -fNM -S {sock} -o ServerAliveInterval=30 {dest}")
        # Cancel the forward WE made last time if it pointed elsewhere: a ControlMaster keeps a
        # stale forward bound to the local port, and a new one on the same port then fails.
        try:
            old = json.loads(state.read_text()).get("spec")
        except (OSError, ValueError):
            old = None
        if old:
            subprocess.run(_ssh_base(cfg) + ["-O", "cancel", "-L", old, dest],
                           capture_output=True, text=True, timeout=30)
        cmd = _ssh_base(cfg) + ["-O", "forward", "-L", spec, dest]
    else:
        # Our own previous forward (the server moved, or it died): kill it so the port frees.
        try:
            old = json.loads(state.read_text()).get("spec")
        except (OSError, ValueError):
            old = None
        if old and _port_in_use(int(cfg.ep["local_port"])):
            _kill_forwards(old)
            time.sleep(1)
        if _port_in_use(int(cfg.ep["local_port"])):
            raise AIProverError(
                f"local port {cfg.ep['local_port']} is already bound but the model does not answer "
                f"there. Kill the stale listener (`aiprover tunnel down`) or change "
                f"[endpoint].local_port.")
        cmd = _ssh_base(cfg) + ["-f", "-N", "-o", "ExitOnForwardFailure=yes",
                                "-o", "ServerAliveInterval=30", "-o", "ServerAliveCountMax=3",
                                "-L", spec, dest]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if r.returncode != 0:
        raise AIProverError(f"ssh forward failed (rc={r.returncode}): "
                            f"{((r.stdout or '') + (r.stderr or '')).strip()[:400]}\n  cmd: "
                            f"{shlex.join(cmd)}")
    state.write_text(json.dumps({"spec": spec, "dest": dest, "source": target[2],
                                 "at": time.time()}))
    return f"forward {spec} via {dest} ({target[2]})"


def tunnel_down(cfg: Config) -> str:
    if cfg.mode != "ssh":
        return "direct mode: no tunnel"
    dest = _ssh_dest(cfg)
    spec = _read_json(cfg.work_root / "tunnel.json").get("spec") or _forward_spec(cfg)
    if _control_path(cfg):
        subprocess.run(_ssh_base(cfg) + ["-O", "cancel", "-L", spec, dest],
                       capture_output=True, text=True, timeout=30)
    else:
        _kill_forwards(spec)
    (cfg.work_root / "tunnel.json").unlink(missing_ok=True)
    return f"cancelled {spec}"


def ensure_endpoint(cfg: Config) -> tuple[str, dict]:
    """The endpoint answers, or raise. Opens/re-opens the tunnel under a cross-process lock."""
    models = probe(cfg, tries=1)
    if models is not None:
        return cfg.api_base, models
    with open(cfg.work_root / ".tunnel.lock", "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        models = probe(cfg, tries=2)            # another process may have fixed it meanwhile
        if models is None and cfg.mode == "ssh":
            tunnel_up(cfg)
            models = probe(cfg, tries=3)
    if models is None:
        raise AIProverError(f"model endpoint {cfg.api_base} does not answer /models "
                            f"(mode={cfg.mode}). Check [endpoint] in {cfg.path} and that the "
                            f"model server is running.")
    return cfg.api_base, models


# =============================================================================
# LEAN: THE GRADER, THE MECHANICAL CHECK, THE SCRATCH PROJECT
# =============================================================================
_GRADER_MOD = None


def grader(cfg: Config):
    """The runner-owned grader, loaded by absolute path with the host Lean in its env."""
    global _GRADER_MOD
    if _GRADER_MOD is None:
        os.environ["AGENT_MATHLIB"] = str(cfg.p("lean_project"))
        os.environ["AGENT_ELAN"] = str(cfg.p("elan_home"))
        spec = importlib.util.spec_from_file_location("_aiprover_grader", GRADER)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)                              # type: ignore[union-attr]
        _GRADER_MOD = mod
    return _GRADER_MOD


AXIOM_PROBE = """

-- AIPROVER AXIOM PROBE (appended by `aiprover check`; not part of your file)
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₂.toList do
    let axs ← Lean.collectAxioms n
    out := out.push s!"{n} :: {axs.toList}"
  logInfo (String.intercalate "\\n" ("AIPROVER_AXIOMS_BEGIN" :: out.toList ++ ["AIPROVER_AXIOMS_END"]))
"""

_COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
_DISQ = [
    (re.compile(r"\bnative_decide\b"), "uses `native_decide` (trusts the compiler; voids the answer)"),
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?axiom\s", re.M),
     "declares an `axiom`"),
    (re.compile(r"\bimplemented_by\b|@\[\s*extern\b"), "uses `implemented_by`/`extern`"),
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*unsafe\s", re.M), "declares something `unsafe`"),
    (re.compile(r"debug\.skipKernelTC"), "sets `debug.skipKernelTC`"),
    (re.compile(r"\bLean\.ofReduceBool\b|\bsorryAx\b"), "names `ofReduceBool`/`sorryAx` directly"),
    (re.compile(r"\bmaxHeartbeats\s+0\b"), "sets `maxHeartbeats 0` (disqualified by our graders)"),
]
_PLACEHOLDER_TEXT = re.compile(r"\bsorry\b|\badmit\b")
# The step2c judge treats a bare `trivial` proof as a PLACEHOLDER, whatever Lean thinks.
_TRIVIAL_PROOF = re.compile(r":=\s*(?:by\s+)?trivial\s*$", re.M)
_IMPORT = re.compile(r"^\s*import\s+([A-Za-z_][\w.]*)", re.M)
_DECL_HEAD = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|example)\b", re.M)


def _errors_only(out: str, limit: int = 60) -> str:
    """Compiler output minus the probe's own info and routine noise, capped for token economy."""
    keep, skip = [], False
    for line in out.splitlines():
        if "AIPROVER_AXIOMS_BEGIN" in line:
            skip = True
        if skip:
            if "AIPROVER_AXIOMS_END" in line:
                skip = False
            continue
        keep.append(line)
    s = "\n".join(keep).strip()
    lines = s.splitlines()
    if len(lines) > limit:
        s = "\n".join(lines[:limit]) + f"\n... ({len(lines) - limit} more lines)"
    return s


def check_lean(cfg: Config, text: str, *, statement_only: bool = False,
               work: Path | None = None, label: str = "answer.lean") -> dict:
    """Mechanical checks (a) type-correctness and (b) completeness, as one verdict.

    (a) compiles with the pinned toolchain and Mathlib, standalone, and is not vacuous;
    (b) no placeholder anywhere -- decided by the KERNEL, not by grep: every constant this file
        adds is walked with `Lean.collectAxioms`, and anything beyond propext / Classical.choice
        / Quot.sound fails (sorryAx = sorry/admit anywhere, incl. private lemmas and defs;
        Lean.ofReduceBool = native_decide; any user axiom).
    In statement-only mode `sorry` in PROOFS is allowed (that task has no proof).
    """
    g = grader(cfg)
    project = cfg.p("lean_project")
    work = work or (cfg.work_root / "checks")
    work.mkdir(parents=True, exist_ok=True)
    problems: list[str] = []
    warnings: list[str] = []
    code = _COMMENT.sub(" ", text)

    if not text.strip():
        return {"verdict": "FAIL", "problems": ["empty file"], "warnings": [],
                "compiles": False, "complete": False, "axioms": {}, "diagnostics": ""}
    for m in _IMPORT.finditer(code):
        if m.group(1).split(".")[0] not in IMPORT_ROOTS:
            problems.append(f"imports `{m.group(1)}`: the answer must be self-contained "
                            f"(Mathlib/Std/Batteries/Aesop/Cslib/... only)")
    for rx, why in _DISQ:
        if rx.search(code):
            problems.append(why)
    if _TRIVIAL_PROOF.search(code):
        warnings.append("a proof is literally `trivial`: the evaluation judge counts that as a "
                        "PLACEHOLDER -- replace it with the tactic that actually closes the goal "
                        "(`decide`, `rfl`, `simp`, `exact ...`)")

    t0 = time.time()
    ok, out = g.compile_text(text + AXIOM_PROBE, work=work, project=project)
    elapsed = round(time.time() - t0, 1)
    axioms: dict[str, list[str]] = {}
    if "AIPROVER_AXIOMS_BEGIN" in out:
        body = out.split("AIPROVER_AXIOMS_BEGIN", 1)[1].split("AIPROVER_AXIOMS_END", 1)[0]
        for line in body.splitlines():
            if " :: " in line:
                n, _, rest = line.partition(" :: ")
                axioms[n.strip()] = [a.strip() for a in rest.strip().strip("[]").split(",")
                                     if a.strip()]
    diag = re.sub(r"\S*_grade\.[0-9a-f]+\.lean", label, _errors_only(out))
    has_error = bool(re.search(r"(^|:)\s*error\b", diag, re.M)) or not ok
    compiles = ok and not has_error
    if not compiles:
        problems.insert(0, "does not compile (see diagnostics)")
    vac = g.vacuity(text)
    if vac and vac != "contains sorry":
        problems.append(f"vacuous: {vac}")

    bad_axioms = {n: sorted(set(a) - STANDARD_AXIOMS) for n, a in axioms.items()
                  if set(a) - STANDARD_AXIOMS}
    uses_sorry = any("sorryAx" in a for a in bad_axioms.values())
    others = {n: [x for x in a if x != "sorryAx"] for n, a in bad_axioms.items()}
    others = {n: a for n, a in others.items() if a}
    if compiles and not axioms:
        problems.append("axiom probe produced no report (unexpected): completeness NOT verified")
    if others:
        problems.append("non-standard axioms: " + "; ".join(
            f"{n} uses {a}" for n, a in list(others.items())[:8]))
    if uses_sorry:
        where = [n for n, a in bad_axioms.items() if "sorryAx" in a]
        msg = f"placeholder (sorry/admit) reaches: {', '.join(where[:8])}"
        (warnings if statement_only else problems).append(msg)
    elif _PLACEHOLDER_TEXT.search(code) and not statement_only:
        warnings.append("the text contains `sorry`/`admit` (outside comments) although no "
                        "declaration depends on it -- remove it")
    complete = compiles and bool(axioms) and not bad_axioms
    passed = compiles and bool(axioms) and not problems
    return {
        "verdict": "PASS" if passed else "FAIL",
        "mode": "statement-only" if statement_only else "theorem+proof",
        "compiles": compiles,
        "complete": complete,
        "problems": problems,
        "warnings": warnings,
        "axioms": axioms,
        "axioms_used": sorted({x for a in axioms.values() for x in a}),
        "declarations": len(_DECL_HEAD.findall(code)),
        "compile_seconds": elapsed,
        "diagnostics": diag if diag else "(no errors or warnings)",
    }


def make_scratch_project(root: Path, lean_project: Path) -> Path:
    """A writable Lean project whose .lake/packages is a symlink into the built one.

    Same construction as the harness's make_project(): lean-lsp-mcp and `lean` need a
    lean-toolchain ancestor, and 6 GB of oleans must not be copied.
    """
    root.mkdir(parents=True, exist_ok=True)
    for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
        src = lean_project / name
        # Copied when missing AND refreshed when the built project's copy has changed: a package
        # added later (cslib) is only on LEAN_PATH once the manifest HERE lists it. These three
        # are project configuration, never the agent's work, so overwriting them is safe.
        if src.is_file() and (not (root / name).is_file()
                              or (root / name).read_bytes() != src.read_bytes()):
            shutil.copy2(src, root / name)
    lib = re.search(r"lean_lib\s+«?([A-Za-z_][\w]*)»?", (root / "lakefile.lean").read_text()
                    if (root / "lakefile.lean").is_file() else "")
    if lib and not (root / f"{lib.group(1)}.lean").exists():
        (root / f"{lib.group(1)}.lean").write_text("-- intentionally empty: files are checked "
                                                   "directly, never through `lake build`.\n")
    (root / ".lake").mkdir(exist_ok=True)
    pk = root / ".lake" / "packages"
    if not pk.exists():
        pk.symlink_to(lean_project / ".lake" / "packages")
    (root / ".lake" / "build" / "lib" / "lean").mkdir(parents=True, exist_ok=True)
    return root


def agent_workspace(cfg: Config) -> Path:
    """The coding agent's own Lean project (the lean-lsp MCP server is rooted here)."""
    return make_scratch_project(cfg.work_root / "lean_workspace", cfg.p("lean_project"))


# =============================================================================
# PROBLEMS
# =============================================================================
def _read_arg(path: str | None, text: str | None) -> str:
    if path:
        return Path(path).expanduser().read_text(errors="replace").strip()
    return (text or "").strip()


def render_problem(a: argparse.Namespace) -> str:
    """Build problem.txt: the <informal_theorem>/<informal_proof> pair the harness was evolved on.

    Optional FIXED Lean context rides inside the theorem block as a "Setting" preamble -- the
    shape the harness's training distribution already has ("often with a Setting preamble that
    defines the notation"). Nothing outside these two blocks is guaranteed to be read.
    """
    if a.problem:
        base = Path(a.problem).expanduser().read_text(errors="replace").strip()
        m_t = re.search(r"<informal_theorem>(.*?)</informal_theorem>", base, re.S)
        m_p = re.search(r"<informal_proof>(.*?)</informal_proof>", base, re.S)
        if not m_t:
            raise AIProverError(f"{a.problem} has no <informal_theorem>...</informal_theorem>")
        thm, prf = m_t.group(1).strip(), (m_p.group(1).strip() if m_p else "")
    else:
        thm = _read_arg(a.theorem, a.theorem_text)
        prf = _read_arg(a.proof, a.proof_text)
        if not thm:
            raise AIProverError("give --problem, or --theorem/--theorem-text")
    if a.statement_only:
        prf = ""
    ctx = _read_arg(a.context, None)
    stmt = _read_arg(a.lean_statement, None)
    extra = []
    if ctx:
        extra.append(
            "Setting (FIXED Lean 4 code). Your Lean file MUST contain the following declarations "
            "copied VERBATIM -- same names, same binders, same definitions, same statements -- "
            "and build on them. Do not rename, restate, weaken or re-prove them differently; "
            "if one of them ends in `sorry`, you may use it as a given fact.\n"
            f"```lean\n{ctx}\n```")
    if stmt:
        extra.append(
            "The Lean 4 statement of this theorem is FIXED. Your file must contain it exactly as "
            "written below (same name, same binders, same hypotheses, same conclusion); replace "
            "only its `sorry` with a real proof that follows the informal proof.\n"
            f"```lean\n{stmt}\n```")
    hint = _read_arg(getattr(a, "hint_file", None), a.hint)
    if hint:
        extra.append(f"Guidance: {hint.strip()}")
    thm_block = thm + ("\n\n" + "\n\n".join(extra) if extra else "")
    return (f"<informal_theorem>\n{thm_block}\n</informal_theorem>\n\n"
            f"<informal_proof>\n{prf}\n</informal_proof>\n")


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", _COMMENT.sub(" ", s)).strip()


def _decl_blocks(lean: str) -> list[tuple[str, str]]:
    """(kind, block) for each top-level declaration in a Lean snippet."""
    code = _COMMENT.sub(" ", lean)
    starts = [(m.start(), m.group(1)) for m in _DECL_HEAD.finditer(code)]
    out = []
    for i, (s, kind) in enumerate(starts):
        e = starts[i + 1][0] if i + 1 < len(starts) else len(code)
        out.append((kind, code[s:e]))
    return out


def preserved(fixed: str, answer: str) -> list[str]:
    """Which fixed declarations are NOT in the answer verbatim (whitespace-normalised).

    Definitions/structures must appear whole. For theorems/lemmas only the STATEMENT must (text
    up to the `:=` that starts the proof), since the point is usually to fill that proof.
    """
    if not fixed.strip():
        return []
    ans = _norm(answer)
    missing = []
    for kind, block in _decl_blocks(fixed):
        if kind in ("theorem", "lemma", "example"):
            head = block.split(":=", 1)[0]
        else:
            head = block
            if re.search(r":=\s*(by\s+)?sorry\s*$", head.strip()):
                head = head.rsplit(":=", 1)[0]
        h = _norm(head)
        if h and h not in ans:
            missing.append(h[:160])
    return missing


# =============================================================================
# LIBRARY SEARCH -- declarations and docstrings of the libraries built into THIS project
# =============================================================================
# `lean_local_search` (lean-lsp-mcp) finds declarations by NAME and already covers every package
# under .lake/packages, cslib included. This is its complement: a text search over declaration
# headers AND docstrings, for when the concept is known but the name is not ("bisimulation
# transitive", "confluence full beta"). No hosted index exists for cslib, so this reads the
# sources of the exact revision this project compiles against -- version-correct by
# construction, which the hosted Mathlib indexes are not.
SEARCH_LIBS = {"cslib": "Cslib", "mathlib": "Mathlib"}          # package dir -> module root
_DECL_RE = re.compile(
    r"^(?P<lead>[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|partial|scoped|local|nonrec)[ \t]+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)[ \t]+"
    r"(?P<name>[^\s:(\[{⟨]+)", re.M)
_SCOPE_RE = re.compile(r"^(namespace|section|end)(?:[ \t]+([\w.']+))?[ \t]*$", re.M)
_DOCSTRING_RE = re.compile(r"/--(.*?)-/", re.S)
_OPEN, _CLOSE = "([{⟨", ")]}⟩"


def _header_end(text: str, start: int, cap: int = 700) -> int:
    """Offset where a declaration's header ends: the first depth-0 `:=` or ` where`, or the
    first following line that starts at column 0 (a new command), or `cap` characters."""
    depth, i, n = 0, start, min(len(text), start + cap)
    while i < n:
        c = text[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return i
        elif depth == 0 and text.startswith(" where", i) and i > start:
            return i
        elif c == "\n" and i + 1 < n and text[i + 1] not in " \t\n":
            return i
        i += 1
    return n


def _index_package(pkg_dir: Path, root: str) -> list[dict]:
    recs: list[dict] = []
    for f in sorted((pkg_dir / root).rglob("*.lean")):
        try:
            text = f.read_text(errors="replace")
        except OSError:
            continue
        module = root + "." + ".".join(f.relative_to(pkg_dir / root).with_suffix("").parts)
        docs = [(m.end(), m.group(1).strip()) for m in _DOCSTRING_RE.finditer(text)]
        scopes: list[tuple[int, str, str | None]] = [(m.start(), m.group(1), m.group(2))
                                                    for m in _SCOPE_RE.finditer(text)]
        si = di = 0
        stack: list[tuple[str, str | None]] = []
        for m in _DECL_RE.finditer(text):
            while si < len(scopes) and scopes[si][0] < m.start():
                _, kw, nm = scopes[si]
                if kw == "end":
                    if stack:
                        stack.pop()
                else:
                    stack.append((kw, nm))
                si += 1
            prefix = ".".join(nm for kw, nm in stack if kw == "namespace" and nm)
            name = m.group("name")
            fqn = f"{prefix}.{name}" if prefix and not name.startswith("_root_.") else name
            doc = ""
            while di < len(docs) and docs[di][0] <= m.start():
                di += 1
            if di > 0 and re.fullmatch(r"(?:\s|@\[[^\]]*\])*", text[docs[di - 1][0]:m.start()]):
                doc = docs[di - 1][1]
            head = re.sub(r"\s+", " ", text[m.start("kind"):_header_end(text, m.start("kind"))])
            recs.append({"module": module, "kind": m.group("kind"), "name": fqn,
                         "header": head[:300], "doc": re.sub(r"\s+", " ", doc)[:300],
                         "line": text.count("\n", 0, m.start()) + 1})
    return recs


def _package_rev(project: Path, pkg: str) -> str:
    try:
        for e in json.loads((project / "lake-manifest.json").read_text()).get("packages", []):
            if e.get("name") == pkg:
                return str(e.get("rev") or "norev")[:12]
    except (OSError, ValueError):
        pass
    return "norev"


def load_search_index(cfg: Config, pkg: str) -> list[dict]:
    """The declaration index of one package, built once per pinned revision and cached."""
    project = cfg.p("lean_project")
    pkg_dir = project / ".lake" / "packages" / pkg
    root = SEARCH_LIBS[pkg]
    if not (pkg_dir / root).is_dir():
        raise AIProverError(f"package {pkg!r} is not in {project} (run ./setup.sh {pkg})")
    cache = cfg.work_root / "search_index" / f"{pkg}-{_package_rev(project, pkg)}.json"
    if cache.is_file():
        try:
            return json.loads(cache.read_text())
        except ValueError:
            pass
    recs = _index_package(pkg_dir, root)
    cache.parent.mkdir(parents=True, exist_ok=True)
    tmp = cache.with_suffix(".tmp")
    tmp.write_text(json.dumps(recs))
    tmp.replace(cache)
    return recs


def search_library(cfg: Config, query: str, libs: list[str], limit: int) -> list[dict]:
    """Terms are matched against the name, the header, the docstring and the module path.

    Full matches (every term somewhere) come first, ranked: all terms in the name, then
    name+header, then anything; shorter names first. When nothing matches every term, the best
    PARTIAL matches are returned instead (most terms matched first) and marked `partial`, so a
    near-synonym ("bisimulation" for a lemma documented as "bisimilarity") still finds the file.
    """
    terms = [t.lower() for t in query.split() if t.strip()]
    if not terms:
        raise AIProverError("empty query")
    full: list[tuple[tuple, dict]] = []
    partial: list[tuple[tuple, dict]] = []
    for pkg in libs:
        for r in load_search_index(cfg, pkg):
            name, head, doc, mod = (r["name"].lower(), r["header"].lower(), r["doc"].lower(),
                                    r["module"].lower())
            matched = [t for t in terms if t in name or t in head or t in doc or t in mod]
            if not matched:
                continue
            if len(matched) == len(terms):
                rank = (0 if all(t in name for t in terms) else
                        1 if all(t in name or t in head for t in terms) else 2)
                full.append(((rank, len(name), name), r))
            elif len(terms) > 1:
                partial.append(((-len(matched), len(name), name),
                                {**r, "partial": f"matched {len(matched)}/{len(terms)} terms: "
                                                 + " ".join(matched)}))
    if full:
        full.sort(key=lambda h: h[0])
        return [r for _, r in full[:limit]]
    partial.sort(key=lambda h: h[0])
    return [r for _, r in partial[:limit]]


def cmd_search(cfg: Config, a: argparse.Namespace) -> int:
    if a.lib in HOSTED_LIBS:
        hits = hosted_search(a.lib, a.query, a.n)
        libs = [a.lib]
    else:
        libs = list(SEARCH_LIBS) if a.lib == "all" else [a.lib]
        hits = search_library(cfg, a.query, libs, a.n)
    if a.json:
        print(json.dumps({"lib": a.lib, "caveat": HOSTED_CAVEAT if a.lib in HOSTED_LIBS else "",
                          "hits": hits}, indent=1, ensure_ascii=False))
        return 0 if hits else 1
    if not hits:
        print(f"no declaration in {'/'.join(libs)} matches any of: {a.query!r}")
        return 1
    if a.lib in HOSTED_LIBS:
        print(f"({a.lib}: {HOSTED_CAVEAT})")
    elif hits[0].get("partial"):
        print(f"(no declaration matches every term of {a.query!r}; best partial matches)")
    for r in hits:
        tag = f"    ({r['partial']})" if r.get("partial") else ""
        where = f"    [import {r['module']}]" if r.get("module") else ""
        print(f"{r['kind']} {r['name']}{where}{tag}".replace("  [", " [", 1) if not r["kind"] else
              f"{r['kind']} {r['name']}{where}{tag}")
        if r.get("header"):
            print(f"    {r['header'][:300]}")
        if r.get("doc"):
            print(f"    -- {r['doc'][:220]}")
    return 0


# =============================================================================
# HOSTED SEARCH -- loogle, leansearch, leandex, for the standalone CLI
# =============================================================================
# Claude Code and Codex reach loogle/leansearch/leanfinder through lean-lsp-mcp (rate-limited,
# cached). Standalone users have no such path, and leandex (semantic search over Lean
# codebases) is not in lean-lsp-mcp at all, so the three are wrapped here. All hosted indexes
# track a newer Mathlib than this project, hence the caveat printed with every answer.
HOSTED_LIBS = ("loogle", "leansearch", "leandex")
HOSTED_CAVEAT = ("hosted index: it tracks a NEWER Mathlib than this project's v4.23.0 and may not know "
                 "cslib. Confirm every name with lean_local_search or `search --lib mathlib|cslib` "
                 "before using it.")


def _http_text(url: str, *, data: bytes | None = None, headers: dict | None = None,
               timeout: float = 20.0, service: str = "") -> str:
    req = urllib.request.Request(url, data=data, headers=headers or {},
                                 method="POST" if data is not None else "GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as e:
        raise AIProverError(f"{service}: HTTP {e.code} -- the service is unavailable or refused the "
                            f"query; try again later or use the local libraries") from None
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        raise AIProverError(f"{service}: {e} -- no outbound network, or the service is down") from None


def hosted_search(lib: str, query: str, limit: int) -> list[dict]:
    q = urllib.parse.quote(query)
    if lib == "loogle":
        raw = json.loads(_http_text(f"https://loogle.lean-lang.org/json?q={q}", service="loogle"))
        if raw.get("error"):
            sug = raw.get("suggestions") or []
            raise AIProverError(f"loogle: {raw['error']}" + (f"; suggestions: {sug[:5]}" if sug else ""))
        return [{"kind": "", "name": h.get("name", ""), "module": h.get("module", ""),
                 "header": h.get("type", ""), "doc": h.get("doc") or ""}
                for h in raw.get("hits", [])[:limit]]
    if lib == "leansearch":
        body = json.dumps({"num_results": str(limit), "query": [query]}).encode()
        raw = json.loads(_http_text("https://leansearch.net/search", data=body, service="leansearch",
                                    headers={"Content-Type": "application/json",
                                             "User-Agent": "aiprover/1.1"}))
        rows = raw[0] if isinstance(raw, list) and raw and raw[0] else []
        out = []
        for r in rows[:limit]:
            r = r.get("result", r) if isinstance(r, dict) else {}
            j = lambda v: ".".join(v) if isinstance(v, list) else str(v or "")
            out.append({"kind": str(r.get("kind") or ""), "name": j(r.get("name")),
                        "module": j(r.get("module_name")), "header": str(r.get("type") or ""),
                        "doc": str(r.get("docstring") or "")})
        return out
    if lib == "leandex":
        headers = {"accept": "text/event-stream", "user-agent": "aiprover/1.1"}
        key = os.environ.get("LEAN_LEANDEX_API_KEY") or os.environ.get("LEANDEX_API_KEY")
        if key:
            headers["Authorization"] = f"Bearer {key}"
        raw = _http_text("https://leandex.projectnumina.ai/api/v1/search"
                         f"?q={q}&limit={limit}&generate_query=False&analyze_result=False",
                         headers=headers, timeout=30, service="leandex")
        data_lines = [l[5:].strip() for l in raw.splitlines() if l.startswith("data:")]
        payload = data_lines[-1] if data_lines else raw.strip()
        try:
            parsed = json.loads(payload)
        except ValueError:
            raise AIProverError(f"leandex: unparseable response: {payload[:200]}") from None
        results = ((parsed.get("data") or {}).get("search_results")
                   or parsed.get("search_results") or [])
        out = []
        for r in results[:limit]:
            d = r.get("primary_declaration") or {}
            pick = lambda *ks: next((str(x[k]) for x in (d, r) for k in ks if x.get(k)), "")
            out.append({"kind": "", "name": pick("lean_name", "name"),
                        "module": pick("module_name", "source_file"),
                        "header": pick("statement_text", "display_statement_text", "type"),
                        "doc": pick("docstring", "informal_description")})
        return out
    raise AIProverError(f"unknown hosted library {lib!r}")


# =============================================================================
# EXTRACT -- the goal at a `sorry` becomes a standalone lemma, with Lean writing the binders
# =============================================================================
# The escalation ladder's second rung: a stuck step is isolated as its own lemma and delegated
# alone. Transcribing the goal state into binders by hand is where names get lost and
# universes go wrong, so Mathlib's `extract_goal` does it: it prints `theorem extracted ...
# := sorry` with the exact local context. We insert it at the `sorry`, compile once, and
# hand the lemma back renamed and ready to paste.
_EXTRACTED_RE = re.compile(r"^theorem\s+(?P<name>[^\s.{]+(?:\.[^\s.{]+)*)(?P<univ>\.\{[^}]*\})?"
                           r"(?P<rest>.*?):=\s*sorry\s*$", re.M | re.S)


def extract_lemma(cfg: Config, text: str, line: int, col: int | None = None,
                  name: str | None = None) -> dict:
    lines = text.split("\n")
    if not 1 <= line <= len(lines):
        raise AIProverError(f"--line {line} is outside the file (1..{len(lines)})")
    src = lines[line - 1]
    idx = src.find("sorry", (col - 1) if col else 0)
    if idx < 0:
        raise AIProverError(f"no `sorry` on line {line}: point --line at the sorry that stands for the stuck step")
    before, after = src[:idx].rstrip(), src[idx + len("sorry"):]
    if before == "" or re.search(r"(\bby|·|=>|<;>|;)$", before):
        repl = "extract_goal; sorry"                 # tactic position
    elif before.endswith(":="):
        repl = "by extract_goal; sorry"              # term position right after :=
    else:
        repl = "(by extract_goal; sorry)"            # a term argument
    lines[line - 1] = src[:idx] + repl + after
    # the enclosing declaration, for the default name
    head = None
    for m in _DECL_RE.finditer(text):
        if text.count("\n", 0, m.start()) + 1 <= line:
            head = m.group("name")
    base = re.sub(r"[^A-Za-z0-9_]+", "_", head or "goal").strip("_") or "goal"
    new_name = name or f"{base}_step_L{line}"
    g = grader(cfg)
    work = cfg.work_root / "checks"
    work.mkdir(parents=True, exist_ok=True)
    ok, out = g.compile_text("\n".join(lines), work=work, project=cfg.p("lean_project"))
    m = _EXTRACTED_RE.search(out)
    if not m:
        errs = [tx.splitlines()[0] for ln, sev, tx in _messages(out) if sev == "error"]
        raise AIProverError("extract_goal produced no lemma. " + (
            f"first compiler error: {errs[0][:200]}" if errs else f"compiler output: {out[:300]}"))
    rest = re.sub(r"\[inst\w*\s*:\s*", "[", m.group("rest"))      # [inst : Group G] -> [Group G]
    rest = re.sub(r"\s+", " ", rest).strip()
    lemma = f"lemma {new_name}{m.group('univ') or ''} {rest} := by\n  sorry\n"
    return {"theorem": head, "line": line, "name": new_name, "lemma": lemma,
            "extracted_as": m.group("name")}


def cmd_extract(cfg: Config, a: argparse.Namespace) -> int:
    text = Path(a.file).expanduser().read_text(errors="replace")
    r = extract_lemma(cfg, text, a.line, a.col, a.name)
    if a.json:
        print(json.dumps(r, indent=1, ensure_ascii=False))
        return 0
    print(f"extracted from {Path(a.file).name}:{r['line']}"
          + (f" (inside `{r['theorem']}`)" if r["theorem"] else "") + ":\n")
    print(r["lemma"])
    print(f"next: paste it ABOVE `{r['theorem'] or 'the theorem'}`, replace the sorry at line {r['line']} "
          f"with `exact {r['name']} ..` (or `apply {r['name']}`), run `check --statement-only` and "
          f"`probe` on the file, then submit the lemma alone: --lean-statement <it>, --context <the "
          f"frozen definitions it mentions>, --theorem-text/--proof-text <that step of P>.")
    return 0


# =============================================================================
# INFORMAL HELPERS -- three moves that need an LLM, answered by whichever LLM this mode has
# =============================================================================
# The rigor pass (make the informal proof explicit), the blind back-translation of a Lean file
# and a free-form question. Backends:
#   claude    `claude -p` -- a FRESH headless Claude Code process on the user's own Claude
#             subscription/credentials. Default inside a Claude Code session.
#   codex     `codex exec` -- likewise on the user's Codex subscription. Default inside Codex.
#   aiprover  the AIProver model server (OpenAI-compatible chat). Default standalone. That
#             model is Lean-specialised and weaker at informal mathematics; read its drafts.
# A fresh process is a feature for `backtranslate`: it has not seen the informal theorem, so
# its reading of the Lean cannot be anchored by it (the judge protocol's point).
# Nothing here feeds an answer anywhere automatically; the commands PRINT for a reader.
HELPER_TIMEOUT = 900          # one reasoning_effort=high answer can take minutes
HELPER_BACKENDS = ("auto", "aiprover", "claude", "codex")


def _hosting_agent() -> str | None:
    """`codex` or `claude` if this process runs under one of them, else None.

    Decided from the process ancestry (Linux /proc): the NEAREST ancestor that is a `codex` or
    `claude` executable names the session we are inside of. Environment markers alone cannot,
    because a Codex session started from a Claude Code shell inherits Claude's variables
    (measured: both sets present, Claude's would win wrongly). Falls back to the markers where
    /proc is unavailable.
    """
    pid = os.getpid()
    for _ in range(40):
        try:
            with open(f"/proc/{pid}/stat") as f:
                ppid = int(f.read().rsplit(")", 1)[1].split()[1])
            if ppid <= 1:
                break
            with open(f"/proc/{ppid}/cmdline", "rb") as f:
                argv0 = f.read().split(b"\0", 1)[0].decode(errors="replace")
        except (OSError, ValueError, IndexError):
            break
        base = os.path.basename(argv0)
        if base == "codex":
            return "codex"
        if base == "claude" or "/claude/versions/" in argv0 or "claude-code" in argv0:
            return "claude"
        pid = ppid
    if os.environ.get("CODEX_THREAD_ID") or os.environ.get("CODEX_SANDBOX"):
        return "codex"
    if os.environ.get("CLAUDECODE") or os.environ.get("CLAUDE_CODE_ENTRYPOINT"):
        return "claude"
    return None


def helper_backend(cfg: Config, requested: str | None = None) -> str:
    """Which LLM answers: the flag, else [helpers].backend, else the session we are inside of."""
    choice = (requested or str(cfg.helpers.get("backend", "auto")) or "auto").strip().lower()
    if choice not in HELPER_BACKENDS:
        raise AIProverError(f"unknown helper backend {choice!r}; one of {HELPER_BACKENDS}")
    if choice != "auto":
        return choice
    return _hosting_agent() or "aiprover"


def _helper_timeout(cfg: Config) -> int:
    return int(cfg.helpers.get("timeout_sec", HELPER_TIMEOUT))


def _claude_answer(cfg: Config, prompt: str) -> str:
    exe = shutil.which("claude")
    if not exe:
        raise AIProverError("backend claude: `claude` CLI not on PATH (use --backend aiprover, or install Claude Code)")
    # The prompt goes in over STDIN: `--disallowedTools` takes a list of names, so a positional
    # prompt after it would be read as more tool names (measured: "Permission deny rule 'with'
    # matches no known tool"), and stdin also has no ARG_MAX limit for a long Lean file.
    cmd = [exe, "-p", "--output-format", "text", "--max-turns", "2", "--permission-mode", "default",
           "--disallowedTools", "Bash,Edit,Write,NotebookEdit,WebFetch,WebSearch,Task,Agent"]
    model = str(cfg.helpers.get("claude_model", "") or "").strip()
    if model:
        cmd += ["--model", model]
    env = {k: v for k, v in os.environ.items() if k not in ("CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT")}
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=_helper_timeout(cfg),
                           input="Answer directly in this reply; use no tools.\n\n" + prompt,
                           cwd=str(cfg.work_root), env=env)
    except subprocess.TimeoutExpired:
        raise AIProverError(f"backend claude: no answer within {_helper_timeout(cfg)}s") from None
    if r.returncode != 0 or not r.stdout.strip():
        raise AIProverError(f"backend claude: rc={r.returncode}: {(r.stderr or r.stdout)[-400:].strip()}")
    return r.stdout.strip()


def _codex_answer(cfg: Config, prompt: str) -> str:
    exe = shutil.which("codex") or next(iter(sorted(Path.home().glob(
        ".vscode-server/extensions/openai.chatgpt-*/bin/linux-*/codex"), reverse=True)), None)
    if not exe:
        raise AIProverError("backend codex: `codex` CLI not found (use --backend aiprover, or install Codex)")
    work = cfg.work_root / "helpers"
    work.mkdir(parents=True, exist_ok=True)
    out = work / f"codex_{os.getpid()}_{int(time.time())}.txt"
    sandbox = str(cfg.helpers.get("codex_sandbox", "read-only") or "read-only")
    cmd = [str(exe), "exec", "--skip-git-repo-check", "--sandbox", sandbox, "-C", str(work),
           "-o", str(out), "Answer directly in this reply; run no commands and edit no files.\n\n" + prompt]
    try:   # `codex exec` blocks on an open stdin, hence DEVNULL
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=_helper_timeout(cfg),
                           stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        raise AIProverError(f"backend codex: no answer within {_helper_timeout(cfg)}s") from None
    ans = out.read_text(errors="replace").strip() if out.is_file() else ""
    out.unlink(missing_ok=True)
    if r.returncode != 0 or not ans:
        raise AIProverError(f"backend codex: rc={r.returncode}: {(r.stderr or r.stdout)[-400:].strip()}")
    return ans


def llm_answer(cfg: Config, prompt: str, backend: str, *, max_tokens: int = 6000) -> str:
    if backend == "claude":
        return _claude_answer(cfg, prompt)
    if backend == "codex":
        return _codex_answer(cfg, prompt)
    return chat(cfg, prompt, max_tokens=max_tokens)

EXPAND_WRITER = """You prepare an informal proof for a formalization system that follows the text literally: every \
gap in the text becomes a gap in the formal proof.

Rewrite the PROOF below as numbered atomic steps. Rules:
- Keep the proof's METHOD and its intermediate lemmas exactly as they are (same induction, same case \
split, same contradiction, same auxiliary claims, in the same order). Expand; never replace.
- Every step names what justifies it: a hypothesis, an earlier step, a standard fact stated precisely, \
or an induction (say on which variable, and write the induction hypothesis out).
- List every case of a case split and both directions of an equivalence.
- Replace "clearly", "obviously", "similarly", "the usual argument", "it follows" by the actual steps.
- Pin what the text leaves implicit: the type of every variable (natural number, integer, real, \
element of which structure) and the meaning of every relation or notation used.
- Do not change the THEOREM, do not add assumptions, do not prove something stronger or weaker.
Output ONLY the rewritten proof, between <informal_proof> and </informal_proof> tags.

THEOREM:
{theorem}

PROOF:
{proof}
"""
EXPAND_CRITIC = """Compare EXPANDED, a rewritten proof, against ORIGINAL, the proof it was rewritten from, both of THEOREM.
Check, concretely:
1. Is the METHOD preserved (same induction / case split / contradiction / construction)?
2. Is every intermediate claim of ORIGINAL present in EXPANDED and used where ORIGINAL uses it?
3. Does EXPANDED introduce any assumption, or prove something weaker or stronger than THEOREM?
4. Are there remaining gaps: a "clearly", a missing case, an unstated induction hypothesis, a step \
whose justification is not named?
Answer with one line `VERDICT: OK` or `VERDICT: ISSUES`, then a numbered list of concrete issues \
(empty if OK). No other text.

THEOREM:
{theorem}

ORIGINAL:
{proof}

EXPANDED:
{expanded}
"""
EXPAND_REFINE = """Revise EXPANDED so that every listed ISSUE is fixed, changing nothing else. Keep the method and \
the intermediate claims of ORIGINAL. Output ONLY the revised proof between <informal_proof> and \
</informal_proof> tags.

THEOREM:
{theorem}

ORIGINAL:
{proof}

EXPANDED:
{expanded}

ISSUES:
{issues}
"""
BACKTRANSLATE = """Below is a Lean 4 file. For EVERY theorem, lemma and definition in it, say in plain English exactly \
what it asserts or defines. Translate what the Lean says, not what it was probably meant to say:
- every hypothesis, including typeclass assumptions in square brackets and implicit arguments;
- the quantifiers, in their order and scope (for all / there exists / exists unique);
- the number type and its conventions (natural-number subtraction truncates at 0, natural and \
integer division round down, division by zero is 0);
- what each local definition means after unfolding it, and where it is used;
- the exact conclusion (strict or non-strict inequality, equality of what, implication or \
equivalence).
One paragraph per declaration, headed by its name. No commentary on correctness or intent.

```lean
{lean}
```
"""


def chat(cfg: Config, prompt: str, *, max_tokens: int = 6000, temperature: float = 0.3,
         system: str | None = None) -> str:
    """One answer from the AIProver endpoint (OpenAI-compatible), with the model thinking."""
    api, models = ensure_endpoint(cfg)
    messages = ([{"role": "system", "content": system}] if system else []) + \
               [{"role": "user", "content": prompt}]
    r = _http_json(api + "/chat/completions", key=cfg.api_key, timeout=HELPER_TIMEOUT, data={
        "model": served_model(cfg, models), "max_tokens": max_tokens, "temperature": temperature,
        "reasoning_effort": "high", "messages": messages})
    try:
        return (r["choices"][0]["message"].get("content") or "").strip()
    except (KeyError, IndexError, TypeError):
        raise AIProverError(f"unexpected answer from the model endpoint: {str(r)[:300]}") from None


def _problem_parts(a: argparse.Namespace) -> tuple[str, str]:
    text = render_problem(a)
    thm = re.search(r"<informal_theorem>(.*?)</informal_theorem>", text, re.S).group(1).strip()
    prf = re.search(r"<informal_proof>(.*?)</informal_proof>", text, re.S).group(1).strip()
    return thm, prf


def _proof_block(answer: str) -> str:
    m = re.search(r"<informal_proof>(.*?)</informal_proof>", answer, re.S)
    return (m.group(1) if m else answer).strip()


def cmd_expand(cfg: Config, a: argparse.Namespace) -> int:
    thm, prf = _problem_parts(a)
    if not prf:
        raise AIProverError("the proof block is empty: nothing to expand (statement-only problem)")
    be = helper_backend(cfg, a.backend)
    if a.dry_run:
        print(f"(backend would be: {be})")
        print(EXPAND_WRITER.format(theorem=thm, proof=prf))
        return 0
    print(f"(backend: {be})", file=sys.stderr)
    expanded = _proof_block(llm_answer(cfg, EXPAND_WRITER.format(theorem=thm, proof=prf), be))
    verdict = "(not checked)"
    for rnd in range(max(0, a.rounds - 1)):
        crit = llm_answer(cfg, EXPAND_CRITIC.format(theorem=thm, proof=prf, expanded=expanded), be,
                          max_tokens=2000)
        verdict = next((l.strip() for l in crit.splitlines() if "VERDICT" in l.upper()),
                       crit.splitlines()[0].strip() if crit else "(no answer)")
        if "ISSUES" not in verdict.upper():
            break
        print(f"[round {rnd + 1}] critic: {' '.join(crit.split())[:400]}", file=sys.stderr)
        expanded = _proof_block(llm_answer(cfg, EXPAND_REFINE.format(
            theorem=thm, proof=prf, expanded=expanded, issues=crit), be))
    out = (f"<informal_theorem>\n{thm}\n</informal_theorem>\n\n"
           f"<informal_proof>\n{expanded}\n</informal_proof>\n")
    if a.out:
        Path(a.out).expanduser().write_text(out)
        print(f"wrote {a.out}  (critic's last verdict: {verdict}). Read the expansion against the "
              f"original before submitting: the method and the lemmas must be the original's.",
              file=sys.stderr)
    else:
        sys.stdout.write(out)
        sys.stdout.flush()
        print(f"(critic's last verdict: {verdict})", file=sys.stderr)
    return 0


def cmd_backtranslate(cfg: Config, a: argparse.Namespace) -> int:
    lean = Path(a.file).expanduser().read_text(errors="replace")
    prompt = BACKTRANSLATE.format(lean=lean)
    be = helper_backend(cfg, a.backend)
    if a.dry_run:
        print(f"(backend would be: {be})")
        print(prompt)
        return 0
    print(f"(backend: {be})", file=sys.stderr)
    print(llm_answer(cfg, prompt, be))
    sys.stdout.flush()
    print("\nCompare each paragraph with the informal theorem clause by clause (SKILL.md, judge "
          "protocol (c)). This is the model's reading of the Lean, not a verdict.", file=sys.stderr)
    return 0


def cmd_ask(cfg: Config, a: argparse.Namespace) -> int:
    q = a.question
    if a.file:
        q += "\n\nContext file `" + Path(a.file).name + "`:\n```lean\n" + \
             Path(a.file).expanduser().read_text(errors="replace") + "\n```\n"
    be = helper_backend(cfg, a.backend)
    if a.dry_run:
        print(f"(backend would be: {be})")
        print(q)
        return 0
    print(f"(backend: {be})", file=sys.stderr)
    print(llm_answer(cfg, q, be, max_tokens=a.max_tokens))
    return 0


# =============================================================================
# STATEMENT PROBE -- is a candidate statement FALSE as written, or closed by automation alone?
# =============================================================================
# The dominant AIProver failure is a file that compiles and states the WRONG theorem (173 of
# 509 training samples). Two mechanical signals catch a share of those before the judge reads:
#   * a COUNTEREXAMPLE: the informal theorem is true, so a formal statement with a dropped
#     hypothesis, a narrowed quantifier or the wrong numeric type (ℕ subtraction, floor
#     division) is often simply false, and `plausible` (Mathlib's random tester) finds a witness;
#   * CLOSED BY AUTOMATION: `simp`/`decide`/`omega`/... alone proving a research-level statement
#     is the smell of a narrowed or specialised one (the judge protocol's "not vacuous" clause).
# Both are advisory. "No counterexample" proves nothing; an abstract statement is "untestable".
PROBE_CLOSERS = ("decide", "simp", "omega", "norm_num", "aesop", "grind")
PROBE_HEARTBEATS = 20000


def _probe_source(text: str) -> tuple[str, list[dict]]:
    """Rewrite every theorem/lemma proof as `by plausible` and append one `example` per closer.

    Returns (source, targets). A target records the generated line ranges so compiler messages
    can be attributed. Declarations without a depth-0 `:=` (pattern-matching proofs) are kept
    as they are and reported as not probed.
    """
    code = _COMMENT.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)   # keep line count
    heads = [(m.start(), m) for m in _DECL_RE.finditer(code)]
    out, targets, pos = [], [], 0
    for i, (st, m) in enumerate(heads):
        if m.group("kind") not in ("theorem", "lemma"):
            continue
        blk_end = heads[i + 1][0] if i + 1 < len(heads) else len(code)
        colon = _header_end(code, m.end("name"), cap=blk_end - m.end("name"))
        if not code.startswith(":=", colon):
            targets.append({"name": m.group("name"), "skipped": "no `:=` found (pattern-matching proof?)"})
            continue
        # the proof ends at the first later line that starts at column 0 (a new command)
        nl = code.find("\n", colon)
        pend = blk_end
        while nl != -1 and nl + 1 < blk_end:
            if code[nl + 1] not in " \t\n":
                pend = nl + 1
                break
            nl = code.find("\n", nl + 1)
        sig = code[m.end("name"):colon]
        base_lines = "".join(out).count("\n")               # generated lines emitted so far
        thm_gen_line = base_lines + code.count("\n", pos, m.start()) + 1
        gen_start_line = base_lines + code.count("\n", pos, colon) + 1
        out.append(code[pos:colon])
        piece = ":= by plausible\n"
        closer_lines = {}
        for c in PROBE_CLOSERS:
            closer_lines[c] = gen_start_line + piece.count("\n")
            piece += f"set_option maxHeartbeats {PROBE_HEARTBEATS} in\nexample{sig} := by {c}\n"
        out.append(piece)
        targets.append({"name": m.group("name"), "thm_line": thm_gen_line, "gen_line": gen_start_line,
                        "closers": closer_lines, "end_line": gen_start_line + piece.count("\n")})
        pos = pend
    out.append(code[pos:])
    return "".join(out), targets


_MSG_RE = re.compile(r"^(\S+?\.lean):(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: ?", re.M)


def _messages(out: str) -> list[tuple[int, str, str]]:
    """(line, severity, text) for every compiler message, multi-line bodies included."""
    ms = list(_MSG_RE.finditer(out))
    res = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(out)
        res.append((int(m.group(2)), m.group(4), out[m.end():end].strip()))
    return res


def probe_file(cfg: Config, text: str) -> dict:
    src, targets = _probe_source(text)
    g = grader(cfg)
    work = cfg.work_root / "checks"
    work.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    ok, out = g.compile_text(src, work=work, project=cfg.p("lean_project"))
    msgs = _messages(out)
    results = []
    for t in targets:
        if "skipped" in t:
            results.append({"name": t["name"], "status": "not probed", "detail": t["skipped"]})
            continue
        lo, hi = t["gen_line"], t["end_line"]
        first_closer = min(t["closers"].values())
        mine = [(ln, sev, tx) for ln, sev, tx in msgs if t["thm_line"] <= ln < first_closer]
        joined = "\n".join(tx for _, _, tx in mine)
        if "Found a counter-example!" in joined:
            body = joined.split("Found a counter-example!", 1)[1].split("-----", 1)[0]
            status, detail = "COUNTEREXAMPLE", " ; ".join(l.strip() for l in body.strip().splitlines() if l.strip())
        elif "Failed to create a `testable` instance" in joined:
            status, detail = "untestable", "no sampling/decidability instances for this statement"
        elif any(sev == "error" for _, sev, _ in mine):
            status, detail = "does not elaborate", next(tx.splitlines()[0] for _, sev, tx in mine if sev == "error")[:160]
        elif "declaration uses 'sorry'" in joined:
            # `plausible` prints "Unable to find a counter-example" WITHOUT a position and then
            # admits the goal, so the positioned trace of a passed test is exactly this warning.
            status, detail = "no counterexample found", "random testing passed; this proves nothing"
        else:
            status, detail = "inconclusive", (joined.splitlines()[0][:160] if joined else "no message")
        closed = []
        for c, ln in t["closers"].items():
            nxt = min([v for v in t["closers"].values() if v > ln] + [hi])
            if not any(sev == "error" and ln <= l < nxt for l, sev, _ in msgs):
                closed.append(c)
        results.append({"name": t["name"], "status": status, "detail": detail, "closed_by": closed})
    return {"results": results, "compile_seconds": round(time.time() - t0, 1),
            "counterexamples": sum(r["status"] == "COUNTEREXAMPLE" for r in results),
            "raw": out if not targets else ""}


def cmd_probe(cfg: Config, a: argparse.Namespace) -> int:
    text = Path(a.file).expanduser().read_text(errors="replace")
    r = probe_file(cfg, text)
    if a.json:
        print(json.dumps(r, indent=1, ensure_ascii=False))
        return 1 if r["counterexamples"] else 0
    if not r["results"]:
        print("probe: no theorem/lemma found in the file")
        if r["raw"]:
            print(r["raw"][:600])
        return 2
    print(f"probe  {Path(a.file).name}  ({len(r['results'])} statement(s), {r['compile_seconds']}s)")
    for x in r["results"]:
        line = f"  {x['name']}: {x['status']}"
        if x["detail"]:
            line += f"  --  {x['detail']}"
        print(line)
        if x.get("closed_by"):
            print(f"      closed by automation alone: {', '.join(x['closed_by'])}  "
                  f"-> is the statement narrowed, specialised or trivial? (judge clause 'not vacuous')")
    if r["counterexamples"]:
        print("  A COUNTEREXAMPLE means the statement is FALSE as written. Since the informal theorem is "
              "true, the formalization dropped a hypothesis, narrowed or widened a quantifier, or "
              "chose the wrong type/cast. Fix the statement before any proof work.")
    return 1 if r["counterexamples"] else 0


# =============================================================================
# JOBS
# =============================================================================
def _job_id(name: str | None) -> str:
    stamp = time.strftime("%Y%m%d-%H%M%S")
    tail = "".join(random.choices(string.ascii_lowercase + string.digits, k=4))
    safe = re.sub(r"[^A-Za-z0-9_-]+", "-", name or "").strip("-")[:40]
    return f"{stamp}-{tail}" + (f"-{safe}" if safe else "")


def _job_dir(cfg: Config, job: str) -> Path:
    d = cfg.jobs / job
    if d.is_dir():
        return d
    hits = sorted(p for p in cfg.jobs.glob(f"*{job}*") if p.is_dir())
    if len(hits) == 1:
        return hits[0]
    raise AIProverError(f"no unique job matches {job!r} ({len(hits)} matches) under {cfg.jobs}")


def _read_json(p: Path) -> dict:
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return {}


def _write_json(p: Path, d: dict) -> None:
    tmp = p.with_suffix(p.suffix + ".tmp")
    tmp.write_text(json.dumps(d, indent=1))
    tmp.replace(p)


def _pid_alive(pid: int | None) -> bool:
    if not pid:
        return False
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def cmd_submit(cfg: Config, a: argparse.Namespace) -> int:
    problem = render_problem(a)
    samples = max(1, int(a.samples))
    job = _job_id(a.name)
    d = cfg.jobs / job
    d.mkdir(parents=True)
    (d / "problem.txt").write_text(problem)
    ctx = _read_arg(a.context, None)
    stmt = _read_arg(a.lean_statement, None)
    if ctx:
        (d / "context.lean").write_text(ctx + "\n")
    if stmt:
        (d / "statement.lean").write_text(stmt + "\n")
    req = {"job": job, "name": a.name, "samples": samples, "created": time.time(),
           "statement_only": bool(a.statement_only) or not re.sub(
               r"\s+", "", re.search(r"<informal_proof>(.*?)</informal_proof>", problem,
                                     re.S).group(1)),
           "timeout_sec": int(a.timeout or cfg.timeout),
           "max_turns": int(a.max_turns or cfg.max_turns)}
    # Who submitted (2026-09-22): lets step1 runs attribute jobs to an agent sample. cwd is the
    # per-sample directory for both Claude Code (~/.aiprover/agent_runs/claude-*) and Codex.
    try:
        _pp = os.getppid()
        _pcmd = Path(f"/proc/{_pp}/cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")[:200] if Path(f"/proc/{_pp}/cmdline").exists() else ""
        req["submitter"] = {"cwd": os.getcwd(), "ppid": _pp, "parent_cmd": _pcmd,
                            "env": {k: v for k, v in os.environ.items()
                                    if k in ("CODEX_HOME", "USAGE_WORKER", "CLAUDE_CWD", "CLAUDE_CODE_ENTRYPOINT", "CODEX_THREAD_ID", "CLAUDE_SESSION_ID")}}
    except Exception:
        pass
    _write_json(d / "request.json", req)
    for i in range(samples):
        s = d / f"s{i}"
        s.mkdir()
        (s / "problem.txt").write_text(problem)
    log = open(d / "worker.log", "ab")
    p = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "_worker", str(d)],
                         stdin=subprocess.DEVNULL, stdout=log, stderr=log,
                         start_new_session=True, close_fds=True,
                         env={**os.environ, "AIPROVER_CONFIG": str(cfg.path)})
    _write_json(d / "worker.json", {"pid": p.pid, "started": time.time()})
    print(job)
    if not a.quiet:
        print(f"  {samples} sample(s) submitted; dir {d}", file=sys.stderr)
        print(f"  next: aiprover wait {job} --timeout 540   then   aiprover result {job}",
              file=sys.stderr)
    return 0


def _acquire_slot(cfg: Config, stop: threading.Event):
    """A global semaphore over every aiprover process on this machine: N flock'd files."""
    sd = cfg.work_root / ".slots"
    sd.mkdir(exist_ok=True)
    while not stop.is_set():
        for i in range(cfg.max_parallel):
            f = open(sd / f"slot{i}.lock", "w")
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return f
            except OSError:
                f.close()
        time.sleep(3 + random.random() * 3)
    return None


def harness_env(cfg: Config, ws: Path, api: str, model: str) -> dict:
    """The environment the evolution run gave the harness (tools/apptainer-local), on this host."""
    env = dict(os.environ)
    elan = cfg.p("elan_home")
    extra_path = [str(elan / "bin")]
    if cfg.rg_dir():
        extra_path.append(cfg.rg_dir())
    env.update({
        "AGENT_WORK": str(ws),
        "AGENT_MATHLIB": str(cfg.p("lean_project")),
        "AGENT_ELAN": str(elan),
        "AGENT_GRADER": str(GRADER),
        "AGENT_API_BASE": api,
        "AGENT_MODEL": model,
        "PYTHONPATH": str(cfg.site_packages("vibe_venv")),
        "LEAN_MCP_SITE": str(cfg.site_packages("mcp_venv")),
        "LEAN_MCP_PY": str(cfg.venv_python("mcp_venv")),
        "VIBE_SITE": str(cfg.site_packages("vibe_venv")),
        "VIBE_LOCAL_API_KEY": cfg.api_key,
        "PATH": ":".join(extra_path + [env.get("PATH", "/usr/bin:/bin")]),
        # Only the harness's container_cmd() reads these, and the `agent` mode never calls it.
        # Set anyway so NO code path in the harness can resolve a cluster-specific default.
        "AGENT_SIF": "",
        "AGENT_MATHLIB_HOST": str(cfg.p("lean_project")),
        "AGENT_ELAN_HOST": str(elan),
        "AGENT_VIBE_HOST": str(cfg.p("vibe_venv")),
        "AGENT_MCP_HOST": str(cfg.p("mcp_venv")),
    })
    return env


# The champion was measured with max_turns 100, a 5400 s kill and fences at 3700 s (search and
# shell withdrawn, finalize) and 2900 s (soft notice). A turn is about one tool call, so a bigger
# turn budget needs a proportionally bigger clock or the time fences fire first and the extra
# turns never happen. The fences therefore scale with THIS job's timeout at the champion's
# ratios; at timeout_sec 5400 they reproduce the champion's numbers exactly. AGENT_MAX_TURNS keeps
# the prompt's "you have about N turns" in step with the --max-turns the loop enforces.
CHAMPION_KILL, CHAMPION_HARD, CHAMPION_SOFT = 5400, 3700, 2900


def budget_env(req: dict) -> dict[str, str]:
    kill = max(60, int(req.get("timeout_sec") or CHAMPION_KILL))
    hard = int(kill * CHAMPION_HARD / CHAMPION_KILL)
    soft = int(kill * CHAMPION_SOFT / CHAMPION_KILL)
    return {"AGENT_MAX_TURNS": str(int(req.get("max_turns") or 100)),
            "AGENT_RESERVE_HARD": str(hard), "AGENT_RESERVE_SOFT": str(soft),
            "AGENT_FINALIZE_DEADLINE": str(hard)}


# Run INSIDE the harness's own interpreter and environment: import it exactly as a rollout does
# and list every absolute path it resolved, so "no hardcoded cluster path survives" is measured.
_PATH_AUDIT = r"""
import importlib.util, json, os, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location("h", sys.argv[1]); h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
names = ["WORK","MATHLIB","ELAN","VIBE_SITE","MCP_SITE","MCP_PY","GRADER_PATH","HOST_MATHLIB",
         "HOST_ELAN","HOST_VIBE","HOST_MCP","ANSWER"]
out = {n: str(getattr(h, n)) for n in names}
g = h._grader()
out.update({"grader.WORK": str(g.WORK), "grader.MATHLIB": str(g.MATHLIB), "grader.ELAN": str(g.ELAN),
            "lean_bin": g.lean_bin(g.MATHLIB), "grader_file": g.__file__})
print(json.dumps(out))
"""


def audit_harness_paths(cfg: Config, ws: Path) -> tuple[bool, str]:
    env = harness_env(cfg, ws, cfg.api_base, "audit")
    r = subprocess.run([str(cfg.venv_python("vibe_venv")), "-c", _PATH_AUDIT, str(HARNESS)],
                       cwd=str(ws), env=env, capture_output=True, text=True, timeout=120)
    if r.returncode != 0:
        return False, (r.stdout + r.stderr)[-400:]
    got = json.loads(r.stdout.strip().splitlines()[-1])
    bad = {}
    for k, v in got.items():
        if k == "ANSWER":                       # created by the run itself, under WORK
            if not v.startswith(str(ws)):
                bad[k] = v
            continue
        if v.startswith("/") and not Path(v).exists():
            bad[k] = v
        if any(t in v for t in ("/work2/", "/scratch/", "11428")) and not Path(v).exists():
            bad[k] = v
    return not bad, (f"{len(got)} resolved paths, all local and present" if not bad
                     else f"UNRESOLVED: {bad}")


def _classify(chk: dict, statement_only: bool, answer: str) -> str:
    if not answer.strip():
        return "empty"
    if not chk["compiles"]:
        return "error"
    if chk["verdict"] == "PASS":
        return "verified"
    if any("placeholder" in p for p in chk["problems"]):
        return "sorry"
    return "rejected"


RANK = {"verified": 0, "sorry": 1, "rejected": 2, "error": 3, "empty": 4, "infra": 5,
        "cancelled": 6}


def run_sample(cfg: Config, jobdir: Path, i: int, req: dict, stop: threading.Event) -> None:
    ws = jobdir / f"s{i}"
    st_path = ws / "state.json"
    _write_json(st_path, {"state": "queued"})
    slot = _acquire_slot(cfg, stop)
    if slot is None:
        _write_json(st_path, {"state": "done", "status": "cancelled"})
        return
    try:
        attempts = 0
        while True:
            attempts += 1
            try:
                api, models = ensure_endpoint(cfg)
                model = served_model(cfg, models)
            except AIProverError as e:
                _write_json(st_path, {"state": "done", "status": "infra", "error": str(e)})
                return
            for stale in ("result.json", "solution.lean", ".hevo_state.json", ".hevo_ticks"):
                (ws / stale).unlink(missing_ok=True)
            shutil.rmtree(ws / "proj", ignore_errors=True)
            env = harness_env(cfg, ws, api, model)
            env.update(budget_env(req))
            cmd = [str(cfg.venv_python("vibe_venv")), str(HARNESS), "agent",
                   "--api-base", api, "--max-turns", str(req["max_turns"])]
            t0 = time.time()
            with open(ws / "agent.log", "ab") as log:
                p = subprocess.Popen(cmd, cwd=str(ws), env=env, stdin=subprocess.DEVNULL,
                                     stdout=log, stderr=log, start_new_session=True)
                _write_json(st_path, {"state": "running", "pid": p.pid, "started": t0,
                                      "attempt": attempts, "model": model})
                timed_out = False
                while p.poll() is None:
                    if stop.is_set():
                        break
                    if time.time() - t0 > req["timeout_sec"]:
                        timed_out = True
                        break
                    time.sleep(5)
                # The whole process GROUP: the harness leaves an LSP, lake and lean behind.
                for sig in (signal.SIGTERM, signal.SIGKILL):
                    try:
                        os.killpg(p.pid, sig)
                    except ProcessLookupError:
                        break
                    time.sleep(3)
                p.wait()
            if stop.is_set():
                _write_json(st_path, {"state": "done", "status": "cancelled"})
                return
            res = _read_json(ws / "result.json")
            g = grader(cfg)
            infra = res.get("infra_failure") or g.infra_failure(res.get("agent_error"), "")
            answer_path = ws / "proj" / "Work.lean"
            answer = answer_path.read_text(errors="replace") if answer_path.is_file() else ""
            if infra and not answer.strip() and attempts < 2:
                (ws / "agent.log").open("a").write(f"\n[aiprover] infra failure, retrying: "
                                                   f"{infra}\n")
                continue
            chk = check_lean(cfg, answer, statement_only=req["statement_only"],
                             work=ws, label=f"s{i}.lean") if answer.strip() else {
                "verdict": "FAIL", "compiles": False, "complete": False,
                "problems": ["no answer written"], "warnings": [], "axioms": {},
                "diagnostics": ""}
            status = "infra" if (infra and not answer.strip()) else _classify(
                chk, req["statement_only"], answer)
            fixed = ""
            for f in ("context.lean", "statement.lean"):
                if (jobdir / f).is_file():
                    fixed += (jobdir / f).read_text() + "\n"
            missing = preserved(fixed, answer) if fixed and answer.strip() else []
            if answer.strip():
                shutil.copy2(answer_path, jobdir / f"s{i}.lean")
            summary = {
                "sample": i, "status": status,
                "lean_file": str(jobdir / f"s{i}.lean") if answer.strip() else None,
                "check": {k: chk.get(k) for k in ("verdict", "compiles", "complete", "problems",
                                                  "warnings", "axioms_used", "diagnostics")},
                "fixed_code_preserved": (not missing) if fixed else None,
                "fixed_code_missing": missing,
                "timed_out": timed_out,
                "elapsed_sec": round(time.time() - t0, 1),
                "turns": res.get("history_entries"),
                "tool_calls": res.get("tool_calls"),
                "stop_reason": res.get("stop_reason"),
                "agent_error": res.get("agent_error"),
                "infra": infra,
                "harness_finalize": res.get("finalized"),
            }
            _write_json(ws / "summary.json", summary)
            _write_json(st_path, {"state": "done", "status": status})
            return
    except Exception as e:                                         # noqa: BLE001
        _write_json(st_path, {"state": "done", "status": "infra",
                              "error": f"{type(e).__name__}: {e}"})
    finally:
        slot.close()


def cmd_worker(cfg: Config, jobdir: Path) -> int:
    req = _read_json(jobdir / "request.json")
    stop = threading.Event()

    def _term(*_):
        stop.set()
    signal.signal(signal.SIGTERM, _term)
    threads = [threading.Thread(target=run_sample, args=(cfg, jobdir, i, req, stop))
               for i in range(req["samples"])]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    _finish(jobdir)
    return 0


def _finish(jobdir: Path) -> dict:
    req = _read_json(jobdir / "request.json")
    sums = []
    for i in range(req.get("samples", 0)):
        s = _read_json(jobdir / f"s{i}" / "summary.json")
        if not s:
            st = _read_json(jobdir / f"s{i}" / "state.json")
            s = {"sample": i, "status": st.get("status", "infra"), "error": st.get("error")}
        sums.append(s)
    sums.sort(key=lambda s: (RANK.get(s.get("status"), 9),
                             0 if s.get("fixed_code_preserved") in (True, None) else 1,
                             s.get("elapsed_sec") or 0))
    out = {"job": req.get("job"), "name": req.get("name"), "done": time.time(),
           "statement_only": req.get("statement_only"),
           "best": sums[0] if sums else None, "samples": sums,
           "counts": {k: sum(1 for s in sums if s.get("status") == k) for k in RANK}}
    if sums and sums[0].get("lean_file"):
        shutil.copy2(sums[0]["lean_file"], jobdir / "best.lean")
    _write_json(jobdir / "result.json", out)
    return out


def job_state(jobdir: Path) -> dict:
    req = _read_json(jobdir / "request.json")
    states = [_read_json(jobdir / f"s{i}" / "state.json") for i in range(req.get("samples", 0))]
    done = (jobdir / "result.json").is_file()
    w = _read_json(jobdir / "worker.json")
    if not done and not _pid_alive(w.get("pid")):
        # The worker died (reboot, OOM kill): settle what exists rather than hang forever.
        _finish(jobdir)
        done = True
    running = [s for s in states if s.get("state") == "running"]
    return {
        "job": jobdir.name, "done": done,
        "samples": len(states),
        "queued": sum(1 for s in states if s.get("state") in (None, "queued")),
        "running": len(running),
        "finished": sum(1 for s in states if s.get("state") == "done"),
        "statuses": [s.get("status") for s in states if s.get("state") == "done"],
        "age_min": round((time.time() - req.get("created", time.time())) / 60, 1),
        "longest_running_min": round(max(
            [(time.time() - s.get("started", time.time())) / 60 for s in running],
            default=0), 1),
    }


def _fmt_state(s: dict) -> str:
    if s["done"]:
        return f"{s['job']}: DONE  {s['statuses']}"
    return (f"{s['job']}: {s['finished']}/{s['samples']} finished, {s['running']} running "
            f"(longest {s['longest_running_min']} min), {s['queued']} queued; "
            f"finished: {s['statuses']}")


def cmd_wait(cfg: Config, a: argparse.Namespace) -> int:
    dirs = [_job_dir(cfg, j) for j in a.jobs]
    t_end = time.time() + a.timeout
    while True:
        states = [job_state(d) for d in dirs]
        done = [s for s in states if s["done"]]
        if (a.any and done) or len(done) == len(states):
            for s in states:
                print(_fmt_state(s))
            return 0
        if time.time() >= t_end:
            for s in states:
                print(_fmt_state(s))
            print(f"(still running after {a.timeout}s -- call `aiprover wait` again; nothing "
                  f"is lost by waiting)")
            return 3
        time.sleep(min(15, max(1, t_end - time.time())))


def cmd_status(cfg: Config, a: argparse.Namespace) -> int:
    dirs = [_job_dir(cfg, a.job)] if a.job else sorted(cfg.jobs.iterdir())[-15:]
    for d in dirs:
        if d.is_dir() and (d / "request.json").is_file():
            print(_fmt_state(job_state(d)))
    return 0


def cmd_result(cfg: Config, a: argparse.Namespace) -> int:
    d = _job_dir(cfg, a.job)
    st = job_state(d)
    if not st["done"]:
        print(_fmt_state(st))
        print("not finished yet -- `aiprover wait` first")
        return 3
    r = _read_json(d / "result.json")
    if a.json:
        print(json.dumps(r, indent=1))
        return 0
    print(f"job {r['job']}  ({'statement-only' if r.get('statement_only') else 'theorem+proof'})"
          f"  counts: { {k: v for k, v in r['counts'].items() if v} }")
    for s in r["samples"]:
        c = s.get("check") or {}
        pres = s.get("fixed_code_preserved")
        print(f"  s{s['sample']}: {s.get('status'):9s} "
              f"{'' if pres is None else ('fixed-code:kept ' if pres else 'fixed-code:CHANGED ')}"
              f"{s.get('elapsed_sec', '?')}s turns={s.get('turns')} "
              f"{'TIMEOUT ' if s.get('timed_out') else ''}"
              f"{('problems: ' + '; '.join(c.get('problems') or [])[:200]) if c.get('problems') else ''}"
              f"{s.get('error') or ''}")
    b = r.get("best") or {}
    show = r["samples"] if a.all else [b]
    for s in show:
        if not s or not s.get("lean_file"):
            continue
        c = s.get("check") or {}
        print(f"\n===== s{s['sample']} [{s['status']}]  {s['lean_file']}")
        print(Path(s["lean_file"]).read_text(errors="replace").rstrip())
        if s.get("fixed_code_missing"):
            print("----- fixed code NOT reproduced verbatim:")
            for m in s["fixed_code_missing"]:
                print(f"   {m}")
        if c.get("verdict") != "PASS":
            print(f"----- check: {c.get('verdict')}; problems: {c.get('problems')}")
            if c.get("warnings"):
                print(f"----- warnings: {c.get('warnings')}")
            print(f"----- diagnostics:\n{c.get('diagnostics')}")
        elif c.get("warnings"):
            print(f"----- check PASS with warnings: {c.get('warnings')}")
    if not b.get("lean_file"):
        print("\nno sample produced a Lean file.")
    return 0


def cmd_cancel(cfg: Config, a: argparse.Namespace) -> int:
    d = _job_dir(cfg, a.job)
    w = _read_json(d / "worker.json")
    if _pid_alive(w.get("pid")):
        os.kill(w["pid"], signal.SIGTERM)
    req = _read_json(d / "request.json")
    for i in range(req.get("samples", 0)):
        st = _read_json(d / f"s{i}" / "state.json")
        if st.get("state") == "running" and st.get("pid"):
            try:
                os.killpg(st["pid"], signal.SIGKILL)
            except ProcessLookupError:
                pass
    print(f"cancelled {d.name}")
    return 0


def cmd_list(cfg: Config, a: argparse.Namespace) -> int:
    for d in sorted(cfg.jobs.iterdir())[-a.n:]:
        if (d / "request.json").is_file():
            print(_fmt_state(job_state(d)))
    return 0


def cmd_check(cfg: Config, a: argparse.Namespace) -> int:
    text = Path(a.file).expanduser().read_text(errors="replace")
    r = check_lean(cfg, text, statement_only=a.statement_only, label=Path(a.file).name)
    fixed = _read_arg(a.fixed, None)
    if fixed:
        miss = preserved(fixed, text)
        r["fixed_code_missing"] = miss
        if miss:
            r["problems"].append(f"{len(miss)} fixed declaration(s) not reproduced verbatim")
            r["verdict"] = "FAIL"
    if a.json:
        print(json.dumps(r, indent=1))
    else:
        print(f"{r['verdict']}  ({r['mode']})  compiles={r['compiles']} "
              f"complete={r['complete']}  axioms={r.get('axioms_used')}  "
              f"{r['compile_seconds']}s")
        for p in r["problems"]:
            print(f"  PROBLEM: {p}")
        for w in r["warnings"]:
            print(f"  warning: {w}")
        for m in r.get("fixed_code_missing") or []:
            print(f"  missing verbatim: {m}")
        if r["diagnostics"] != "(no errors or warnings)":
            print("diagnostics:\n" + r["diagnostics"])
    return 0 if r["verdict"] == "PASS" else 1


def cmd_render(cfg: Config, a: argparse.Namespace) -> int:
    sys.stdout.write(render_problem(a))
    return 0


def cmd_tunnel(cfg: Config, a: argparse.Namespace) -> int:
    if a.action == "down":
        print(tunnel_down(cfg))
        return 0
    if a.action == "up":
        try:
            api, models = ensure_endpoint(cfg)
        except AIProverError as e:
            print(f"DOWN: {e}")
            return 1
    models = probe(cfg)
    if models is None:
        print(f"DOWN: {cfg.api_base} does not answer")
        return 1
    m = (models.get("data") or [{}])[0]
    print(f"UP: {cfg.api_base}  model={m.get('id')}  max_model_len={m.get('max_model_len')}")
    return 0


def cmd_workspace(cfg: Config, a: argparse.Namespace) -> int:
    ws = agent_workspace(cfg)
    if a.new:
        f = ws / "work" / f"{re.sub(r'[^A-Za-z0-9_]+', '_', a.new)}.lean"
        f.parent.mkdir(parents=True, exist_ok=True)
        print(f)
    else:
        print(ws)
    return 0


def cmd_mcp_serve(cfg: Config, a: argparse.Namespace) -> int:
    """exec lean-lsp-mcp over stdio, rooted at the coding agent's scratch project."""
    ws = agent_workspace(cfg)
    env = dict(os.environ)
    path = [str(cfg.p("elan_home") / "bin")] + ([cfg.rg_dir()] if cfg.rg_dir() else [])
    env["PATH"] = ":".join(path + [env.get("PATH", "/usr/bin:/bin")])
    env["LEAN_PROJECT_PATH"] = str(ws)
    env["ELAN_HOME"] = str(cfg.p("elan_home"))
    env.pop("PYTHONPATH", None)
    py = str(cfg.venv_python("mcp_venv"))
    os.chdir(ws)
    os.execve(py, [py, "-m", "lean_lsp_mcp", "--lean-project-path", str(ws), "--repl"], env)
    return 0


# =============================================================================
# DOCTOR
# =============================================================================
def _sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def cmd_doctor(cfg: Config, a: argparse.Namespace) -> int:
    rows: list[tuple[str, bool, str]] = []

    def check(name: str, fn):
        try:
            ok, msg = fn()
        except Exception as e:                                     # noqa: BLE001
            ok, msg = False, f"{type(e).__name__}: {e}"
        rows.append((name, ok, msg))
        print(f"  {'PASS' if ok else 'FAIL'}  {name:34s} {msg}", flush=True)
        return ok

    print(f"config: {cfg.path}")

    def c_manifest():
        m = json.loads(MANIFEST.read_text())
        h, g = _sha(HARNESS)[:16], _sha(GRADER)[:16]
        ok = h == m["harness_sha256"][:16] and g == m["grader_sha256"][:16]
        return ok, f"harness {h} ({m.get('champion')}), grader {g}"
    check("harness is the pinned champion", c_manifest)

    def c_twin():
        other = {"claude_code": "codex", "codex": "claude_code"}
        root = SKILL_DIR.parents[1]                 # <plugin>/<agent>/skills/<skill> -> <plugin>
        me = SKILL_DIR.parents[1].name
        if me not in other:
            return True, "standalone copy"
        twin = root.parent / other[me] / "skills" / SKILL_DIR.name
        diffs = [f for f in ("scripts/aiprover.py", "harness/harness.py",
                             "harness/grade_type_correctness.py", "harness/MANIFEST.json")
                 if not (twin / f).is_file() or _sha(twin / f) != _sha(SKILL_DIR / f)]
        return not diffs, "claude_code/ and codex/ copies identical" if not diffs else \
            f"DIFFER: {diffs}"
    check("both skill copies identical", c_twin)

    lp = cfg.p("lean_project")
    check("lean project built", lambda: (
        (lp / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file(),
        str(lp)))
    check("lean toolchain pinned + installed", lambda: (
        True, f"{grader(cfg).pinned_toolchain(lp)} -> {grader(cfg).lean_bin(lp)}"))
    check("REPL built (for --repl tools)", lambda: (
        bool(glob.glob(str(lp / ".lake/packages/[Rr][Ee][Pp][Ll]/.lake/build/bin/repl"))),
        "lean REPL binary present"))

    def c_cslib():
        pkg = lp / ".lake/packages/cslib"
        built = (pkg / ".lake/build/lib/lean/Cslib.olean").is_file()
        if not built:
            return False, "missing: run ./setup.sh cslib (adds + builds the pinned package, ~15 s)"
        tc = (pkg / "lean-toolchain").read_text().strip() if (pkg / "lean-toolchain").is_file() else "?"
        same = tc == grader(cfg).pinned_toolchain(lp)
        return same, f"Cslib oleans present, toolchain {tc}" + ("" if same else " != project's")
    check("cslib built (CS library, same Lean)", c_cslib)

    def c_canary():
        (cfg.work_root / "checks").mkdir(exist_ok=True)
        t0 = time.time()
        ok, out = grader(cfg).compile_text(grader(cfg).CANARY, work=cfg.work_root / "checks",
                                           project=lp)
        return ok, f"`import Mathlib` compiles in {time.time() - t0:.0f}s" if ok else out[:300]
    check("Mathlib canary compiles", c_canary)

    def c_axioms():
        bad = check_lean(cfg, "import Mathlib\ntheorem t (n : Nat) : n + 0 = n := by sorry\n")
        nat = check_lean(cfg, "import Mathlib\ntheorem t : (2:Nat) + 2 = 4 := by native_decide\n")
        good = check_lean(cfg, "import Mathlib\ntheorem t (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := "
                               "by positivity\n")
        ok = (bad["verdict"] == "FAIL" and not bad["complete"] and nat["verdict"] == "FAIL"
              and good["verdict"] == "PASS")
        return ok, (f"sorry->{bad['verdict']}, native_decide->{nat['verdict']}, "
                    f"clean->{good['verdict']} {good['axioms_used']}")
    check("check: kernel axiom probe", c_axioms)

    def c_paths():
        ws = cfg.work_root / "doctor_paths"
        ws.mkdir(parents=True, exist_ok=True)
        return audit_harness_paths(cfg, ws)
    check("harness paths all local", c_paths)

    def c_vibe():
        r = subprocess.run([str(cfg.venv_python("vibe_venv")), "-c",
                            "import importlib.metadata as m, vibe.app_server.local; "
                            "print(m.version('mistral-vibe'))"],
                           capture_output=True, text=True, timeout=120,
                           env={**os.environ, "PYTHONPATH": str(cfg.site_packages("vibe_venv"))})
        v = r.stdout.strip()
        return r.returncode == 0 and v == "2.24.2", f"mistral-vibe {v or r.stderr[-200:]}"
    check("vibe (harness agent loop)", c_vibe)

    def c_mcp():
        r = subprocess.run([str(cfg.venv_python("mcp_venv")), "-c",
                            "import importlib.metadata as m, lean_lsp_mcp, leanclient.aio.client "
                            "as c; print(m.version('lean-lsp-mcp'), c.MIN_LEAN_VERSION)"],
                           capture_output=True, text=True, timeout=120)
        out = r.stdout.strip()
        ok = r.returncode == 0 and "(4, 23)" in out
        return ok, (f"lean-lsp-mcp {out}" + ("" if ok else
                    " -- leanclient gate NOT relaxed: run setup.sh (fix-lean-tools)"))
    check("lean-lsp-mcp + leanclient patch", c_mcp)

    def c_follow():
        # Both Lean projects reach the libraries through a `.lake/packages` symlink; ripgrep only
        # traverses it with --follow, which setup.sh patches into lean-lsp-mcp's local search.
        hits = glob.glob(str(cfg.site_packages("mcp_venv") / "lean_lsp_mcp" / "search_utils.py"))
        ok = bool(hits) and '"--follow",' in Path(hits[0]).read_text()
        return ok, ("ripgrep follows .lake/packages (Mathlib + cslib names searchable)" if ok else
                    "lean_local_search would see NO library declarations: run ./setup.sh venvs")
    check("lean_local_search reaches the libraries", c_follow)

    def c_rg():
        path = ":".join(([cfg.rg_dir()] if cfg.rg_dir() else []) + [os.environ.get("PATH", "")])
        w = shutil.which("rg", path=path)
        return bool(w), w or "ripgrep not found (lean_local_search needs it)"
    check("ripgrep", c_rg)

    def c_endpoint():
        api, models = ensure_endpoint(cfg)
        m = [d for d in models.get("data", []) if d.get("id") == served_model(cfg, models)][0]
        mml = m.get("max_model_len")
        return True, f"{api} model={m['id']} max_model_len={mml}"
    ep_ok = check("model endpoint (tunnel + /models)", c_endpoint)

    if ep_ok:
        def c_think():
            api, models = ensure_endpoint(cfg)
            r = _http_json(api + "/chat/completions", key=cfg.api_key, timeout=300, data={
                "model": served_model(cfg, models), "max_tokens": 600, "temperature": 1.0,
                "reasoning_effort": "high",
                "messages": [{"role": "user", "content": "What is 17*3? Reply with the number."}]})
            msg = r["choices"][0]["message"]
            reasoning = msg.get("reasoning") or msg.get("reasoning_content") or ""
            return bool(reasoning.strip()), (f"reasoning {len(reasoning)} chars, answer "
                                             f"{(msg.get('content') or '').strip()[:40]!r}")
        check("model thinks (reasoning_effort=high)", c_think)

    if a.full:
        def c_selftest():
            ws = cfg.work_root / "doctor_selftest"
            shutil.rmtree(ws, ignore_errors=True)
            ws.mkdir(parents=True)
            (ws / "problem.txt").write_text(
                "<informal_theorem>\nFor every natural number n, n + 0 = n.\n</informal_theorem>"
                "\n\n<informal_proof>\nBy the definition of addition.\n</informal_proof>\n")
            env = harness_env(cfg, ws, cfg.api_base, "selftest")
            r = subprocess.run([str(cfg.venv_python("vibe_venv")), str(HARNESS), "selftest"],
                               cwd=str(ws), env=env, capture_output=True, text=True,
                               timeout=1800)
            last = [l for l in r.stdout.splitlines() if l.startswith("SELFTEST")]
            fails = [l.strip()[6:] for l in r.stdout.splitlines() if l.strip().startswith("FAIL ")]
            # `mathlib read-only` asserts the CONTAINER's :ro mount. AIProver runs the harness
            # directly on the host (as the evolution run did, via tools/apptainer-local), so it
            # holds exactly when this user cannot write the shared project -- a hygiene
            # property, not a correctness one. Reported, never fatal.
            known = {"mathlib read-only"}
            real = [f for f in fails if f not in known]
            note = (" (known under host execution: 'mathlib read-only' -- this user can write "
                    "the shared Lean project; see STARTUP.md)") if set(fails) & known else ""
            if not last:
                return False, (r.stdout + r.stderr)[-400:]
            return not real, last[-1] + note
        check("harness selftest (no model call)", c_selftest)

        def c_mcp_smoke():
            r = subprocess.run([sys.executable, str(Path(__file__).resolve()), "_mcp_smoke"],
                               capture_output=True, text=True, timeout=900)
            tail = [l for l in r.stdout.splitlines() if l.startswith("MCP-SMOKE")]
            return r.returncode == 0, (tail[-1] if tail else (r.stdout + r.stderr)[-400:])
        check("lean-lsp-mcp tools (coding agent)", c_mcp_smoke)

    if a.full and ep_ok:
        def c_live():
            """AIProver AS AN AGENT, end to end: a real rollout on a one-line theorem. PASS needs
            a verified answer AND at least one lean-lsp call by the model with none failing --
            so a tool that is registered but broken inside the harness is caught here."""
            d = cfg.jobs / f"doctor-live-{int(time.time())}"
            d.mkdir(parents=True)
            prob = ("<informal_theorem>\nFor all natural numbers a and b, a + b = b + a.\n"
                    "</informal_theorem>\n\n<informal_proof>\nBy commutativity of addition "
                    "on the natural numbers.\n</informal_proof>\n")
            (d / "problem.txt").write_text(prob)
            req = {"job": d.name, "name": "doctor", "samples": 1, "created": time.time(),
                   "statement_only": False, "timeout_sec": 1500, "max_turns": cfg.max_turns}
            _write_json(d / "request.json", req)
            (d / "s0").mkdir()
            (d / "s0" / "problem.txt").write_text(prob)
            _write_json(d / "worker.json", {"pid": os.getpid(), "started": time.time()})
            run_sample(cfg, d, 0, req, threading.Event())
            r = _finish(d)
            s0 = r["samples"][0]
            ev = _read_json(d / "s0" / "result.json").get("events", [])
            lean = [(e.get("title"), (e.get("state") or {}).get("status")) for e in ev
                    if e.get("type") == "effect" and str(e.get("title", "")).startswith("m_lean")]
            failed = [t for t, st in lean if st == "failed"]
            ok = s0.get("status") == "verified" and bool(lean) and not failed
            return ok, (f"{s0.get('status')} in {s0.get('elapsed_sec')}s; model made {len(lean)} "
                        f"lean-lsp calls, {len(failed)} failed {failed or ''}"
                        + ("" if lean else " -- NO lean-lsp call: tools unreachable?"))
        check("AIProver live rollout + its tools", c_live)

    if a.agents:
        root = cfg.path.resolve().parent

        def c_claude():
            if not shutil.which("claude"):
                return False, "claude CLI not on PATH"
            r = subprocess.run(["claude", "-p", "--output-format", "stream-json", "--verbose",
                                "--max-turns", "1", "Reply OK"], capture_output=True, text=True,
                               timeout=300, cwd=str(cfg.work_root))
            try:
                init = json.loads(r.stdout.splitlines()[0])
            except (IndexError, ValueError):
                return False, f"no init message: {(r.stdout + r.stderr)[:200]}"
            skills = [x for x in init.get("skills", []) if "aiprover" in x]
            mcp = [m for m in init.get("mcp_servers", []) if "lean-lsp" in m.get("name", "")]
            tools = [t for t in init.get("tools", []) if "lean-lsp" in t]
            ok = bool(skills) and bool(mcp) and mcp[0].get("status") == "connected" and \
                len(tools) >= 20
            return ok, (f"skill {skills or 'MISSING'}, mcp {[(m['name'], m['status']) for m in mcp] or 'MISSING'}, "
                        f"{len(tools)} lean tools" + ("" if ok else " -- run setup.sh claude"))
        check("Claude Code sees skill + lean-lsp", c_claude)

        def c_codex():
            codex = shutil.which("codex") or next(iter(sorted(Path.home().glob(
                ".vscode-server/extensions/openai.chatgpt-*/bin/linux-*/codex"), reverse=True)),
                None)
            if not codex:
                return False, "codex CLI not found"
            skill = Path.home() / ".agents" / "skills" / SKILL_DIR.name
            if not (skill / "SKILL.md").is_file():
                return False, f"{skill} missing -- run setup.sh codex"
            out = cfg.work_root / "doctor_codex.txt"
            r = subprocess.run([str(codex), "exec", "--skip-git-repo-check", "--sandbox",
                                "danger-full-access", "-o", str(out), "-C", str(cfg.work_root),
                                "Call the MCP tool lean_local_search (server lean-lsp) with "
                                "query 'add_comm' and limit 1. Reply with exactly TOOL-OK if it "
                                "returned a result, else TOOL-FAIL and the error. Also say "
                                "SKILL-OK if a skill named aiprover-autoformalize is available "
                                "to you, else SKILL-MISSING."],
                               capture_output=True, text=True, timeout=600)
            ans = out.read_text() if out.is_file() else (r.stdout + r.stderr)[-300:]
            ok = "TOOL-OK" in ans and "SKILL-OK" in ans
            return ok, " ".join(ans.split())[:160] + ("" if ok else " -- run setup.sh codex")
        check("Codex sees skill + calls lean-lsp", c_codex)

    bad = [n for n, ok, _ in rows if not ok]
    print(f"DOCTOR: {len(rows) - len(bad)}/{len(rows)} PASS" + (f"  FAILED: {bad}" if bad else ""))
    if bad:
        guide = cfg.path.resolve().parent / "STARTUP.md"
        print(f"fix: see {guide if guide.is_file() else 'STARTUP.md in AIProver_plugin/'} "
              f"(section 5 maps every check to its fix)")
    return 1 if bad else 0


def cmd_mcp_smoke(cfg: Config) -> int:
    """Drive `aiprover mcp-serve` exactly as the coding agent does and call the key tools."""
    smoke = HERE / "smoke_lean_mcp.py"
    py = str(cfg.venv_python("mcp_venv"))
    r = subprocess.run([py, str(smoke), sys.executable, str(Path(__file__).resolve()),
                        str(agent_workspace(cfg))], text=True, timeout=880)
    return r.returncode


# =============================================================================
# CLI
# =============================================================================
def _problem_args(p: argparse.ArgumentParser) -> None:
    g = p.add_argument_group("the problem (one of --problem / --theorem[-text])")
    g.add_argument("--problem", help="file holding <informal_theorem>..</informal_theorem> "
                                     "<informal_proof>..</informal_proof>")
    g.add_argument("--theorem", help="file with the NL theorem (statement, definitions)")
    g.add_argument("--theorem-text", help="the NL theorem inline")
    g.add_argument("--proof", help="file with the NL proof")
    g.add_argument("--proof-text", help="the NL proof inline")
    g.add_argument("--context", help="Lean file of FIXED declarations the answer must contain "
                                     "verbatim (shared definitions, already-proved lemmas)")
    g.add_argument("--lean-statement", help="Lean file with the FIXED statement to prove "
                                            "(ending in `:= by sorry`)")
    g.add_argument("--hint", help="one short line of guidance appended to the theorem block")
    g.add_argument("--hint-file", help="file with longer guidance (a compiler error, the goal "
                                       "state where the last attempt got stuck, lemma names)")
    g.add_argument("--statement-only", action="store_true",
                   help="formalize the statement only (the proof block is sent empty)")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="aiprover", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("submit", help="start an AIProver job (returns immediately)")
    _problem_args(s)
    s.add_argument("--samples", "-k", type=int, default=4,
                   help="independent AIProver rollouts, run in parallel (default 4)")
    s.add_argument("--name", help="short label for the job id")
    s.add_argument("--timeout", type=int, help="per-rollout wall seconds (default from config)")
    s.add_argument("--max-turns", type=int, help="harness turn budget (default from config)")
    s.add_argument("--quiet", "-q", action="store_true")

    r = sub.add_parser("render", help="print the problem.txt a submit would send")
    _problem_args(r)

    w = sub.add_parser("wait", help="block until job(s) finish, at most --timeout seconds")
    w.add_argument("jobs", nargs="+")
    w.add_argument("--timeout", type=int, default=540)
    w.add_argument("--any", action="store_true", help="return when ANY job finishes")

    x = sub.add_parser("result", help="show a finished job: per-sample summary + best Lean")
    x.add_argument("job")
    x.add_argument("--json", action="store_true")
    x.add_argument("--all", action="store_true", help="print every sample's Lean, not just best")

    st = sub.add_parser("status")
    st.add_argument("job", nargs="?")
    li = sub.add_parser("list")
    li.add_argument("-n", type=int, default=20)
    ca = sub.add_parser("cancel")
    ca.add_argument("job")

    c = sub.add_parser("check", help="mechanical checks (a)+(b) on a Lean file")
    c.add_argument("file")
    c.add_argument("--statement-only", action="store_true", help="allow `sorry` proofs")
    c.add_argument("--fixed", help="Lean file of declarations that must appear verbatim")
    c.add_argument("--json", action="store_true")

    pb = sub.add_parser("probe", help="statement sanity probe: counterexample search (plausible) "
                                     "+ which automation tactics close each statement alone")
    pb.add_argument("file")
    pb.add_argument("--json", action="store_true")

    se = sub.add_parser("search", help="search declarations + docstrings of the pinned libraries "
                                      "(cslib by default; lean_local_search covers names)")
    se.add_argument("query", help="words that must all occur in the name, header or docstring")
    se.add_argument("--lib", default="cslib",
                    choices=["cslib", "mathlib", "all", "loogle", "leansearch", "leandex"],
                    help="local pinned libraries (cslib default, mathlib, all) or a hosted index")
    se.add_argument("-n", type=int, default=15)
    se.add_argument("--json", action="store_true")

    ex = sub.add_parser("extract", help="the goal at a `sorry` as a standalone lemma (Lean writes "
                                       "the binders via extract_goal), for delegating a stuck step")
    ex.add_argument("file")
    ex.add_argument("--line", type=int, required=True, help="1-indexed line holding the sorry")
    ex.add_argument("--col", type=int, help="1-indexed column to pick one of several sorries")
    ex.add_argument("--name", help="lemma name (default <theorem>_step_L<line>)")
    ex.add_argument("--json", action="store_true")

    be_help = ("which LLM answers: auto (default) = claude inside a Claude Code session, codex inside "
               "Codex, else the AIProver model server; [helpers].backend in aiprover.toml overrides")
    xp = sub.add_parser("expand", help="rewrite the informal proof as explicit numbered steps (method "
                                      "and lemmas kept), with a critique round")
    _problem_args(xp)
    xp.add_argument("--rounds", type=int, default=2, help="writer + (rounds-1) critic/refine passes")
    xp.add_argument("--out", help="write a complete problem file (theorem unchanged, proof expanded)")
    xp.add_argument("--backend", choices=HELPER_BACKENDS, help=be_help)
    xp.add_argument("--dry-run", action="store_true", help="print the prompt, call nothing")

    bt = sub.add_parser("backtranslate", help="state in plain English what each declaration of a "
                                             "Lean file says, from a fresh context (judge aid)")
    bt.add_argument("file")
    bt.add_argument("--backend", choices=HELPER_BACKENDS, help=be_help)
    bt.add_argument("--dry-run", action="store_true")

    ak = sub.add_parser("ask", help="one free-form question to the LLM of this mode")
    ak.add_argument("question")
    ak.add_argument("--file", help="a Lean file to include as context")
    ak.add_argument("--max-tokens", type=int, default=4000)
    ak.add_argument("--backend", choices=HELPER_BACKENDS, help=be_help)
    ak.add_argument("--dry-run", action="store_true")

    t = sub.add_parser("tunnel")
    t.add_argument("action", nargs="?", default="status", choices=["up", "status", "down"])

    ws = sub.add_parser("workspace", help="the coding agent's Lean scratch project")
    ws.add_argument("--new", metavar="NAME", help="print a fresh file path work/NAME.lean in it")

    d = sub.add_parser("doctor", help="verify the whole environment")
    d.add_argument("--full", action="store_true",
                   help="also: harness selftest, all 23 lean-lsp tools, and one LIVE AIProver "
                        "rollout that must use its tools successfully (~3-5 min)")
    d.add_argument("--agents", action="store_true",
                   help="also ask Claude Code and Codex themselves whether they see the skill "
                        "and can call lean-lsp (costs a few k frontier tokens)")

    sub.add_parser("mcp-serve", help="exec lean-lsp-mcp over stdio (MCP launcher)")
    cf = sub.add_parser("config", help="print the resolved configuration")
    cf.add_argument("--shell", action="store_true", help="KEY=VALUE lines for scripts")
    wk = sub.add_parser("_worker")
    wk.add_argument("jobdir")
    sub.add_parser("_mcp_smoke")

    a = ap.parse_args(argv)
    try:
        cfg = Config()
        if a.cmd == "config" and a.shell:
            # For setup.sh: one KEY=VALUE per line, shell-quoted, paths expanded.
            vals = {"AIP_CONFIG": cfg.path, "AIP_WORK_ROOT": cfg.work_root,
                    "AIP_MODE": cfg.mode, "AIP_API_BASE": cfg.api_base,
                    "AIP_RG_DIR": cfg.rg_dir() or ""}
            for k in ("lean_project", "elan_home", "vibe_venv", "mcp_venv"):
                vals[f"AIP_{k.upper()}"] = cfg.p(k)
            for k, v in vals.items():
                print(f"{k}={shlex.quote(str(v))}")
            return 0
        if a.cmd == "config":
            print(f"config        {cfg.path}\napi_base      {cfg.api_base}  (mode={cfg.mode})")
            for k in ("lean_project", "elan_home", "vibe_venv", "mcp_venv"):
                print(f"{k:13s} {cfg.p(k)}")
            print(f"work_root     {cfg.work_root}\nmax_parallel  {cfg.max_parallel}\n"
                  f"harness       {HARNESS}")
            return 0
        return {
            "submit": lambda: cmd_submit(cfg, a),
            "render": lambda: cmd_render(cfg, a),
            "wait": lambda: cmd_wait(cfg, a),
            "result": lambda: cmd_result(cfg, a),
            "status": lambda: cmd_status(cfg, a),
            "list": lambda: cmd_list(cfg, a),
            "cancel": lambda: cmd_cancel(cfg, a),
            "check": lambda: cmd_check(cfg, a),
            "probe": lambda: cmd_probe(cfg, a),
            "search": lambda: cmd_search(cfg, a),
            "extract": lambda: cmd_extract(cfg, a),
            "expand": lambda: cmd_expand(cfg, a),
            "backtranslate": lambda: cmd_backtranslate(cfg, a),
            "ask": lambda: cmd_ask(cfg, a),
            "tunnel": lambda: cmd_tunnel(cfg, a),
            "workspace": lambda: cmd_workspace(cfg, a),
            "doctor": lambda: cmd_doctor(cfg, a),
            "mcp-serve": lambda: cmd_mcp_serve(cfg, a),
            "_worker": lambda: cmd_worker(cfg, Path(a.jobdir)),
            "_mcp_smoke": lambda: cmd_mcp_smoke(cfg),
        }[a.cmd]()
    except AIProverError as e:
        print(f"aiprover: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
