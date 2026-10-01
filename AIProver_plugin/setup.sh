#!/usr/bin/env bash
# =============================================================================
# AIProver setup -- provisions everything the coding agents (Claude Code, Codex) and the
# AIProver agent need on THIS machine, then verifies it. IDEMPOTENT: safe to re-run; every step
# checks first and does nothing if its target already works.
#
#   ./setup.sh                 everything: sync, deps, claude, codex, doctor --full --agents
#   ./setup.sh deps            elan + Lean 4.23.0, the Mathlib project (+ cslib), both venvs, ripgrep
#   ./setup.sh cslib           add + build the pinned cslib package in an EXISTING Lean project
#   ./setup.sh claude          install the Claude Code plugin (skill + lean-lsp MCP)
#   ./setup.sh codex           install the Codex skill + register the lean-lsp MCP server
#   ./setup.sh doctor          verify only (= bin/aiprover doctor --full --agents)
#   ./setup.sh sync            copy the canonical skill files claude_code/ -> codex/
#
# Paths come from aiprover.toml ([paths]); edit that file first on a new machine. Anything that
# already exists at a configured path is used as it is, never rebuilt.
# Read STARTUP.md for what each step is for and how to fix a failing check.
# =============================================================================
set -euo pipefail
ROOT="$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)"
SKILL=aiprover-autoformalize
CC_SKILL="$ROOT/claude_code/skills/$SKILL"
CX_SKILL="$ROOT/codex/skills/$SKILL"
AIP="$CC_SKILL/scripts/aiprover"
LEAN_TOOLCHAIN="leanprover/lean4:v4.23.0"
RG_VERSION=14.1.1

say()  { printf '\n== %s\n' "$*"; }
ok()   { printf '   ok: %s\n' "$*"; }
die()  { printf '   FAILED: %s\n' "$*" >&2; exit 1; }

need_python() {
  for py in python3.12 python3; do
    if command -v "$py" >/dev/null && "$py" -c 'import sys; sys.exit(sys.version_info[:2] != (3, 12))' 2>/dev/null; then
      PY312=$(command -v "$py"); return 0; fi
  done
  die "Python 3.12 is required for the venvs (the lock files were resolved on 3.12.3)"
}

load_config() {
  eval "$("$AIP" config --shell)"
  ok "config $AIP_CONFIG"
}

# ---------------------------------------------------------------------------
step_sync() {
  say "sync: claude_code/ is canonical; codex/ gets identical scripts, harness, references"
  mkdir -p "$CX_SKILL"
  for d in scripts harness references; do
    rm -rf "${CX_SKILL:?}/$d"; cp -a "$CC_SKILL/$d" "$CX_SKILL/$d"
  done
  find "$ROOT" -name __pycache__ -type d -prune -exec rm -rf {} +
  ok "codex/skills/$SKILL synced (its SKILL.md is Codex-specific and kept)"
}

step_elan() {
  say "elan + $LEAN_TOOLCHAIN"
  export ELAN_HOME="$AIP_ELAN_HOME"
  if [ ! -x "$ELAN_HOME/bin/elan" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none --no-modify-path
  fi
  local tc="$ELAN_HOME/toolchains/${LEAN_TOOLCHAIN//\//--}"; tc="${tc//:/---}"
  [ -x "$tc/bin/lean" ] || "$ELAN_HOME/bin/elan" toolchain install "$LEAN_TOOLCHAIN"
  [ -x "$tc/bin/lean" ] || die "toolchain missing at $tc"
  ok "$("$tc/bin/lean" --version)"
}

step_lean_project() {
  say "Lean project (Mathlib v4.23.0 + REPL) at $AIP_LEAN_PROJECT"
  local P="$AIP_LEAN_PROJECT"
  if [ -f "$P/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ] && \
     ls "$P"/.lake/packages/[Rr][Ee][Pp][Ll]/.lake/build/bin/repl >/dev/null 2>&1; then
    ok "already built"; return 0
  fi
  mkdir -p "$P"
  for f in lakefile.lean lake-manifest.json lean-toolchain; do
    [ -f "$P/$f" ] || cp "$ROOT/setup/lean_project/$f" "$P/$f"
  done
  [ -f "$P/TmpProjDir.lean" ] || echo "-- library root (intentionally empty)" > "$P/TmpProjDir.lean"
  export ELAN_HOME="$AIP_ELAN_HOME"; export PATH="$ELAN_HOME/bin:$PATH"
  ( cd "$P" && lake exe cache get )            # prebuilt Mathlib oleans (~5 GB download)
  ( cd "$P" && lake build repl )               # the Lean REPL behind lean-lsp-mcp --repl
  [ -f "$P/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ] || die "Mathlib oleans missing"
  ok "built"
}

# cslib (the Lean library for Computer Science), pinned to its last commit on Lean v4.23.0. That
# commit's manifest pins mathlib and batteries at EXACTLY this project's revisions, so `lake build`
# fetches only cslib and compiles its ~30 modules (~15 s) against the prebuilt oleans; Mathlib is
# not rebuilt or moved. A project provisioned before this step existed gets the two pins appended
# here; `lake` then resolves cslib from the manifest entry, never via `lake update`.
CSLIB_REV=cd368e67e7b5cd563be1d7dc47254e9c4d5962cf
step_cslib() {
  say "cslib (CS library, pinned $CSLIB_REV) in $AIP_LEAN_PROJECT"
  local P="$AIP_LEAN_PROJECT"
  [ -f "$P/lakefile.lean" ] && [ -f "$P/lake-manifest.json" ] || die "no Lean project at $P: run ./setup.sh lean first"
  if grep -q 'require cslib' "$P/lakefile.lean"; then
    ok "lakefile already requires cslib"
  else
    # The pins live in setup/lean_project/; copy them verbatim rather than restating them here.
    sed -n '/^-- CSLib, the Lean library/,/^  "https:\/\/github.com\/leanprover\/cslib"/p' "$ROOT/setup/lean_project/lakefile.lean" > "$P/.cslib_require.tmp"
    grep -q 'require cslib' "$P/.cslib_require.tmp" || die "could not extract the cslib require from setup/lean_project/lakefile.lean"
    { printf '\n'; cat "$P/.cslib_require.tmp"; } >> "$P/lakefile.lean"; rm -f "$P/.cslib_require.tmp"
    ok "appended the cslib require to lakefile.lean"
  fi
  "$PY" - "$P/lake-manifest.json" "$ROOT/setup/lean_project/lake-manifest.json" <<'PYEOF'
import json, sys
dst, src = sys.argv[1], sys.argv[2]
m = json.load(open(dst))
if not any(p["name"] == "cslib" for p in m["packages"]):
    entry = next(p for p in json.load(open(src))["packages"] if p["name"] == "cslib")
    m["packages"].append(entry)
    with open(dst, "w") as f:
        json.dump(m, f, indent=1); f.write("\n")
    print("   ok: added the cslib entry to lake-manifest.json")
else:
    print("   ok: lake-manifest.json already lists cslib")
PYEOF
  if [ -f "$P/.lake/packages/cslib/.lake/build/lib/lean/Cslib.olean" ] && \
     [ "$(git -C "$P/.lake/packages/cslib" rev-parse HEAD 2>/dev/null)" = "$CSLIB_REV" ]; then
    ok "already built at $CSLIB_REV"; return 0
  fi
  export ELAN_HOME="$AIP_ELAN_HOME"; export PATH="$ELAN_HOME/bin:$PATH"
  # STARTUP.md §6 recommends `chmod -R a-w` on the packages tree so no agent can write the shared
  # Mathlib. Lake must create .lake/packages/cslib inside it, so lift that for the build only
  # and put it back -- on the parent AND on the new package, so cslib is as protected as Mathlib.
  local relock=0
  if [ ! -w "$P/.lake/packages" ]; then chmod u+w "$P/.lake/packages"; relock=1; fi
  ( cd "$P" && lake build cslib/Cslib ) || { [ $relock = 1 ] && chmod a-w "$P/.lake/packages"; die "lake build cslib/Cslib failed"; }
  if [ $relock = 1 ]; then chmod -R a-w "$P/.lake/packages/cslib"; chmod a-w "$P/.lake/packages"; fi
  [ -f "$P/.lake/packages/cslib/.lake/build/lib/lean/Cslib.olean" ] || die "cslib oleans missing after build"
  [ "$(git -C "$P/.lake/packages/cslib" rev-parse HEAD)" = "$CSLIB_REV" ] || die "cslib is not at $CSLIB_REV"
  # Same Lean everywhere: the pinned cslib commit must declare the project's own toolchain.
  [ "$(cat "$P/.lake/packages/cslib/lean-toolchain")" = "$(cat "$P/lean-toolchain")" ] || \
    die "cslib toolchain $(cat "$P/.lake/packages/cslib/lean-toolchain") != project $(cat "$P/lean-toolchain")"
  ok "built ($(find "$P/.lake/packages/cslib/.lake/build/lib/lean" -name '*.olean' | wc -l) oleans, toolchain $(cat "$P/.lake/packages/cslib/lean-toolchain"))"
  echo "   note: a running lean-lsp MCP server (Claude Code / Codex session) must be restarted to see cslib"
}

make_venv() {   # $1 = venv dir, $2 = lock file
  local V="$1" LOCK="$2"
  if [ ! -x "$V/bin/python3" ]; then
    "$PY312" -m venv "$V"
  fi
  "$V/bin/python3" -m pip install --quiet --upgrade pip >/dev/null
  "$V/bin/python3" -m pip install --quiet -r "$LOCK"
}

step_venvs() {
  need_python
  say "vibe venv (mistral-vibe 2.24.2, the harness's agent loop) at $AIP_VIBE_VENV"
  if "$AIP_VIBE_VENV/bin/python3" -c 'import importlib.metadata as m; assert m.version("mistral-vibe")=="2.24.2"' 2>/dev/null; then
    ok "present"
  else
    make_venv "$AIP_VIBE_VENV" "$ROOT/setup/requirements-vibe.lock"; ok "installed"
  fi
  say "MCP venv (lean-lsp-mcp 0.30.0) at $AIP_MCP_VENV"
  if "$AIP_MCP_VENV/bin/python3" -c 'import importlib.metadata as m; assert m.version("lean-lsp-mcp")=="0.30.0"' 2>/dev/null; then
    ok "present"
  else
    make_venv "$AIP_MCP_VENV" "$ROOT/setup/requirements-mcp.lock"; ok "installed"
  fi
  # leanclient >= 0.12 refuses to start a language server on Lean < 4.24. We pin 4.23.0 (the
  # grader's toolchain), and leanclient documents the gate as advisory. Unpatched, ~15 of the 23
  # lean tools fail on every call. RE-RUN THIS after any pip install into the MCP venv.
  local CLIENT
  CLIENT=$(find "$AIP_MCP_VENV" -path '*/leanclient/aio/client.py' -print -quit)
  [ -n "$CLIENT" ] || die "leanclient not found in $AIP_MCP_VENV"
  if grep -q '^MIN_LEAN_VERSION = (4, 23)' "$CLIENT" && \
     "$AIP_MCP_VENV/bin/python3" -c 'import leanclient.aio.client as c; assert c.MIN_LEAN_VERSION == (4, 23)' 2>/dev/null; then
    ok "leanclient gate already relaxed to 4.23 (source and loaded module agree)"
  else
    [ -f "$CLIENT.orig" ] || cp "$CLIENT" "$CLIENT.orig"
    sed -i 's/^MIN_LEAN_VERSION = (4, [0-9]\+)/MIN_LEAN_VERSION = (4, 23)/' "$CLIENT"
    grep -q '^MIN_LEAN_VERSION = (4, 23)' "$CLIENT" || die "could not patch $CLIENT"
    # The edit keeps the file's SIZE and usually lands in the same SECOND as pip's bytecode
    # compile, so the .pyc (validated by mtime-seconds + size) still looks fresh and Python keeps
    # running the unpatched (4, 24). Measured on a fresh venv. Drop the bytecode.
    rm -f "$(dirname "$CLIENT")"/__pycache__/client.*.pyc
    ok "leanclient gate relaxed to 4.23 (backup $CLIENT.orig)"
  fi
  # Lean 4.23 + lean-lsp-mcp 0.30.0: the scratch pools (lean_file_outline, lean_run_code,
  # lean_verify, lean_minimal_hypotheses, lean_multi_attempt) warm their slot with an EMPTY
  # header, so the first real trial changes the imports to `import Mathlib`. On the 4.23 server
  # that header change plus an immediate waitForDiagnostics is never answered: the first such
  # tool call of EVERY fresh MCP session hangs 300 s and errors (the 2nd call works). Measured
  # 2026-09-21: smoke 20 PASS / 1 FAIL in ~6.5 min -> 21 PASS in 54 s once the slots are warmed
  # with the project's header. Idempotent; re-applied after any pip install like the gate above.
  local SCRATCH CLIENT_UTILS
  SCRATCH=$(find "$AIP_MCP_VENV" -path '*/leanclient/aio/scratch.py' -print -quit)
  CLIENT_UTILS=$(find "$AIP_MCP_VENV" -path '*/lean_lsp_mcp/client_utils.py' -print -quit)
  [ -n "$SCRATCH" ] && [ -n "$CLIENT_UTILS" ] || die "leanclient/aio/scratch.py or lean_lsp_mcp/client_utils.py not found in $AIP_MCP_VENV"
  if grep -q 'warm_text' "$SCRATCH" && grep -q 'warm_text' "$CLIENT_UTILS"; then
    ok "scratch pools already warm with the project header (warm_text patch present)"
  else
    [ -f "$SCRATCH.orig" ] || cp "$SCRATCH" "$SCRATCH.orig"
    [ -f "$CLIENT_UTILS.orig" ] || cp "$CLIENT_UTILS" "$CLIENT_UTILS.orig"
    "$PY" - "$SCRATCH" "$CLIENT_UTILS" <<'PYEOF'
import re, sys
scratch, cu = sys.argv[1], sys.argv[2]
s = open(scratch).read()
old = "doc = await self._client.open(p, text=self.header, wait=False)"
if "warm_text" not in s:
    assert s.count(old) == 1, "scratch.py anchor not found"
    s = s.replace(old, 'doc = await self._client.open(p, text=getattr(self, "warm_text", self.header), wait=False)')
    open(scratch, "w").write(s)
c = open(cu).read()
if "warm_text" not in c:
    m = re.search(r'name_prefix="_mcp_serial" if serial else "_mcp_scratch",
        \)
', c)
    assert m, "client_utils.py anchor not found"
    c = c[:m.end()] + '        pool.warm_text = os.environ.get("LEAN_SCRATCH_WARM_HEADER", "import Mathlib\n")
' + c[m.end():]
    if "
import os
" not in c:
        c = c.replace("import asyncio
", "import asyncio
import os
", 1)
    open(cu, "w").write(c)
PYEOF
    rm -f "$(dirname "$SCRATCH")"/__pycache__/scratch.*.pyc "$(dirname "$CLIENT_UTILS")"/__pycache__/client_utils.*.pyc
    grep -q 'warm_text' "$SCRATCH" && grep -q 'warm_text' "$CLIENT_UTILS" || die "could not apply the scratch warm_text patch"
    ok "scratch pools now warm with the project header (backups $SCRATCH.orig, $CLIENT_UTILS.orig)"
  fi
  # lean_local_search runs ripgrep over the project root to find declarations by name, and both
  # Lean projects here (the coding agent's workspace and the harness's per-problem project) reach
  # Mathlib and cslib through a SYMLINK `.lake/packages -> <built project>/.lake/packages`.
  # ripgrep does not follow symlinks unless told to, so without `--follow` that leg of the search
  # sees NO library declarations at all (measured: 0 hits for `Bisimilarity`, 3 with --follow) and
  # the tool is left with whatever the language server has indexed from the open file's imports.
  # One flag, idempotent, re-applied after any pip install like the two patches above.
  local SEARCH_UTILS
  SEARCH_UTILS=$(find "$AIP_MCP_VENV" -path '*/lean_lsp_mcp/search_utils.py' -print -quit)
  [ -n "$SEARCH_UTILS" ] || die "lean_lsp_mcp/search_utils.py not found in $AIP_MCP_VENV"
  if grep -q '"--follow",' "$SEARCH_UTILS"; then
    ok "lean_local_search follows the .lake/packages symlink (--follow patch present)"
  else
    [ -f "$SEARCH_UTILS.orig" ] || cp "$SEARCH_UTILS" "$SEARCH_UTILS.orig"
    "$PY" - "$SEARCH_UTILS" <<'PYEOF2'
import sys
p = sys.argv[1]; s = open(p).read()
old = '        "rg",\n        "--json",\n        "--no-ignore",\n'
assert s.count(old) == 1, "search_utils.py anchor not found"
open(p, "w").write(s.replace(old, '        "rg",\n        "--json",\n        "--follow",\n        "--no-ignore",\n'))
PYEOF2
    rm -f "$(dirname "$SEARCH_UTILS")"/__pycache__/search_utils.*.pyc
    grep -q '"--follow",' "$SEARCH_UTILS" || die "could not apply the --follow patch to $SEARCH_UTILS"
    ok "lean_local_search now follows the .lake/packages symlink (backup $SEARCH_UTILS.orig)"
  fi
}

step_rg() {
  say "ripgrep (lean_local_search needs it)"
  local dir="${AIP_RG_DIR:-$HOME/.local/bin}"
  if PATH="$dir:$PATH" command -v rg >/dev/null; then ok "$(PATH="$dir:$PATH" command -v rg)"; return 0; fi
  mkdir -p "$dir"
  local T; case "$(uname -m)" in
    x86_64) T=x86_64-unknown-linux-musl ;; aarch64) T=aarch64-unknown-linux-gnu ;;
    *) die "unknown arch $(uname -m): install ripgrep into $dir yourself" ;; esac
  local TMP; TMP=$(mktemp -d)
  curl -sSL --max-time 180 "https://github.com/BurntSushi/ripgrep/releases/download/${RG_VERSION}/ripgrep-${RG_VERSION}-${T}.tar.gz" -o "$TMP/rg.tgz"
  tar xzf "$TMP/rg.tgz" -C "$TMP" && install -m 0755 "$TMP"/ripgrep-*/rg "$dir/rg" && rm -rf "$TMP"
  ok "installed $dir/rg -- make sure [paths].rg_dir in aiprover.toml points at $dir"
}

link_config() {
  # An INSTALLED Claude Code plugin runs from a cache copy, which cannot find aiprover.toml by
  # walking up; this is where aiprover.py looks next.
  mkdir -p "$HOME/.config/aiprover"
  ln -sfn "$ROOT/aiprover.toml" "$HOME/.config/aiprover/aiprover.toml"
  ok "~/.config/aiprover/aiprover.toml -> $ROOT/aiprover.toml"
}

step_claude() {
  say "Claude Code: plugin 'aiprover' (skill + lean-lsp MCP server)"
  command -v claude >/dev/null || die "claude CLI not found"
  link_config
  claude plugin marketplace add "$ROOT" >/dev/null 2>&1 || claude plugin marketplace update aiprover-local >/dev/null 2>&1 || true
  # Reinstall rather than `update`: Claude Code runs an installed plugin from a cached COPY and
  # refreshes that copy only when plugin.json's version changes, so an edited skill would
  # otherwise keep running stale.
  if claude plugin list 2>/dev/null | grep -q 'aiprover@aiprover-local'; then
    claude plugin uninstall aiprover@aiprover-local >/dev/null 2>&1 || true
  fi
  claude plugin marketplace update aiprover-local >/dev/null 2>&1 || true
  claude plugin install aiprover@aiprover-local --scope user >/dev/null
  claude plugin list 2>/dev/null | grep -q 'aiprover@aiprover-local' || die "plugin install failed"
  ok "installed (user scope) from the current files"
  echo "   (without installing: claude --plugin-dir $ROOT/claude_code ...;"
  echo "    Agent SDK: ClaudeAgentOptions(plugins=[{\"type\": \"local\", \"path\": \"$ROOT/claude_code\"}]))"
}

step_codex() {
  say "Codex: skill in ~/.agents/skills + MCP server 'lean-lsp'"
  local CODEX; CODEX=$(command -v codex || ls -1 "$HOME"/.vscode-server/extensions/openai.chatgpt-*/bin/linux-*/codex 2>/dev/null | tail -1 || true)
  [ -n "$CODEX" ] && [ -x "$CODEX" ] || die "codex CLI not found"
  link_config
  mkdir -p "$HOME/.agents/skills"
  ln -sfn "$CX_SKILL" "$HOME/.agents/skills/$SKILL"
  ok "~/.agents/skills/$SKILL -> $CX_SKILL"
  "$CODEX" mcp remove lean-lsp >/dev/null 2>&1 || true
  "$CODEX" mcp add lean-lsp -- "$CX_SKILL/scripts/aiprover" mcp-serve >/dev/null
  # Lean tools can legitimately take minutes (first file elaboration, lean_build).
  "$PY" - "$HOME/.codex/config.toml" <<'EOF'
import re, sys
p = sys.argv[1]; s = open(p).read()
hdr = "[mcp_servers.lean-lsp]"
i = s.index(hdr) + len(hdr)
nxt = re.search(r"^\[", s[i:], re.M)
block = s[i:i + nxt.start()] if nxt else s[i:]
block = re.sub(r"^(startup_timeout_sec|tool_timeout_sec)\s*=.*\n", "", block, flags=re.M)
block = block.rstrip("\n") + "\nstartup_timeout_sec = 120\ntool_timeout_sec = 600\n\n"
s = s[:i] + block + (s[i + nxt.start():] if nxt else "")
open(p, "w").write(s)
EOF
  ok "registered: $("$CODEX" mcp list 2>/dev/null | grep lean-lsp | tr -s ' ')"
  echo "   run Codex with --sandbox danger-full-access (see STARTUP.md)"
}

step_doctor() {
  say "doctor --full --agents"
  "$AIP" doctor --full --agents
}

# ---------------------------------------------------------------------------
PY=$(command -v python3)
"$PY" -c 'import sys; sys.exit(sys.version_info < (3, 11))' || die "python3 >= 3.11 required"
load_config
[ $# -eq 0 ] && set -- all
for step in "$@"; do
  case "$step" in
    all)    step_sync; step_elan; step_lean_project; step_cslib; step_venvs; step_rg; step_claude; step_codex; step_doctor ;;
    deps)   step_elan; step_lean_project; step_cslib; step_venvs; step_rg ;;
    sync)   step_sync ;;
    lean)   step_elan; step_lean_project; step_cslib ;;
    cslib)  step_cslib ;;
    venvs)  step_venvs ;;
    rg)     step_rg ;;
    claude) step_claude ;;
    codex)  step_codex ;;
    doctor) step_doctor ;;
    *) die "unknown step '$step' (all|deps|sync|lean|cslib|venvs|rg|claude|codex|doctor)" ;;
  esac
done
