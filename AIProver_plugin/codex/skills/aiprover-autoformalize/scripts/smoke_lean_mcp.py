#!/usr/bin/env python3
"""Drive the coding agent's lean-lsp MCP server EXACTLY as the agent does, and call every tool.

    <mcp_venv>/bin/python3 smoke_lean_mcp.py <python> <aiprover.py> <workspace>

The server is started through `aiprover mcp-serve` -- the same launcher the Claude Code plugin's
.mcp.json and the Codex config.toml point at -- so a PASS here means the agent's tool works,
not merely that the package imports. Beyond "no error", the core tools are checked for the
RIGHT answer (the goal text, a closing tactic, a real lemma name), because a tool that returns
something plausible but wrong costs more turns than one that errors.

Run with the MCP venv's interpreter: it carries the `mcp` client library.
"""
import asyncio
import os
import sys
from pathlib import Path

PY, CLI, WS = sys.argv[1], sys.argv[2], Path(sys.argv[3])
REL = "work/_AIProverSmoke.lean"
SRC = """import Mathlib

theorem smoke_add_comm (a b : Nat) : a + b = b + a := by
  sorry
"""
SORRY_LINE, SORRY_COL, THM_LINE = 4, 3, 3

# tool -> (arguments, substring the answer must contain or None, core?)
CASES = {
    "lean_diagnostic_messages": ({"file_path": REL}, "sorry", True),
    "lean_goal": ({"file_path": REL, "line": SORRY_LINE, "column": SORRY_COL}, "a + b = b + a", True),
    "lean_term_goal": ({"file_path": REL, "line": THM_LINE, "column": 38}, None, True),
    "lean_hover_info": ({"file_path": REL, "line": THM_LINE, "column": 11}, None, True),
    "lean_completions": ({"file_path": REL, "line": THM_LINE, "column": 20}, None, True),
    "lean_declaration_file": ({"file_path": REL, "symbol": "Nat"}, None, True),
    "lean_references": ({"file_path": REL, "line": THM_LINE, "column": 11}, None, True),
    "lean_file_outline": ({"file_path": REL}, "smoke_add_comm", True),
    "lean_code_actions": ({"file_path": REL, "line": SORRY_LINE, "column": SORRY_COL}, None, True),
    "lean_run_code": ({"code": "import Mathlib\ntheorem t (a b : Nat) : a + b = b + a := by omega"},
                      None, True),
    "lean_multi_attempt": ({"file_path": REL, "line": SORRY_LINE,
                            "snippets": ["omega", "exact Nat.add_comm a b", "ring"]}, "omega", True),
    "lean_verify": ({"file_path": REL, "theorem_name": "smoke_add_comm"}, None, True),
    "lean_minimal_hypotheses": ({"file_path": REL, "theorem_name": "smoke_add_comm"}, None, True),
    "lean_profile_proof": ({"file_path": REL, "line": THM_LINE, "column": 11}, None, True),
    "lean_local_search": ({"query": "add_comm", "limit": 5}, "add_comm", True),
    "lean_build": ({}, None, True),
    "lean_get_widgets": ({"file_path": REL, "line": SORRY_LINE, "column": SORRY_COL}, None, True),
    # hosted services: need outbound internet; reported, not required
    "lean_leansearch": ({"query": "commutativity of addition on naturals", "num_results": 3}, None, False),
    "lean_loogle": ({"query": "Nat.add_comm", "num_results": 3}, None, False),
    "lean_leanfinder": ({"query": "addition is commutative", "num_results": 3}, None, False),
    "lean_state_search": ({"file_path": REL, "line": SORRY_LINE, "column": SORRY_COL,
                           "num_results": 3}, None, False),
    "lean_hammer_premise": ({"file_path": REL, "line": SORRY_LINE, "column": SORRY_COL,
                             "num_results": 8}, None, False),
}


async def main() -> int:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    (WS / REL).parent.mkdir(parents=True, exist_ok=True)
    (WS / REL).write_text(SRC)
    # env passed EXPLICITLY: the mcp client otherwise gives the server only a minimal default
    # environment, dropping $AIPROVER_CONFIG -- and the smoke would test some other config's venv.
    params = StdioServerParameters(command=PY, args=[CLI, "mcp-serve"], env=dict(os.environ))
    core_fail, ext_fail, passed, skipped = [], [], [], []
    async with stdio_client(params) as (r, w):
        async with ClientSession(r, w) as s:
            await s.initialize()
            published = [t.name for t in (await s.list_tools()).tools]
            print(f"server publishes {len(published)} tools (config: "
                  f"{os.environ.get('AIPROVER_CONFIG', 'default search')})")
            for name in published:
                if name not in CASES:
                    skipped.append(name)
                    print(f"  SKIP  {name} (needs another tool's output)")
                    continue
                args, want, core = CASES[name]
                try:
                    out = await asyncio.wait_for(s.call_tool(name, args), timeout=300)
                    txt = " ".join((c.text if getattr(c, "text", None) else str(c))
                                   for c in out.content)
                    bad = out.isError if hasattr(out, "isError") else getattr(out, "is_error", False)
                    bad = bad or txt.lstrip().lower().startswith(("error", "traceback"))
                    if not bad and want and want not in txt:
                        bad, txt = True, f"answer lacks {want!r}: {txt[:120]}"
                except Exception as e:                              # noqa: BLE001
                    bad, txt = True, f"{type(e).__name__}: {e}"
                tag = "PASS" if not bad else ("FAIL" if core else "WARN")
                (passed if not bad else core_fail if core else ext_fail).append(name)
                print(f"  {tag}  {name:26s} {txt[:90].replace(chr(10), ' ')}")
    (WS / REL).unlink(missing_ok=True)
    print(f"MCP-SMOKE: {len(passed)} PASS, {len(core_fail)} core FAIL {core_fail or ''}, "
          f"{len(ext_fail)} hosted-service WARN {ext_fail or ''}, {len(skipped)} skipped")
    return 1 if core_fail else 0


sys.exit(asyncio.run(main()))
