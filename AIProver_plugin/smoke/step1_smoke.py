#!/usr/bin/env python3
"""End-to-end smoke: one problem through a coding agent WITH the AIProver skill, exactly as step1.

    ~/lean_env/bin/python3 smoke/step1_smoke.py --agent claude --problem P.txt --out DIR [--model M]
    ~/lean_env/bin/python3 smoke/step1_smoke.py --agent codex  --problem P.txt --out DIR

What is reproduced from step1 (llm_inferAndEval/gpu_inference.py), not reimplemented:
    the user prompt        gpu_inference.wrapPromptInQuery(<the NL pair>)
    the system prompt      gpu_inference.CLAUDE_SYSTEM_PROMPT
    answer extraction      gpu_inference.extract_fl_proof(<final text>)
    claude options         claude_sdk_utils.build_claude_code_options with AIPROVER=1
Codex: the openai-codex SDK is used when importable (step1's path); otherwise `codex exec` with
the same sandbox, system-prompt suffix and prompt -- the SDK drives the same binary.

Then the extracted file goes through `aiprover check`. Writes DIR/{final.txt, answer.lean,
check.txt, run.json} and prints a one-line verdict. Needs the Python that step1 uses (lean_env).
"""
from __future__ import annotations

import argparse
import asyncio
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
STEP1 = REPO / "llm_inferAndEval"
sys.path.insert(0, str(STEP1))
os.environ["AIPROVER"] = "1"
os.environ.setdefault("AIPROVER_PLUGIN_DIR", str(ROOT))

import gpu_inference as g                                              # noqa: E402
import claude_sdk_utils as cs                                          # noqa: E402

g.useExamplesInPrompt = False
g.examples = ""
AIP = ROOT / "bin" / "aiprover"


async def run_claude(prompt: str, model: str, cwd: Path) -> dict:
    import dataclasses
    from claude_agent_sdk import (AssistantMessage, ResultMessage, TextBlock, ToolUseBlock,
                                  query)
    opts = cs.build_claude_code_options(model, 15, g.CLAUDE_SYSTEM_PROMPT)
    opts = dataclasses.replace(opts, cwd=str(cwd))
    texts, tools, result = [], {}, {}
    log = open(cwd / "transcript.txt", "w")
    async for m in query(prompt=prompt, options=opts):
        if isinstance(m, AssistantMessage):
            for b in m.content:
                if isinstance(b, TextBlock):
                    texts.append(b.text)
                    log.write(f"\n[assistant] {b.text}\n")
                elif isinstance(b, ToolUseBlock):
                    tools[b.name] = tools.get(b.name, 0) + 1
                    log.write(f"\n[tool] {b.name} {json.dumps(b.input)[:600]}\n")
            log.flush()
        elif isinstance(m, ResultMessage):
            result = {"num_turns": m.num_turns, "total_cost_usd": m.total_cost_usd,
                      "usage": m.usage, "is_error": m.is_error, "result": m.result}
    final = result.get("result") or (texts[-1] if texts else "")
    return {"final": final, "tools": tools, **result}


def run_codex(prompt: str, model: str | None, cwd: Path) -> dict:
    system = g.CLAUDE_SYSTEM_PROMPT
    try:
        import codex_sdk_utils as cx                                    # noqa: F401
        import openai_codex                                             # noqa: F401
        outs = cx.query_codex(prompt=prompt, model=model, sandbox="full_access", n_samples=1,
                              system_prompt=system, workspace_root=str(cwd),
                              keep_workspaces=True)
        return {"final": outs[0], "via": "openai-codex SDK"}
    except ImportError:
        pass
    codex = shutil.which("codex") or sorted(Path.home().glob(
        ".vscode-server/extensions/openai.chatgpt-*/bin/linux-*/codex"))[-1]
    suffix = ("\n\nYou have the aiprover-autoformalize skill and the lean-lsp MCP tools. Use that "
              "skill for this task and follow its procedure: delegate Lean writing to AIProver, "
              "judge all four properties (type-correct, complete, semantically correct, "
              "proof-faithful), and iterate until they all hold. Then give your final answer in "
              "exactly the format the task requests.")               # == codex_sdk_utils
    full = f"{system}{suffix}\n\n{prompt}"
    cmd = [str(codex), "exec", "--skip-git-repo-check", "--sandbox", "danger-full-access",
           "--json", "-o", str(cwd / "final.txt"), "-C", str(cwd)]
    if model:
        cmd += ["-m", model]
    with open(cwd / "events.jsonl", "w") as ev:
        p = subprocess.run(cmd + [full], stdout=ev, stderr=subprocess.STDOUT, text=True,
                           timeout=6 * 3600)
    usage, tools = {}, {}
    for line in (cwd / "events.jsonl").read_text().splitlines():
        try:
            e = json.loads(line)
        except ValueError:
            continue
        if e.get("type") == "turn.completed":
            for k, v in (e.get("usage") or {}).items():
                usage[k] = usage.get(k, 0) + (v or 0)
        it = e.get("item") or {}
        if e.get("type") == "item.completed" and it.get("type") in ("command_execution",
                                                                     "mcp_tool_call"):
            k = it.get("type") + (":" + it.get("tool", "") if it.get("tool") else "")
            tools[k] = tools.get(k, 0) + 1
    final = (cwd / "final.txt").read_text() if (cwd / "final.txt").is_file() else ""
    return {"final": final, "via": "codex exec", "rc": p.returncode, "usage": usage,
            "tools": tools}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--agent", choices=["claude", "codex"], required=True)
    ap.add_argument("--problem", required=True, help="file with the NL pair (step1's input)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--model", default=None)
    a = ap.parse_args()
    out = Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    pair = Path(a.problem).read_text().strip()
    prompt = g.wrapPromptInQuery(pair)
    (out / "prompt.txt").write_text(prompt)
    t0 = time.time()
    if a.agent == "claude":
        rec = asyncio.run(run_claude(prompt, a.model or "claude-opus-5", out))
    else:
        rec = run_codex(prompt, a.model, out)
    rec["elapsed_sec"] = round(time.time() - t0, 1)
    (out / "final.txt").write_text(rec.get("final") or "")
    lean = g.extract_fl_proof(rec.get("final") or "")
    (out / "answer.lean").write_text(lean + "\n")
    chk = subprocess.run([str(AIP), "check", str(out / "answer.lean")], capture_output=True,
                         text=True)
    (out / "check.txt").write_text(chk.stdout + chk.stderr)
    rec["check_rc"] = chk.returncode
    rec["check"] = chk.stdout.splitlines()[0] if chk.stdout else chk.stderr[:200]
    rec["format_ok"] = ("<formal_proof>" in (rec.get("final") or "")
                        and "```lean4" in (rec.get("final") or ""))
    (out / "run.json").write_text(json.dumps({k: v for k, v in rec.items() if k != "final"},
                                             indent=1, default=str))
    print(f"SMOKE {a.agent}: check={rec['check']}  format_ok={rec['format_ok']}  "
          f"elapsed={rec['elapsed_sec']}s  turns={rec.get('num_turns')}  "
          f"cost={rec.get('total_cost_usd')}  usage={rec.get('usage')}  tools={rec.get('tools')}")
    return 0 if chk.returncode == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
