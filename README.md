# AIProver

AIProver turns a natural-language theorem **and its proof** into a Lean 4 file that compiles, has
no `sorry`, states exactly that theorem and follows that proof. It is a fine-tuned Leanstral-class
prover driven by an evolved agentic harness (Lean 4.23.0, Mathlib, cslib, the lean-lsp tools),
packaged so it can be used in three ways:

| mode | what you run | who judges the result |
|---|---|---|
| **standalone** | `bin/aiprover` (submit / wait / result / check / probe / search) | you |
| **Claude Code plugin** | Claude Code with the `aiprover-autoformalize` skill | Claude Code: plans, delegates Lean work to AIProver, judges faithfulness, decomposes and weaves |
| **Codex skill** | Codex with the same skill | Codex, likewise |

Everything lives in [`AIProver_plugin/`](AIProver_plugin/). The model itself runs on a GPU server
you point the plugin at; the harness, the Lean toolchain and the tools run on your machine.

## 1. Set up

Follow [`AIProver_plugin/README.md`](AIProver_plugin/README.md) ("Quick start"). In short:

1. `cd AIProver_plugin` and edit `aiprover.toml`: `[endpoint]` says where the model server is
   (an SSH host and the vLLM port, or a direct `api_base`), `[paths]` where Lean, the venvs and
   ripgrep live or should be built.
2. `./setup.sh` -- installs what is missing (elan + Lean 4.23.0, Mathlib, cslib, two Python venvs,
   ripgrep), installs the Claude Code plugin and the Codex skill, and ends with
   `bin/aiprover doctor --full --agents`. All rows `PASS` means every layer works for real.
   Already installed and updating? See "Startup after updating" in the same README.
3. Any time later: `bin/aiprover doctor` (about 40 s). If a row fails,
   [`AIProver_plugin/STARTUP.md`](AIProver_plugin/STARTUP.md) §5 maps it to its fix.

## 2. Write the problem

AIProver reads one text with two tagged blocks. The theorem block carries the statement with the
definitions and assumptions it relies on; the proof block carries the proof, intermediate lemmas
included. LaTeX is fine. Save it as `problem.txt`:

```text
<informal_theorem>
Let $G$ be a group and let $a, b \in G$. If $ab = ba$, then for every natural number $n$,
$(ab)^n = a^n b^n$.
</informal_theorem>

<informal_proof>
By induction on $n$. For $n = 0$ both sides equal $e$. Assume $(ab)^n = a^n b^n$. Then
$(ab)^{n+1} = (ab)^n (ab) = a^n b^n a b$. Since $ab = ba$, also $b^n a = a b^n$ (by an
inner induction on $n$, using $ba = ab$ at each step), so $a^n b^n a b = a^n a b^n b =
a^{n+1} b^{n+1}$.
</informal_proof>
```

Leave the proof block empty to ask for the **statement only** (the answer then ends in `sorry`).

## 3. Use it

### Standalone (no coding agent)

```bash
cd AIProver_plugin
bin/aiprover doctor                                   # once per session
bin/aiprover expand --problem problem.txt --out problem.expanded.txt   # optional: the model rewrites the
                                                      #   proof as explicit numbered steps (method kept); read it
bin/aiprover submit --problem problem.expanded.txt -k 4 --name demo   # 4 independent attempts; prints JOB
bin/aiprover wait JOB --timeout 540                   # rc 0 = done, rc 3 = still running (repeat)
bin/aiprover result JOB                               # per-attempt status + the best Lean file
bin/aiprover check ~/.aiprover/jobs/JOB/s0.lean       # (a) compiles, (b) no placeholder, by the kernel
bin/aiprover probe ~/.aiprover/jobs/JOB/s0.lean       # is the statement FALSE as written? closed by simp alone?
bin/aiprover backtranslate ~/.aiprover/jobs/JOB/s0.lean   # the model says in English what the Lean states: compare with T
bin/aiprover search "bisimulation transitive"         # library declarations by concept (cslib; --lib mathlib|loogle|leansearch|leandex)
bin/aiprover extract ~/.aiprover/jobs/JOB/s0.lean --line 27   # a stuck step (a `sorry`) as a standalone lemma to delegate
```
Pieces of a larger problem can be fixed in Lean: `--context defs.lean` (declarations the answer
must contain verbatim) and `--lean-statement stmt.lean` (the exact statement to prove), plus
`--hint`/`--hint-file` for guidance. `bin/aiprover --help` and `submit --help` list everything.
Judging that the Lean says what the text says is yours in this mode: `check` and `probe` are
mechanical, and `expand`/`backtranslate`/`ask` are drafts from AIProver's own model (a Lean
specialist, not a frontier model) to help you read, not verdicts.

### With Claude Code

Start Claude Code anywhere (the plugin is installed at user scope) and give it the problem; the
skill triggers on the tagged blocks:

```text
claude
> Formalize this in Lean 4 with AIProver. The file must compile, contain no sorry, state exactly
> the theorem and follow the proof.
>
> <informal_theorem> ... </informal_theorem>
> <informal_proof> ... </informal_proof>
```
or non-interactively: `claude -p "$(cat prompt.txt)"` where `prompt.txt` holds the same text.
Claude Code then runs `doctor`, makes the proof explicit (its own model does the informal work;
no other LLM or key is involved), submits whole-problem jobs, probes and judges the candidates,
and -- if none is faithful and complete -- freezes a skeleton, submits one job per lemma,
extracting stuck steps as lemmas, weaves the proofs back and gates the final file. If you need a specific output
format, say so in the prompt (for example: `<formal_proof>` around one ```` ```lean4 ```` fence).

### With Codex

Codex's default sandbox cannot reach the model server, so start it with full access:

```bash
codex --sandbox danger-full-access
```
then give it the same prompt as above. Non-interactively:
`codex exec --sandbox danger-full-access "$(cat prompt.txt)"`. The procedure is identical; the
skill tells Codex how to wait on jobs cheaply.

### What comes back

One self-contained Lean 4 file: `import Mathlib` (and a `Cslib.*` module when the theorem is about
transition systems, process or lambda calculi, combinatory or linear logic), your definitions,
the lemmas of the proof and the theorem. The coding agent reports that all four properties hold;
standalone, `check` certifies the first two and `probe` screens the statement.

## Layout

| path | what |
|---|---|
| `AIProver_plugin/README.md` | setup, startup after updating, what is new |
| `AIProver_plugin/STARTUP.md` | the runbook: every doctor check, every fix, known limits |
| `AIProver_plugin/claude_code/` | the Claude Code plugin (skill + lean-lsp MCP server) |
| `AIProver_plugin/codex/` | the Codex skill (same scripts and harness) |
| `AIProver_plugin/.../references/playbook.md` | how the coding agent decomposes, probes, searches and judges |

## License

MIT, see [LICENSE](LICENSE).
