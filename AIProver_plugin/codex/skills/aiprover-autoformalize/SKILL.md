---
name: aiprover-autoformalize
description: Proof auto-formalization into Lean 4 (v4.23.0 + Mathlib, plus cslib for computer-science notions) with the AIProver agent -- our fine-tuned Leanstral prover driven by an evolved agentic harness. Use whenever you are given a natural-language theorem with its proof (e.g. <informal_theorem>/<informal_proof> blocks) and must produce a Lean 4 formalization that compiles, has no sorry, states exactly the theorem, and follows the proof. Delegate Lean writing and proof search to AIProver; you plan, judge, decompose and weave.
---

# AIProver: proof auto-formalization

You turn a natural-language pair  M = ⟨T, P⟩  (a theorem T, possibly in several parts, with the
definitions and assumptions it relies on, and its proof P, possibly through intermediate lemmas)
into ONE self-contained Lean 4 file ⟨T̂, P̂⟩ that is **equivalent** to it. The NL pair is your
only input. Four properties, ALL required:

| | property | who certifies |
|---|---|---|
| (a) | **Type-correct**: Lean's kernel accepts the file (Lean v4.23.0, Mathlib v4.23.0, `import Mathlib`) | `aiprover check` |
| (b) | **Complete**: no `sorry`, `admit`, empty `by`, or any other placeholder -- anywhere, including helper lemmas and `def`s | `aiprover check` (kernel axiom probe) |
| (c) | **Semantically correct**: T̂ states exactly T under the same definitions -- no added assumptions, no dropped conditions, every part | **you**, with the judge protocol below |
| (d) | **Proof-faithful**: P̂ follows P's strategy, including its intermediate lemmas, with no new assumptions | **you**, with the judge protocol below |

**You do not stop until all four hold.** (a) and (b) are mechanical; (c) and (d) are undecidable
and you are the judge. A file that compiles is not an answer.

## Who does what

**AIProver** = our fine-tuned Leanstral model inside the evolved hevo harness (champion
`d01_r04`). One call is a full agentic Lean session of up to 200 turns (the champion was measured
at 100; the extra budget serves runs that hold a correct statement with an unfinished proof): it
writes the file,
compiles it, searches Mathlib, reads goals and repairs, with the lean-lsp tools. It is strong at
writing Lean and closing proofs. On 509 hard training problems it produced a solved, faithful
formalization in 205 cases -- and in **173 more its file compiled but stated the WRONG theorem**.
It cannot reliably judge its own statement. Five evolution rounds tried to teach it to; all failed.

**Division of labour -- this is how you save frontier tokens without losing accuracy:**
- AIProver writes Lean and searches for proofs. Send it the whole problem first, then pieces.
  Sampling is cheap for it (our GPUs) and expensive for you, so ask for several samples rather
  than doing the search yourself.
- You read the NL carefully, plan, **judge (c) and (d)**, fix statements, decompose, weave the
  pieces, and make small repairs. Do not grind through tactic search yourself while AIProver can
  do it. Do not read AIProver's trajectories. `aiprover result` gives you everything you need.
- While jobs run, WAIT (`aiprover wait`). Waiting costs nothing, and polling or idle exploration
  costs tokens.

## The commands

`AIP=<this skill's directory>/scripts/aiprover` -- the skill's base directory is given to you when
this skill loads. Every command prints a short summary; add `--json` where noted for the full record.

```
$AIP doctor                        # once per session, first. All PASS or read STARTUP.md
$AIP submit --problem FILE -k 4 --name main      # prints JOB id, returns at once
$AIP submit --theorem-text "..." --proof-text "..." [--context C.lean] [--lean-statement S.lean] [--hint "..."] [--statement-only] -k 2
$AIP wait JOB [JOB...] --timeout 540 [--any]     # blocks <= 9 min; rc 0 done, rc 3 still running
$AIP result JOB [--all] [--json]   # per-sample status + best Lean file + its check
$AIP check FILE.lean [--statement-only] [--fixed C.lean]   # (a)+(b); rc 0 = PASS
$AIP probe FILE.lean               # statement sanity: counterexample search + automation closers (~5 s)
$AIP search "words" [--lib cslib|mathlib|all|loogle|leansearch|leandex]   # library search (local pinned, or hosted)
$AIP extract FILE.lean --line N [--name L]   # the goal at that `sorry` as a standalone lemma, binders written by Lean
$AIP workspace --new NAME          # path for YOUR Lean file inside the lean-lsp project
$AIP status | list | cancel JOB
```

- A job runs `-k` independent AIProver samples in parallel, typically 5-40 min each (up to 180
  at the default 3 h cap; `--max-turns`/`--timeout` set a job's own budget).
  **Waiting, cheaply:** start ONE command `$AIP wait JOB... --timeout 3300` and, when your shell
  call yields with it still running, keep polling that same session with the longest wait
  allowed and NO commentary between polls -- `wait` prints nothing until the jobs finish, so
  each poll costs almost nothing. rc 3 means the timeout passed with jobs still running: start
  another `wait`. Nothing is lost between waits; jobs run detached from your shell.
- Sample status, best first: `verified` (passes (a)+(b); still needs YOUR (c)/(d) judgement),
  `sorry` (elaborates but has a placeholder), `rejected` (compiles, but a disqualifying
  construct or axiom), `error` (does not compile), `empty`, `infra`.
- `--context C.lean`: declarations the answer must contain VERBATIM (your fixed definitions,
  lemma statements with `sorry` as given facts). `--lean-statement S.lean`: the fixed statement
  to prove (`... := by sorry`). `result` reports `fixed-code:kept` or `fixed-code:CHANGED`. Treat
  CHANGED as a failed sample unless the change is harmless and you adopt it deliberately.
- `--statement-only` sends an empty proof block: AIProver formalizes the statement alone
  (a `sorry` proof is the complete answer there). This is useful for drafting T̂ quickly.
- `--hint` passes one line of guidance, e.g. the compiler error to fix or the Mathlib lemma to use.
  `--hint-file F` passes longer guidance: the goal state where the last attempt got stuck, the
  exact error, the lemma names you found. Use it on every resubmission (step 4d).
- `probe` rewrites every theorem's proof as `plausible` (Mathlib's random tester) and tries the
  closers `decide simp omega norm_num aesop grind` on each statement alone. `COUNTEREXAMPLE`
  means the statement is FALSE as written -- a dropped hypothesis, a narrowed or widened
  quantifier, ℕ subtraction or floor division where T means ℤ/ℚ/ℝ -- so (c) fails before any
  proof work; `closed by automation alone` is the "not vacuous" clause of the judge made
  mechanical. `untestable` (abstract types, undecidable relations) and `no counterexample` prove
  nothing. Run it on every candidate and every skeleton before you judge.
- `search` is for the concept when the name is unknown ("bisimulation transitive", "confluence
  full beta"): every word must occur in the name, header, docstring or module path; hits print the
  exact `import` line. `--lib loogle|leansearch|leandex` query the hosted indexes (newer Mathlib:
  confirm names locally). `lean_local_search` already finds names by prefix across Mathlib AND
  cslib, and the lean-lsp `lean_loogle`/`lean_leansearch`/`lean_leanfinder` tools are the
  rate-limited path to the same hosted services -- prefer them over `search --lib loogle` here.
- `extract` isolates a stuck step: point it at the `sorry` standing for the step and Lean's
  `extract_goal` writes the lemma with the exact local context as binders (universes, instances,
  earlier `have`s included). Paste it above the theorem, close the step with it, delegate it alone.
- `expand`, `backtranslate`, `ask` call an LLM. Inside this session that LLM is YOUR OWN model in a
  fresh headless process (`--backend auto`), so they cost your tokens and know nothing of this
  conversation. Use that: `$AIP backtranslate FILE.lean` IS the blind back-translation of the
  judge protocol -- a reader that has never seen T cannot be anchored by it. `expand` is a
  convenience for step 1b when you prefer not to write the steps out yourself. Standalone users
  get AIProver's own model instead.

**lean-lsp MCP tools** (server `lean-lsp`: `lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`,
`lean_run_code`, `lean_local_search`, `lean_loogle`, `lean_leansearch`, `lean_hover_info`,
`lean_verify`, `lean_state_search`, `lean_hammer_premise`, ...) are available to you for quick
local work: checking a goal, trying a tactic, confirming a lemma name, reading a definition,
retrieving premises for a goal. Files must live in the project that `$AIP workspace --new NAME`
points into. Use them for cheap targeted checks, not for long proof searches (delegate those).

**Libraries.** The project pins Mathlib `v4.23.0` and **cslib** (the Lean library for Computer
Science, at its last Lean-4.23.0 commit: lambda calculus, combinatory logic, labelled transition
systems and bisimulation, CCS, linear logic). When T is about such notions, search cslib
(`$AIP search`, `lean_local_search`) and import the module a hit lives in -- `import Cslib`
alone loads only a few modules. Import cslib only when the problem needs it and the environment
that will compile your answer has it (this plugin's project does; a plain Mathlib checker does
not). Both AIProver and `check` accept `Cslib.*` imports.

## The procedure

**0. Preflight.** `$AIP doctor` (about 40 s). If anything FAILs, stop and follow STARTUP.md
(doctor prints its path). Do not work around a broken environment. AIProver needs
network access to 127.0.0.1 and to its SSH host, and write access to `~/.aiprover`. Run Codex
with `--sandbox danger-full-access` (on hosts where bubblewrap cannot create a network
namespace, `workspace-write` cannot run any command at all).

**1. Read and blueprint.** Write the NL input to a file (`problem.txt`, with the
`<informal_theorem>`/`<informal_proof>` blocks exactly as given). Then list, briefly:
definitions D1..; theorem parts T1..Tk with their exact hypotheses; the proof's intermediate
lemmas L1..Lm and how the main argument uses them. Resolve ambiguity now: which number type
(ℕ/ℤ/ℚ/ℝ), what "positive"/"nonzero" range, 0- or 1-indexing, which Mathlib notion each named
concept is.

**1b. Make P explicit before anyone formalizes it.** AIProver follows P as written, so a gap in P
becomes a gap in P̂. Where P says "similarly", "clearly", "by induction" without the induction
hypothesis, "by the usual argument", or skips a case, write the missing steps out yourself:
numbered atomic steps, each naming the fact or rule it uses, every case of a case split listed.
Keep P's METHOD and its intermediate lemmas exactly (that is (d)); expand, never replace. Send
this expanded proof as the `<informal_proof>` block (or `--proof-text`), and keep the original P
beside it for the judge. Also pin notation that P leaves implicit (which type the variables
range over, what "divides" or "≤" means for the objects at hand). This is the single cheapest
thing you can do for AIProver's success rate.

**2. Delegate the whole problem at once.** `$AIP submit --problem problem.txt -k 4 --name whole`,
then `wait`. For a long problem (many parts or lemmas) ALSO submit
`--statement-only -k 2 --name stmt` at the same time, so you get statement drafts to judge early.

**3. Probe, then judge every `verified` sample**, best first. `$AIP probe s<i>.lean` first: a
`COUNTEREXAMPLE` fails (c) outright (keep the file only as a draft); `closed by automation
alone` on a theorem that should carry content is the narrowing smell -- check it hard. Then the
judge protocol. Take the first that passes (c) and (d). If none pass, keep what IS right: a faithful statement, correct definitions,
lemma statements, and proofs of some parts.

**4. If no sample is complete and faithful: fix the statement, then decompose.**
  a. Write the skeleton yourself (usually by correcting the best sample): definitions, every
     lemma Li of the NL proof and every theorem part Tj as a Lean statement with `:= by sorry`.
     `$AIP check --statement-only skeleton.lean` must PASS, `$AIP probe skeleton.lean` must show
     no counterexample, and the skeleton must pass the judge for (c) and for the lemma structure
     of (d). **Freeze it** -- from now on the statements do
     not change unless the judge finds a fault.
  b. Submit one job per open piece, all in parallel: `--context` = the frozen definitions plus
     the statements of the lemmas that piece may use (as `sorry`d givens); `--lean-statement` =
     the piece's own statement; `--theorem-text`/`--proof-text` = the NL for that piece only (its
     statement and its part of P). `-k 2`..`-k 4`. Give the main theorem's job the lemmas as
     givens, so its proof follows P's structure instead of re-deriving everything.
  c. Weave: paste each returned proof into the skeleton (take only the proof bodies; the
     statements are frozen). `$AIP check`. Fix small breakage yourself (a name clash, an `open`,
     a missing `import`) and check again.
  d. A piece that fails -- the ladder, in this order, one rung per round:
     1. **Resubmit with a structured hint** (`--hint-file`): the exact error, the goal state at the
        failing step (`lean_goal` on the best sample's file), and the lemma names you confirmed
        with `lean_local_search`/`$AIP search`/`lean_loogle`. `-k 4`.
     2. **Extract the stuck step as a lemma.** In the best sample's file replace the failing step
        by `sorry` (so the file elaborates) and run `$AIP extract FILE --line <that line>`: Lean
        writes the lemma with the exact context as binders. Paste it above the theorem, close the
        step with `exact <lemma> ..`, `check --statement-only`, `probe`, and submit the lemma
        ALONE (`--context` = the frozen definitions, `--lean-statement` = the lemma, NL = that
        step of P). AIProver solves small, fully-specified goals far more reliably than it finds
        its way through a long proof.
     3. **Split along P's own reasoning** (sub-lemmas for each step of P's argument), recurse,
        and weave back.
     4. Only after these: prove a small step yourself when it is a few lines.
     Never bypass the ladder by weakening the statement, and do not let a piece absorb more
     than ~3 rounds before you split it.

**5. Final gate** -- on the exact final file, in this order:
  1. `$AIP check final.lean` -> PASS (covers (a) and (b); warnings about a bare `trivial` proof
     must also be fixed, because the evaluation judge counts `trivial` as a placeholder).
  2. The full judge protocol, (c) and (d), on the final file.
  3. Only then answer.

Never deliver a file that fails any of the four. If you are stuck, go back to step 4 with a finer
split. Do not weaken the statement to make a proof go through; that trades an (a)/(b) failure
for a (c) failure, which is just as fatal and harder to see.

## Judge protocol for (c) and (d)

Do it in this order, because order matters: judging after re-reading the NL anchors you to what
the text meant rather than what the Lean says.

**(c) Semantic correctness.**
1. **Blind back-translation.** From the Lean alone -- every `def`, `structure`, instance argument,
   binder, hypothesis and conclusion -- write in plain English what T̂ asserts. Unfold local
   definitions. `$AIP backtranslate FILE.lean` does this in a fresh process of your own model that
   has not read T; prefer it to doing it in this context. WRITE IT DOWN before you look at T again, and translate what the Lean says, not
   what you expect it to say. Only then compare.
2. **Compare clause by clause** with T (read P too, since it can fix the meaning of notation):
   - every part of a multi-part theorem present, each with its own hypotheses;
   - same quantifiers, in the same order and scope; ∃ vs ∃!; for-all vs for-some;
   - no extra hypothesis (including a stronger typeclass: `Field` for a ring, `Fintype`,
     `DecidableEq` that changes meaning, `Nonempty`, positivity) and no dropped one;
   - the conclusion neither weaker nor stronger (≤ vs <, ↔ vs →, pointwise vs as functions);
   - number types: ℕ subtraction truncates and ℕ/ℤ division floors -- is that what T means?
     Casts sit where T's arithmetic happens;
   - named notions: use the library's notion for what T NAMES ("idempotent", "countable",
     "subgroup generated by") and check its definition really is T's meaning. Formalizing the
     parenthetical gloss instead of the named notion, or a similarly-named neighbour, is the most
     common way AIProver's files compile yet are wrong;
   - definitions: T's own definitions formalized as defined (not replaced by an unfolded copy, not
     stubbed, conventions such as `1/0 = 0` preserved); indexing (0- vs 1-based, `Fin n` vs a
     list of length n) and edge cases (empty, zero, n = 1) agree;
   - not vacuous: hypotheses are satisfiable, and the statement is not closed by
     `simp`/`tauto`/`decide` alone because it was narrowed or specialised.
3. Verdict: equivalent, or list each mismatch and fix it (in the skeleton, then re-run 4b for the
   affected pieces).

**(d) Proof faithfulness.**
- Each intermediate lemma of P appears as a Lean lemma (or a clearly labelled `have`) whose
  statement matches it, and the main proof USES them where P does.
- P's method is followed: induction where P inducts, contradiction where P argues by
  contradiction, the same case split and the same key constructions. Tactics like `simp`,
  `omega`, `linarith` or `positivity` finishing a routine step P also treats as routine are
  fine. Replacing P's whole argument with a different one (brute-force `decide` over a case P
  handles conceptually, or a Mathlib lemma that IS the theorem when P proves it) is not.
- No new assumptions: no `axiom`, no extra hypotheses on helper lemmas that P does not have, no
  `sorry` anywhere (already checked by (b)).

## The answer

- ONE self-contained Lean 4 file: `import Mathlib` (or Mathlib submodules; cslib modules only
  when the problem needs them, see Libraries), your definitions, lemmas and theorems, with no
  reference to files of your own. It must PASS `$AIP check`.
- If the request specifies an output format, follow it EXACTLY. The step1 evaluation, for
  example, wants nothing but
  `<formal_proof>` + one ```` ```lean4 ```` fence holding the whole file + `</formal_proof>`.
  Otherwise print the file in a ```` ```lean4 ```` block and state that all four checks pass.

More detail -- decomposition worked through on an example, AIProver's measured failure modes,
how to make P explicit, what `probe` output means, the lemma-extraction recipe, search order and
the tactic rules that keep P̂ faithful -- is in `references/playbook.md`. Read it the first time
you decompose.
