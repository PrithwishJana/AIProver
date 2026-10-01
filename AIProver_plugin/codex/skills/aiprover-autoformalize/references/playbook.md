# AIProver playbook

Read this the first time you decompose a problem. SKILL.md has the procedure; this has the
detail behind it.

## 1. What AIProver is, in numbers

The harness is `hevo_mixed_v1` champion `d01_r04`, selected over 10 rounds of harness evolution
on 509 hard LoCoLib training problems (algebraic structures, foundations/logic, number theory).
One sample of it, on that set:

| outcome | count | what it means for you |
|---|---|---|
| solved (faithful + complete) | 205 | still judge it, but usually right |
| compiles, complete, **unfaithful** | 173 | the trap: (a)+(b) pass, (c) fails |
| faithful statement, proof has `sorry` | 9 | keep the statement, delegate the proof piecewise |
| elaborates with `sorry`, statement unverified | 61 | salvage the parts that are right |
| does not elaborate | 61 | usually still has a useful statement draft |

So roughly 4 of 10 samples are right as they stand, and many more carry a correct statement or a
correct part. Several samples plus your judgement plus decomposition beats any single sample.
Median session is ~13 min (p90 ~40 min). The harness spends its last 18% of turns making the
file elaborate, so even a failed sample usually hands back a compiling skeleton with `sorry`s.

## 2. AIProver's measured failure modes -- check these first when judging

From the evolution run's error analysis, ordered by how often they cost a correct answer:

1. **Gloss instead of notion.** T says "e is idempotent (i.e. e² = e)" and the Lean inlines
   `e * e = e` instead of `IsIdempotentElem e`, or the reverse with the wrong library notion.
   Formalize the notion the text NAMES, and check with `lean_hover_info` that the library
   definition really is it.
2. **Under-specified / narrowed.** It proves one instance, a special case, or drops a hypothesis
   or a whole part of a multi-part theorem. It is especially tempted to do this when the
   automation check calls a statement trivial.
3. **Over-generalized.** A carrier given more structure than T grants (`Field` for a ring,
   `LinearOrder` added, a universe-polymorphic `Type*` where T fixes a concrete set), or a
   hypothesis silently strengthened.
4. **Wrong numeric type / coercion.** ℕ where T means ℤ or ℝ; truncated subtraction; floor
   division; casts in the wrong place.
5. **Definitions replaced.** A named definition from T replaced by an unfolded copy, or by a
   `def` that is stubbed or does not match (Mizar-style conventions such as `1/0 = 0` must be
   preserved).
6. **Representation drift.** `Fin n → α` vs `List α` of length n, 0- vs 1-based indexing,
   sets vs types, `Finset.range (n+1)` vs `Finset.Icc 1 n`.
7. **Disqualified constructs** (`native_decide`, `axiom`, `maxHeartbeats 0`): `check` catches
   these and marks the sample `rejected`.

## 3. Decomposition, worked through

Input (abridged): *"Let R be an abelian group. Define NatMul(n,a) = a+…+a (n times) and
IntMul(i,a) = NatMul(i,a) if i ≥ 0, NatMul(-i,-a) if i < 0. Then (1) if i ≤ j and k = j-i then
NatMul(k,a) = NatMul(j,a) - NatMul(i,a); (2) -NatMul(i,a) = NatMul(i,-a); (3) IntMul(i+j,a) =
IntMul(i,a) + IntMul(j,a). Proof: (1) by distributivity … (2) by induction on n … (3) by cases
on the signs of i and j, using (1) and (2)."*

**Step 2** (`submit --problem problem.txt -k 4`): suppose the best `verified` sample states
`NatMul`/`IntMul` as `def`s correctly and proves (1) and (2), but its (3) replaces `IntMul` by
`zsmul` (definition replaced -> (c) fails), and sample 2 has the right (3) statement with `sorry`.

**Step 4a**, `skeleton.lean` (you write it from the two samples):
```lean
import Mathlib

variable {R : Type*} [AddCommGroup R]

def NatMul : ℕ → R → R                             -- as T defines it: a + ... + a, n times
  | 0, _ => 0
  | n + 1, a => NatMul n a + a
def IntMul (i : ℤ) (a : R) : R := if 0 ≤ i then NatMul i.toNat a else NatMul (-i).toNat (-a)

theorem part1 (a : R) (i j k : ℕ) (hij : i ≤ j) (hk : k = j - i) :
    NatMul k a = NatMul j a - NatMul i a := by sorry
theorem part2 (a : R) (i : ℕ) : -NatMul i a = NatMul i (-a) := by sorry
theorem part3 (a : R) (i j : ℤ) : IntMul (i + j) a = IntMul i a + IntMul j a := by sorry
```
`check --statement-only skeleton.lean` passes and the skeleton passes your judge. Freeze it.

**Step 4b**, three jobs in parallel (parts 1 and 2 already have verified proofs in sample 1, so
only part 3 is actually needed here -- shown in full for the pattern):
```
# context for part3 = the defs + part1/part2 statements as givens
$AIP submit --name part3 -k 4 \
   --context ctx_part3.lean --lean-statement stmt_part3.lean \
   --theorem-text "Statement (3): for all integers i, j, IntMul(i+j,a) = IntMul(i,a) + IntMul(j,a)." \
   --proof-text  "By cases on the signs of i, j and i+j. When all are ≥ 0 this is additivity of NatMul ... use part (1) when the signs differ and part (2) to move negation inside."
```
`ctx_part3.lean` holds the `variable`, both `def`s and the `part1`/`part2` statements ending in
`:= by sorry`. `stmt_part3.lean` holds `theorem part3 ... := by sorry`. The returned file
contains all of these verbatim plus a real proof of `part3`. It may call `part1`/`part2`, which
is exactly P's structure.

**Step 4c**: paste the proof bodies into the skeleton, `check final.lean`, judge, answer.

Rules of thumb:
- One job per NL lemma is the natural grain. Split further only when a piece fails twice.
- Always hand a piece the lemmas P uses for it, as givens in `--context`, so AIProver follows
  P instead of inventing another route (that protects (d)) and has less to do.
- Keep NL for a piece self-contained: restate the notation it needs in `--theorem-text`. The
  context Lean pins the meaning, so the NL can be brief.
- A piece's proof may need a helper lemma P does not state. Accept it only if it is a routine
  step of P's argument and adds no hypothesis.
- `--statement-only -k 2` is a cheap second opinion when you are unsure how to state something.
  Judge its outputs like any other.

## 4. Reading `result`

```
job 2026...-whole  (theorem+proof)  counts: {'verified': 2, 'sorry': 1, 'error': 1}
  s2: verified  611.2s turns=34
  s0: verified  1022.4s turns=51
  s3: sorry     1840.0s turns=88 problems: placeholder (sorry/admit) reaches: main_thm
  s1: error     2011.7s turns=100 TIMEOUT problems: does not compile (see diagnostics)
===== s2 [verified]  ~/.aiprover/jobs/<job>/s2.lean
<the Lean file>
```
- Only the best sample's Lean is printed. `--all` prints every sample's file. Use it when the
  best one fails your judge, because a lower-ranked sample may have the faithful statement.
- Files stay on disk (`s<i>.lean`), so pass paths around rather than re-printing files.
- `infra` means the model endpoint failed (already retried once). Run `$AIP tunnel up` and
  `$AIP doctor`, then resubmit.

## 5. Small repairs you should do yourself

It is cheaper to fix these directly than to resubmit: a missing `open`/namespace, a renamed
Mathlib lemma (`lean_local_search` / `lean_loogle` to find the 4.23 name, `$AIP search` when you
know the concept but not the name), a universe or implicit-argument annotation, a duplicated
helper name between woven pieces, and weaving glue (`exact partK ...`). For one routine goal,
`lean_hammer_premise` / `lean_state_search` at the position return candidate lemmas and
`lean_multi_attempt` tries several closers in one call. Anything that needs real proof search,
delegate.

## 6. Lean / Mathlib / cslib versions

Lean `v4.23.0`, Mathlib `v4.23.0`, cslib at its last Lean-4.23.0 commit (`cd368e6`, 2025-09-15:
29 modules -- lambda calculus named and locally nameless, STLC safety, combinatory logic with
confluence, LTS with (weak, sw) bisimulation and trace equivalence, CCS, classical linear logic
with cut elimination, reduction systems). Everything compiles with ONE toolchain. Hosted search
tools (`lean_leansearch`, `lean_leanfinder`, `lean_loogle`) may return names from a newer
Mathlib, and cslib on GitHub today has ~250 modules on a newer Lean: neither can be imported
here. Confirm any name with `lean_local_search` or `lean_hover_info` (they read this project's
own libraries) before relying on it. `grind` exists on 4.23. `native_decide` is forbidden.

## 7. Make P explicit before delegating (the rigor pass)

AIProver follows P as written. Informal proofs in these datasets routinely say "similarly for
the other direction", "clearly", "by induction" (hypothesis unstated), "the usual argument",
"by cases" (cases unlisted), or lean on a convention the reader is assumed to know. Each of
those is a step AIProver must invent -- and inventing is where it drifts from P or stalls.

Before step 2, rewrite P as numbered atomic steps. For each step name what justifies it (which
hypothesis, which earlier step, which named fact, induction on what). Spell out every case of
a case split and both directions of an "iff". Pin the ambient types ("all variables are
integers", "subgroup of G") and what named relations mean for these objects. Keep P's method
and its intermediate lemmas exactly as P has them -- (d) is judged against the ORIGINAL P --
and keep the original beside your expansion so you can judge against it.

Send the expansion as the `<informal_proof>` block (or `--proof-text`). The theorem text is
never rewritten; only the proof is expanded.

## 8. Reading `probe`

```
probe  s2.lean  (3 statement(s), 4.1s)
  part1: COUNTEREXAMPLE  --  a := 1 ; i := 0 ; j := 1 ; issue: 1 = 0 does not hold ; (0 shrinks)
  part2: no counterexample found  --  random testing passed; this proves nothing
      closed by automation alone: simp, omega  -> is the statement narrowed, specialised or trivial?
  part3: untestable  --  no sampling/decidability instances for this statement
```
- `COUNTEREXAMPLE`: the statement is false as written. T is a true theorem, so the formal
  statement lost a hypothesis, widened a quantifier, used ℕ where T means ℤ/ℚ/ℝ (truncated
  subtraction, floor division), or placed a cast wrongly. Fix the statement; do not touch the
  proof yet. The witness tells you which variable to look at.
- `closed by automation alone`: a statement that `simp`/`decide`/`omega`/... prove outright
  carries no content for AIProver to be faithful to. For a lemma that P treats as routine that is
  fine; for a theorem part or a lemma P proves with an argument, suspect narrowing or
  specialisation (failure modes 2 and 6 in §2) and compare against T clause by clause.
- `untestable`: abstract carriers, undecidable relations, or no sampler -- no information.
- `no counterexample found`: 100 random tests passed. It is not evidence of (c); go on to judge.
- `not probed`: a pattern-matching proof (no `:=`) -- rewrite it with `:= by ...` if you want it
  probed, or judge by hand.
Probe the skeleton (step 4a) as well as every candidate: a false lemma statement in a frozen
skeleton wastes every job submitted against it.

## 9. A stuck step becomes a lemma (the extraction recipe)

When a piece fails twice at the same place:
1. Open the best sample's file in the workspace (`$AIP workspace --new NAME`, paste it) and
   replace the failing step by `sorry`, so the file elaborates up to that point.
2. `$AIP extract FILE.lean --line <line of that sorry> --name <piece>_step<k>`. Lean's
   `extract_goal` prints the lemma with the exact local context as binders -- universes,
   instance arguments, earlier `have`s and the induction hypothesis included -- so nothing is
   transcribed by hand. (`lean_goal` at the position shows the same context if you want to read
   it first.)
3. Paste the lemma above the theorem, make the step `exact <piece>_step<k> ...`, and run
   `$AIP check --statement-only` on the file.
4. `$AIP probe` the new lemma (a false extracted statement means the surrounding proof was
   already off the rails -- look upstream).
5. Submit the lemma alone: `--context` = frozen definitions (+ any lemma it may use as a
   `sorry`d given), `--lean-statement` = the lemma, `--theorem-text`/`--proof-text` = that step
   of P, `-k 4`. Small, fully specified goals are what AIProver solves most reliably.
6. Weave the returned proof body back; `check`; judge.

## 10. Search order, and cslib

1. `lean_local_search NAME` -- by name prefix, across Mathlib AND cslib of THIS project. Always
   first when you have a guess at the name.
2. `$AIP search "concept words"` -- declarations whose name, header or docstring contain every
   word; cslib by default, `--lib mathlib|all` for Mathlib (first run builds a cached index,
   ~10 s). Hits print the exact `import` line.
3. `lean_loogle` -- by type shape (`_ * (_ ^ _)`, `|- tsum _ = _ * tsum _`); `lean_leansearch`
   / `lean_leanfinder` -- natural language. Hosted, newer Mathlib: confirm every hit with 1.
   (`$AIP search --lib loogle|leansearch|leandex` reaches the same services from the shell; the
   lean-lsp tools are the rate-limited path and are preferred inside a session.)
4. For a concrete goal in a file: `lean_state_search`, `lean_hammer_premise` at the position.
5. `lean_hover_info` on the chosen name to read what it IS before using it (failure mode 1).

cslib: `import Cslib` loads only six modules; import the module a hit lives in
(`.lake/packages/cslib/Cslib/A/B.lean` -> `import Cslib.A.B`). Use it only when T is about
its notions (transition systems, bisimulation, process calculi, lambda calculi, combinatory
logic, linear logic) and the environment compiling your answer has it. Tell AIProver which
module to import in `--hint` when you delegate such a piece; it searches cslib with
`lean_local_search` too, but naming the module saves it turns.

## 11. Tactic rules that keep P̂ faithful

For your own small repairs, and as `--hint` material when a sample violates them:
- **No enumeration where P argues.** `fin_cases`, `decide`, `interval_cases`, `omega` over a
  case split that P handles conceptually replaces P's argument -- a (d) failure even when it
  compiles. Automation may close a step P also treats as routine.
- **Mirror P's structure.** One `have`/lemma per intermediate claim of P, in P's order, used
  where P uses it. A proof that reaches the conclusion by a different route is not P̂.
- **Typed numerals and casts.** Write `((2 : ℝ) / 3)`, never bare `2 / 3`; decide the carrier
  of each variable up front; a `↑` sits exactly where T's arithmetic happens.
- **No `set_option maxHeartbeats`** above the default to force `decide`/`simp` through: that is
  a sign the statement or the route is wrong, and `maxHeartbeats 0` is a disqualifier.
- **Keep automation calls small.** `linarith`/`nlinarith` with the five hypotheses that matter,
  not the whole context; `simp only [...]` once you know the lemma set (`simp?` finds it).
- **Repeated branches = a lemma.** Identical scripts in several cases mean a `wlog` or a helper
  lemma, never copy-paste.
- **Never weaken to compile.** Adding a hypothesis, specialising a type, or dropping a part to
  make a proof go through trades an (a)/(b) failure for a (c) failure.

## 12. Standalone mode: the informal steps without a coding agent

`bin/aiprover` can be driven by a person with no Claude Code or Codex. The judgement steps then
have no frontier model, so three commands offer them on AIProver's own endpoint (an
OpenAI-compatible chat API; the model is Lean-specialised, so treat the answers as drafts):

| command | what it does | NL analogue in the plugin modes |
|---|---|---|
| `expand --problem P.txt --out P2.txt` | rewrites P as numbered atomic steps, method and lemmas kept; a critic pass checks method/lemmas/assumptions and the writer revises (`--rounds`) | step 1b, done by the coding agent |
| `backtranslate FILE.lean` | says in plain English what every declaration of the file states, hypotheses and number types included | judge protocol (c) step 1, done by the coding agent |
| `ask "question" [--file F.lean]` | one free-form question with a file as context | the agent's own reasoning |

Every command has `--dry-run` (prints the prompt). The coding agents are told NOT to call these:
they are better informal mathematicians than the model behind them.

