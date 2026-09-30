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
Mathlib lemma (`lean_local_search` / `lean_loogle` to find the 4.23 name), a universe or
implicit-argument annotation, a duplicated helper name between woven pieces, and weaving glue
(`exact partK ...`). Anything that needs real proof search, delegate.

## 6. Lean / Mathlib version

Lean `v4.23.0`, Mathlib `v4.23.0`. Hosted search tools (`lean_leansearch`, `lean_leanfinder`,
`lean_loogle`) may return names from a newer Mathlib. Confirm any name with `lean_local_search`
or `lean_hover_info` before relying on it. `grind` exists on 4.23. `native_decide` is forbidden.
