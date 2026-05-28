/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T42 (Phase 19 / Path C — Corrected formulation of
        `AssemblyPieceA` with an explicit positive constant `C` on the
        main term, refuting the original `C = 1` form via the
        counterexample `n = 30`, `z = 5`.)
-/
import Gdbh.PathC_BrunBonferroniDecomposition
import Gdbh.PathC_AssemblyPieceAClosure
import Mathlib.NumberTheory.PrimeCounting

/-!
# Path C — P19-T42: Corrected `AssemblyPieceA` with an explicit constant.

## Counterexample to the original `AssemblyPieceA`

The original Prop
`Gdbh.PathCBrunBonferroniDecomposition.AssemblyPieceA` asserts, for
every truncation depth `k : ℕ → ℕ` and every `n ≥ 4`,

```
goldbachSiftedPair n √n  ≤  n · pairedBrunFactor √n
                              + n · π(√n)^{2 k n + 1} / (2 k n + 1)!
```

i.e. with **coefficient `1`** on the main term `n · pairedBrunFactor √n`.

This formulation is **mathematically false**.  At the small explicit
witness `n = 30`, `z = √30 = 5`, `k(30) = 4`:

* LHS = `goldbachSiftedPair 30 5 = 8`
  (the eight values `m ∈ {1, 7, 11, 13, 17, 19, 23, 29}`, each coprime
   to `30 = 2·3·5`, give paired sift members `(m, 30 - m)`);
* Main term = `30 · pairedBrunFactor 5 = 30 · 1/5 = 6`;
* Tail term = `30 · 3^9 / 9!  =  590490 / 362880 < 2`;
* So RHS  <  `6 + 2 = 8 = LHS`, contradicting the claimed `LHS ≤ RHS`.

The root cause:  the classical Brun-Goldbach upper bound has a singular
series factor (Hardy-Littlewood),

```
r(n) ≤ C · n / (log n)² · S(n)   ,   S(n) ≤ 2 C₂ ∏_{p | n, p > 2} (p-1)/(p-2)   .
```

For primorial `n = 2·3·5·...·k`, the singular series `S(n)` grows like
`log log n` — but `pairedBrunFactor` only captures the *average*
singular series, ignoring the `n`-dependent factor.  Hence the
`C = 1` coefficient on `n · pairedBrunFactor √n` is *insufficient*;
an explicit positive constant `C` (the Hardy-Littlewood / Selberg
upper bound, classically `C = 8` or `C = 16` depending on
normalization) is required.

## The corrected Prop

We define
```
AssemblyPieceA_Corrected : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (k : ℕ → ℕ) (n : ℕ), 4 ≤ n →
      goldbachSiftedPair n √n ≤ C · n · pairedBrunFactor √n + tail   .
```

For `C = 8`, the counterexample at `n = 30` becomes consistent
(`RHS ≥ 8 · 6 = 48 > 8 = LHS`).

## Deliverables

* `AssemblyPieceA_Corrected`:  the corrected Prop (Option A from the
  task spec — an explicit positive constant on the main term).

* `pairedBrunFactor_five_eq`:  the exact computation
  `pairedBrunFactor 5 = 1/5`, used in the counterexample refutation.

* `goldbachSiftedPair_thirty_five_eq`:  the exact computation
  `goldbachSiftedPair 30 5 = 8`, the LHS of the counterexample.

* `assemblyPieceA_false_at_n30`:  **refutation** of the original
  `AssemblyPieceA` Prop, exhibiting the explicit counterexample at
  `n = 30`, `k = fun _ => 4`.

* `assemblyPieceA_corrected_holds_at_n30`:  sanity check that the
  *corrected* Prop is consistent with the counterexample, by
  exhibiting the constant `C = 8` and verifying the inequality at
  `n = 30`.

* `assemblyPieceA_corrected_implies_scaled_assembly`:  the forward
  bridge.  If `AssemblyPieceA_Corrected` holds with constant `C`, then
  the same combinatorial chain delivers Path C's Brun-Bonferroni
  conclusion with the constant scaled by `C`.

## Constraint compliance

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.

## References

* G. H. Hardy, J. E. Littlewood, *Some problems of "Partitio
  numerorum": III. On the expression of a number as a sum of primes*,
  Acta Math. 44 (1923), 1–70.
* A. Selberg, *On elementary methods in primenumber-theory and their
  limitations*, in *Collected Papers* I, Springer 1989.
* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, Theorem 7.1.
-/

namespace Gdbh
namespace PathCAssemblyPieceACorrected

open Real
open Finset
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPair_le goldbachSiftedPairSet)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunBonferroniDecomposition
  (AssemblyPieceA)

/-! ## Section 1 — The corrected Prop with explicit constant. -/

/-- **Corrected `AssemblyPieceA`** with an explicit positive constant
`C` on the main term `n · pairedBrunFactor √n`.

The original `AssemblyPieceA` (coefficient `1`) is **mathematically
false** — see `assemblyPieceA_false_at_n30` for the explicit
counterexample at `n = 30`.  The corrected Prop introduces an
existentially-quantified positive constant `C > 0`, allowing the
Hardy-Littlewood / Selberg singular series upper bound to be absorbed
into a single constant. -/
def AssemblyPieceA_Corrected : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (k : ℕ → ℕ) (n : ℕ), 4 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                  / ((2 * k n + 1).factorial : ℝ)

/-! ## Section 2 — Computational lemmas for the counterexample at `n = 30`. -/

/-- `Nat.sqrt 30 = 5`. -/
theorem nat_sqrt_thirty : Nat.sqrt 30 = 5 := by
  symm
  rw [Nat.eq_sqrt]
  refine ⟨by norm_num, by norm_num⟩

/-- The primes in `[3, 5]` are exactly `{3, 5}`. -/
theorem primes_three_five_filter :
    (Finset.Icc 3 5).filter Nat.Prime = ({3, 5} : Finset ℕ) := by
  decide

/-- **Exact value of `pairedBrunFactor 5`**:
`(1 - 2/3)(1 - 2/5) = (1/3)(3/5) = 1/5`. -/
theorem pairedBrunFactor_five_eq : pairedBrunFactor 5 = (1 : ℝ) / 5 := by
  unfold pairedBrunFactor
  rw [primes_three_five_filter]
  rw [show ({3, 5} : Finset ℕ) = insert 3 ({5} : Finset ℕ) from rfl]
  rw [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ))]
  rw [Finset.prod_singleton]
  norm_num

/-- `Nat.primeCounting 5 = 3` (the primes `≤ 5` are `2, 3, 5`). -/
theorem primeCounting_five_eq : Nat.primeCounting 5 = 3 := by
  decide

/-- **Exact value of `goldbachSiftedPair 30 5`**:  the eight values
`m ∈ {1, 7, 11, 13, 17, 19, 23, 29}`, each in `[1, 29]` with both `m`
and `30 - m` coprime to every prime `p ≤ 5` (i.e. `p ∈ {2, 3, 5}`). -/
theorem goldbachSiftedPair_thirty_five_eq :
    goldbachSiftedPair 30 5 = 8 := by
  decide

/-! ## Section 3 — Auxiliary arithmetic facts for the tail term. -/

/-- The tail-term inequality `30 · 3^9 < 2 · 9!`, used to bound the
truncation tail by `< 2` at the counterexample `(n = 30, k = 4)`. -/
theorem tail_thirty_inequality :
    (30 * 3^9 : ℕ) < 2 * Nat.factorial 9 := by
  decide

/-- Real-valued version of `tail_thirty_inequality`. -/
theorem tail_thirty_inequality_real :
    (30 : ℝ) * (3 : ℝ)^9 < 2 * (Nat.factorial 9 : ℝ) := by
  have h := tail_thirty_inequality
  exact_mod_cast h

/-- The factorial `9! > 0` in `ℝ`. -/
theorem factorial_nine_pos_real : (0 : ℝ) < (Nat.factorial 9 : ℝ) := by
  have : 0 < Nat.factorial 9 := Nat.factorial_pos 9
  exact_mod_cast this

/-! ## Section 4 — Refutation of the original `AssemblyPieceA`. -/

/-- **Refutation of `AssemblyPieceA`** via the explicit
counterexample at `n = 30`, `k = fun _ => 4`.

The original Prop's RHS at `(n, k_val) = (30, 4)` is

```
  30 · pairedBrunFactor 5  +  30 · 3^9 / 9!
=   6                       +  590490 / 362880
<   6                       +  2
=   8 .
```

But the LHS is `goldbachSiftedPair 30 5 = 8`, giving `8 ≤ RHS < 8`,
a contradiction. -/
theorem assemblyPieceA_false_at_n30 : ¬ AssemblyPieceA := by
  intro h
  -- Instantiate at k = fun _ => 4, n = 30.
  have h30 := h (fun _ => 4) 30 (by norm_num)
  -- Simplify Nat.sqrt 30, pairedBrunFactor 5, Nat.primeCounting 5,
  -- and goldbachSiftedPair 30 5.
  rw [nat_sqrt_thirty] at h30
  rw [pairedBrunFactor_five_eq] at h30
  rw [primeCounting_five_eq] at h30
  rw [goldbachSiftedPair_thirty_five_eq] at h30
  -- Normalize the casts so the arithmetic terms are real numerals.
  push_cast at h30
  -- After push_cast, h30 reads (8 : ℝ) ≤ 30 · (1/5) + 30 · 3^9 / 9!
  -- We show this is `8 ≤ 6 + 590490/362880 < 8`.
  -- First, evaluate 30 · (1/5) = 6.
  have h_main : (30 : ℝ) * ((1 : ℝ) / 5) = 6 := by norm_num
  rw [h_main] at h30
  -- Next, bound the tail: 30 · 3^9 / 9! < 2.
  have h_tail_lt :
      (30 : ℝ) * (3 : ℝ)^(2 * 4 + 1) / ((2 * 4 + 1).factorial : ℝ) < 2 := by
    have h_eq : (2 * 4 + 1 : ℕ) = 9 := by norm_num
    rw [h_eq]
    -- Now bound 30 · 3^9 / 9! < 2 i.e. 30 · 3^9 < 2 · 9!.
    rw [div_lt_iff₀ factorial_nine_pos_real]
    exact tail_thirty_inequality_real
  -- Combine:  h30 : 8 ≤ 6 + tail,  h_tail_lt : tail < 2,
  -- so 8 ≤ 6 + tail < 6 + 2 = 8, contradiction.
  linarith [h30, h_tail_lt]

/-! ## Section 5 — The corrected Prop is consistent at the
counterexample. -/

/-- **Validity sanity check**:  the corrected Prop `AssemblyPieceA_Corrected`
with constant `C = 8` is consistent with the counterexample at
`n = 30`, `k = fun _ => 4`.

At `n = 30`, `k(30) = 4`:
* LHS = `goldbachSiftedPair 30 5 = 8`;
* Main term (scaled) = `8 · 30 · 1/5 = 48`;
* Tail = `30 · 3^9 / 9! ≥ 0`;
* RHS ≥ `48 + 0 = 48 ≥ 8 = LHS`.

So the corrected inequality holds at this specific point. -/
theorem assemblyPieceA_corrected_holds_at_n30 :
    (goldbachSiftedPair 30 (Nat.sqrt 30) : ℝ)
      ≤ 8 * (30 : ℝ) * pairedBrunFactor (Nat.sqrt 30)
        + (30 : ℝ) * (Nat.primeCounting (Nat.sqrt 30) : ℝ)^(2 * 4 + 1)
                / ((2 * 4 + 1).factorial : ℝ) := by
  rw [nat_sqrt_thirty]
  rw [pairedBrunFactor_five_eq]
  rw [primeCounting_five_eq]
  rw [goldbachSiftedPair_thirty_five_eq]
  -- LHS = 8, main term = 8·30·(1/5) = 48, tail ≥ 0.
  have h_main_eq : 8 * (30 : ℝ) * ((1 : ℝ) / 5) = 48 := by norm_num
  rw [h_main_eq]
  -- Tail is non-negative.
  have h_tail_nonneg :
      (0 : ℝ) ≤ (30 : ℝ) * (3 : ℝ)^(2 * 4 + 1)
                / ((2 * 4 + 1).factorial : ℝ) := by
    refine div_nonneg ?_ ?_
    · refine mul_nonneg (by norm_num) ?_
      positivity
    · exact_mod_cast Nat.zero_le _
  -- 8 ≤ 48 + tail.
  have : (8 : ℝ) ≤ 48 := by norm_num
  linarith

/-! ## Section 6 — Existence of the corrected Prop at a fixed point.

This is a partial validity check.  We do NOT close
`AssemblyPieceA_Corrected` itself (which still requires the
Halberstam-Richert combinatorial chain — the corrected formulation
inherits the same combinatorial residual).  We only show that, at the
specific counterexample point, the corrected form with `C = 8` is
satisfied. -/

/-! ## Section 7 — Forward bridge: corrected Prop → Path C with
constant scaling. -/

/-- **Forward bridge**:  the corrected `AssemblyPieceA_Corrected`
(with explicit constant `C > 0`) produces, by the same combinatorial
chain as the original `AssemblyPieceA`, a Brun-Bonferroni bound with
the constant scaled by `C`.

Concretely, if `AssemblyPieceA_Corrected` holds with constant `C`,
then for every `k : ℕ → ℕ` and `n ≥ 4`:

```
goldbachSiftedPair n √n ≤ C · n · pBF(√n) + tail   .
```

The downstream Brun bound `r(n) ≤ C₀ · n / (log n)²` then holds with
constant `C · C₀`, where `C₀` is the constant produced by the
original Halberstam-Richert chain assuming the (false) `C = 1` form.
Since `GoldbachRepresentationBound` is existentially quantified in
its constant, scaling by `C` preserves the conclusion.

This bridge is **mechanical** (a constant absorption);  the genuine
combinatorial content is the closure of `AssemblyPieceA_Corrected`,
which is strictly weaker than (and implied by) the false original. -/
theorem assemblyPieceA_corrected_implies_scaled_assembly
    (h : AssemblyPieceA_Corrected) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ → ℕ) (n : ℕ), 4 ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                    / ((2 * k n + 1).factorial : ℝ) := h

/-- **Bridge equivalence**:  the corrected Prop is **definitionally
identical** to its "scaled assembly" form. -/
theorem assemblyPieceA_corrected_iff_scaled :
    AssemblyPieceA_Corrected ↔
      (∃ C : ℝ, 0 < C ∧
        ∀ (k : ℕ → ℕ) (n : ℕ), 4 ≤ n →
          (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
            ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
              + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                      / ((2 * k n + 1).factorial : ℝ)) := Iff.rfl

/-- **Original `AssemblyPieceA` implies the corrected form** (with
`C = 1`).  This direction is trivial:  if the original holds, take
`C = 1` and the inequality is identical.

Note: this direction is *vacuously interesting* because the original
Prop is **false** (see `assemblyPieceA_false_at_n30`).  We record the
bridge for completeness and to expose the logical relation. -/
theorem assemblyPieceA_implies_corrected
    (h : AssemblyPieceA) : AssemblyPieceA_Corrected := by
  refine ⟨1, by norm_num, ?_⟩
  intro k n hn
  have := h k n hn
  -- Original RHS has coefficient 1; corrected with C = 1 is identical.
  simpa [one_mul] using this

/-! ## Section 8 — Direct contradiction: the original Prop refutes
itself.

Combining `assemblyPieceA_false_at_n30` with the trivial bridge,
the chain is:

```
   AssemblyPieceA  →  AssemblyPieceA_Corrected (with C = 1)
   AssemblyPieceA  →  False  (via counterexample at n = 30)
```

The contrapositive gives:  **the original `AssemblyPieceA` is
unprovable**, while the corrected form `AssemblyPieceA_Corrected`
(with `C ≥ 8` say) is still potentially closable via the full
Halberstam-Richert chain. -/

/-- **Summary**:  `AssemblyPieceA → False`, equivalently `¬ AssemblyPieceA`. -/
theorem assemblyPieceA_unprovable : ¬ AssemblyPieceA :=
  assemblyPieceA_false_at_n30

/-- The corrected Prop with `C = 1` is **not** equivalent to the
original (which is false);  the corrected Prop with `C ≥ 8` is the
mathematically sound formulation.

This theorem records the fact: at `C = 1`, `AssemblyPieceA_Corrected`
specialises to (and is implied by) the original `AssemblyPieceA`,
which we have shown to be false.  At larger `C`, the corrected Prop
is strictly weaker and potentially closable. -/
theorem assemblyPieceA_corrected_constant_required :
    ∀ C : ℝ, C ≤ 1 → ¬ (0 < C ∧ ∀ (k : ℕ → ℕ) (n : ℕ), 4 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                  / ((2 * k n + 1).factorial : ℝ)) := by
  intro C hC1 ⟨hCpos, hineq⟩
  -- Apply the inequality at n = 30, k = fun _ => 4.
  have h30 := hineq (fun _ => 4) 30 (by norm_num)
  rw [nat_sqrt_thirty] at h30
  rw [pairedBrunFactor_five_eq] at h30
  rw [primeCounting_five_eq] at h30
  rw [goldbachSiftedPair_thirty_five_eq] at h30
  -- Normalize casts.
  push_cast at h30
  -- After: (8 : ℝ) ≤ C · 30 · (1/5) + tail.
  -- Bound the tail: 30 · 3^9 / 9! < 2.
  have h_tail_lt :
      (30 : ℝ) * (3 : ℝ)^(2 * 4 + 1) / ((2 * 4 + 1).factorial : ℝ) < 2 := by
    have h_eq : (2 * 4 + 1 : ℕ) = 9 := by norm_num
    rw [h_eq]
    rw [div_lt_iff₀ factorial_nine_pos_real]
    exact tail_thirty_inequality_real
  -- So h30 : 8 ≤ C · 30 · (1/5) + tail, with C ≤ 1 and tail < 2.
  -- C · 30 · (1/5) = 6C ≤ 6, so 8 ≤ 6 + 2 = 8, contradiction (strict).
  have h6C : C * (30 : ℝ) * ((1 : ℝ) / 5) ≤ 6 := by nlinarith
  linarith [h30, h_tail_lt, h6C]

/-! ## Section 9 — Audit handle.

All theorems in this file use only the structural mathematical
content available in the closed building blocks of Path C.  The
only axioms transitively invoked are
`[Classical.choice, Quot.sound, propext]`. -/

/-- **P19-T42 summary** (sentinel; informal).

This file establishes:

* The original `AssemblyPieceA` is **false** (refuted at `n = 30`).
* The corrected `AssemblyPieceA_Corrected` introduces an explicit
  positive constant `C` on the main term, accommodating the
  Hardy-Littlewood singular series factor.
* For any `C ≤ 1`, the corrected form is still refuted at `n = 30`.
* For `C = 8` (Selberg/Hardy-Littlewood upper bound), the corrected
  form is consistent with the counterexample.
* The forward bridge from the corrected Prop to the constant-scaled
  Brun-Bonferroni assembly is mechanical (a definitional re-export).

The downstream impact:  any Path C theorem that consumed the false
`AssemblyPieceA` must be re-derived from `AssemblyPieceA_Corrected`.
Since `GoldbachRepresentationBound` and its downstream consumers
are existentially quantified in their constants, the scaling by `C`
preserves all conclusions modulo a constant absorption. -/
theorem pathC_p19_t42_summary : True := trivial

end PathCAssemblyPieceACorrected
end Gdbh
