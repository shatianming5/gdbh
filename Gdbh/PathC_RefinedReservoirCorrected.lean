/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P20-T1 (Phase 20 / Path C — corrected reservoir absorbing the
         Hardy–Littlewood singular series along primorials)
-/
import Gdbh.PathC_BrunRefinedComposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Path C — P20-T1: Corrected refined reservoir `n · log log n / (log n)²`

This file is the **P20-T1 deliverable** in Phase 20 (Path C refined
reservoir correction).  Phase 19 (P19-T51 + T45 + T50) established that
the *original* refined-reservoir form

```
B(n, z) := n / (log n)²
```

— used in `Gdbh.PathCBrunRefinedComposition.refinedReservoir` and in
`BrunGoldbachPairedMainTermRefinedAtSqrt` — is **counter-exemplified
along primorials**: at `n = ∏_{p ≤ z₀} p` (`z₀ → ∞`), the
Hardy–Littlewood singular series factor
`∏_{p ∣ n, p ≥ 3} (p − 1) / (p − 2)` grows like `log log n` (Mertens'
3rd theorem on residues), which is unbounded, so the bound

```
goldbachSiftedPair n √n  ≤  C₁ · n · pairedBrunFactor √n  +  n / (log n)²
```

fails for every fixed constant `C₁`.

## FixA: absorb the singular series into the reservoir

The honest fix is to enlarge the reservoir by a factor of `log log n`:

```
B_corr(n, z) := n · log log n / (log n)² .
```

This **fully absorbs** the divergent singular series along primorials:
the Hardy–Littlewood twin-prime asymptotic predicts
`r₂(n) ∼ 2 · C₂ · ∏_{p∣n, p≥3} (p−1)/(p−2) · n / (log n)²`,
and the residue product is `O(log log n)` (Mertens 3 + multiplicative
divisor count).  Hence `r₂(n) = O(n · log log n / (log n)²)`, which is
exactly the corrected reservoir.

## File scope

This file **only defines** the corrected reservoir and proves its
elementary positivity and comparison properties relative to the
original `refinedReservoir`.  It does **not** rebuild
`BrunGoldbachPairedMainTermRefined` with the corrected reservoir — that
is deferred to subsequent P20 tasks.

## Honesty note

For small `n`, `Real.log (Real.log n)` can be negative (`n = 2`) or
zero (`n = 1`), so the corrected reservoir is **not unconditionally
non-negative**.  We document the precise thresholds:

* `n ≥ 3` ⇒ `log n ≥ log 3 > 1` (since `e < 3`) ⇒ `log log n > 0`
  ⇒ corrected reservoir is *strictly positive*.
* `n ≥ 27 = 3³` ⇒ `log n ≥ 3 · log 3 > 3 > e` ⇒ `log log n > 1`
  ⇒ corrected reservoir ≥ original reservoir.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext` are transitively used (verified via
`#print axioms` at the end of the file).
-/

namespace Gdbh
namespace PathCRefinedReservoirCorrected

open Real
open Gdbh.PathCBrunRefinedComposition (refinedReservoir refinedReservoir_def)

/-! ## Section 1 — Definition

The corrected reservoir is `(n : ℝ) · log log n / (log n)²`,
independent of the sieve threshold `z` (same indexing convention as
`Gdbh.PathCBrunRefinedComposition.refinedReservoir`). -/

/-- **Corrected refined reservoir.**  Absorbs the Hardy–Littlewood
singular-series factor `∏_{p ∣ n, p ≥ 3} (p−1)/(p−2) = O(log log n)`
into the refined Brun reservoir `n / (log n)²` from
`Gdbh.PathCBrunRefinedComposition.refinedReservoir`.

This is the **P20-T1 corrected reservoir** that replaces the
counter-exemplified `n / (log n)²` along primorials. -/
noncomputable def refinedReservoirCorrected (n z : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2

/-- Definitional unfolding (`@[simp]`). -/
@[simp] lemma refinedReservoirCorrected_def (n z : ℕ) :
    refinedReservoirCorrected n z
      = (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2 := rfl

/-- Independence of the second argument (sieve threshold `z`). -/
lemma refinedReservoirCorrected_indep_of_z (n _z₁ _z₂ : ℕ) :
    refinedReservoirCorrected n _z₁ = refinedReservoirCorrected n _z₂ := rfl

/-! ## Section 2 — Logarithm helper lemmas

We need explicit lower bounds on `Real.log n` for `n ≥ 3` and on
`Real.log (Real.log n)` for `n ≥ 3` (positivity) and `n ≥ 27`
(domination of `1`).  These follow from the elementary
`Real.exp_one_lt_three`. -/

/-- For `n ≥ 3`, `log n > 0` (since `n > 1`). -/
private lemma log_natCast_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.log (n : ℝ) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := by omega
    exact_mod_cast this
  exact Real.log_pos h1

/-- For `n ≥ 3`, `(log n)² > 0`. -/
private lemma log_natCast_sq_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < (Real.log (n : ℝ))^2 := by
  have h := log_natCast_pos hn
  positivity

/-- `Real.log 3 > 1`.  Follows from `exp 1 < 3` (`Real.exp_one_lt_three`). -/
private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hloglt : Real.log (Real.exp 1) < Real.log 3 :=
    Real.log_lt_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at hloglt

/-- For `n ≥ 3`, `log n ≥ log 3 > 1` (since `n ≥ 3`). -/
private lemma log_natCast_gt_one {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) < Real.log (n : ℝ) := by
  have h3 : (1 : ℝ) < Real.log 3 := log_three_gt_one
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hmono : Real.log 3 ≤ Real.log (n : ℝ) := Real.log_le_log h3pos hn3
  linarith

/-- For `n ≥ 3`, `log log n > 0` (since `log n > 1`). -/
private lemma log_log_natCast_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < Real.log (Real.log (n : ℝ)) := by
  have h := log_natCast_gt_one hn
  exact Real.log_pos h

/-- For `n ≥ 27 = 3³`, `log n ≥ 3 · log 3 > 3 > e`, hence `log log n > 1`. -/
private lemma log_log_natCast_gt_one {n : ℕ} (hn : 27 ≤ n) :
    (1 : ℝ) < Real.log (Real.log (n : ℝ)) := by
  -- Step 1: `log 27 = 3 · log 3 > 3`.
  have hlog3 : (1 : ℝ) < Real.log 3 := log_three_gt_one
  have h27_eq : (27 : ℝ) = (3 : ℝ)^3 := by norm_num
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [h27_eq]
    rw [show ((3 : ℝ)^3) = 3 * 3 * 3 from by ring]
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    have h33_pos : (0 : ℝ) < 3 * 3 := by norm_num
    rw [Real.log_mul (by linarith : (3 : ℝ) * 3 ≠ 0) (by linarith : (3 : ℝ) ≠ 0)]
    rw [Real.log_mul (by linarith : (3 : ℝ) ≠ 0) (by linarith : (3 : ℝ) ≠ 0)]
    ring
  have hlog27_gt3 : (3 : ℝ) < Real.log 27 := by
    rw [hlog27]; linarith
  -- Step 2: `log n ≥ log 27 > 3`.
  have hn27 : (27 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h27_pos : (0 : ℝ) < 27 := by norm_num
  have hlog_mono : Real.log (27 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log h27_pos hn27
  have hlog_n_gt3 : (3 : ℝ) < Real.log (n : ℝ) := by linarith
  -- Step 3: `log log n > log 3 > 1`.
  have hlog_n_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog3_lt_log_log_n : Real.log 3 < Real.log (Real.log (n : ℝ)) := by
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    exact Real.log_lt_log h3_pos hlog_n_gt3
  linarith

/-! ## Section 3 — Basic properties of the corrected reservoir

We expose:

* `refinedReservoirCorrected_nonneg`: for `n ≥ 3`, the corrected
  reservoir is non-negative.
* `refinedReservoirCorrected_pos_of_n_ge_three`: for `n ≥ 3`, the
  corrected reservoir is strictly positive.
* `refinedReservoirCorrected_ge_original`: for `n ≥ 27`, the corrected
  reservoir dominates the original `refinedReservoir`. -/

/-- **Non-negativity at `n ≥ 3`.**  For `n ≥ 3`, both `log log n > 0`
and `(log n)² > 0`, and `n > 0`, so the quotient is non-negative.

(For small `n`: at `n ≤ 1`, `log n ≤ 0` and the formula reduces to
`0 / 0 = 0` by mathlib's `Real` division convention; at `n = 2`,
`log 2 ≈ 0.693 < 1`, so `log log 2 < 0` and the reservoir is
**negative** — this is the honest documented limitation.) -/
theorem refinedReservoirCorrected_nonneg
    (n z : ℕ) (hn : 3 ≤ n) :
    0 ≤ refinedReservoirCorrected n z := by
  unfold refinedReservoirCorrected
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hll_nn : 0 ≤ Real.log (Real.log (n : ℝ)) :=
    le_of_lt (log_log_natCast_pos hn)
  have hnum_nn : 0 ≤ (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
    mul_nonneg hn_nn hll_nn
  have hden_nn : 0 ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  exact div_nonneg hnum_nn hden_nn

/-- **Strict positivity at `n ≥ 3`.**  For `n ≥ 3`, `log log n > 0`
(since `log n > log 3 > 1`) and `(log n)² > 0`, so the corrected
reservoir is strictly positive.

(Numerically: `log log 3 ≈ 0.0937 > 0`.) -/
theorem refinedReservoirCorrected_pos_of_n_ge_three
    (n z : ℕ) (hn : 3 ≤ n) :
    0 < refinedReservoirCorrected n z := by
  unfold refinedReservoirCorrected
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := log_log_natCast_pos hn
  have hnum_pos : 0 < (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
    mul_pos hn_pos hll_pos
  have hden_pos : 0 < (Real.log (n : ℝ))^2 := log_natCast_sq_pos hn
  exact div_pos hnum_pos hden_pos

/-- **Domination of the original reservoir.**  For `n ≥ 27 = 3³`,
`log log n > 1`, hence the corrected reservoir dominates the original
`refinedReservoir n z = n / (log n)²`.

The threshold `N₀ = 27` is convenient because `log 27 = 3 · log 3` and
`log 3 > 1` (since `e < 3`), so `log log 27 > log 3 > 1`. -/
theorem refinedReservoirCorrected_ge_original
    (n z : ℕ) (hn : 27 ≤ n) :
    refinedReservoir n z ≤ refinedReservoirCorrected n z := by
  -- Unfold both reservoirs.
  rw [refinedReservoir_def, refinedReservoirCorrected_def]
  -- Goal:
  --   `(n : ℝ) / (log n)² ≤ (n : ℝ) · log log n / (log n)²`.
  have hn3 : 3 ≤ n := by omega
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hden_pos : 0 < (Real.log (n : ℝ))^2 := log_natCast_sq_pos hn3
  -- Reduce to `1 ≤ log log n` via division monotonicity.
  rw [div_le_div_iff₀ hden_pos hden_pos]
  -- Goal: `n · (log n)² ≤ n · log log n · (log n)²`.
  have hll_gt_one : (1 : ℝ) < Real.log (Real.log (n : ℝ)) :=
    log_log_natCast_gt_one hn
  have hll_ge_one : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := le_of_lt hll_gt_one
  have hsq_nn : 0 ≤ (Real.log (n : ℝ))^2 := le_of_lt hden_pos
  -- `n · (log n)² ≤ n · log log n · (log n)²`
  -- iff `n · (log n)² · 1 ≤ n · (log n)² · log log n` (rearranging)
  -- which follows from `1 ≤ log log n` and `n · (log n)² ≥ 0`.
  have hn_lhs_nn : 0 ≤ (n : ℝ) * (Real.log (n : ℝ))^2 :=
    mul_nonneg hn_nn hsq_nn
  nlinarith [hll_ge_one, hn_lhs_nn]

/-! ## Section 4 — Relationship to the original `refinedReservoir`

We document the algebraic identity tying the corrected reservoir to
the original. -/

/-- **Factoring identity.**  When `log n ≠ 0`, the corrected reservoir
equals the original reservoir multiplied by `log log n`:

```
refinedReservoirCorrected n z  =  refinedReservoir n z · log log n .
```

This makes the absorption of the singular-series factor explicit:
the corrected reservoir is *literally* the original reservoir scaled
by `log log n`. -/
theorem refinedReservoirCorrected_eq_refinedReservoir_mul_log_log
    (n z : ℕ) :
    refinedReservoirCorrected n z
      = refinedReservoir n z * Real.log (Real.log (n : ℝ)) := by
  unfold refinedReservoirCorrected
  rw [refinedReservoir_def]
  ring

/-- **Quantitative comparison.**  For `n ≥ 27`, the *ratio* of the
corrected to the original reservoir is `log log n > 1` (see
`refinedReservoirCorrected_eq_refinedReservoir_mul_log_log` for the
underlying algebraic identity, valid for all `n`). -/
theorem refinedReservoirCorrected_ratio_ge_log_log
    (n z : ℕ) (_hn : 27 ≤ n) :
    refinedReservoir n z * Real.log (Real.log (n : ℝ))
      = refinedReservoirCorrected n z :=
  (refinedReservoirCorrected_eq_refinedReservoir_mul_log_log n z).symm

/-! ## Section 5 — P20-T1 summary

The corrected reservoir is now defined and shown to dominate the
original `refinedReservoir` for `n ≥ 27`.  This sets up subsequent
P20 tasks:

* P20-T2 (next): rebuild `BrunGoldbachPairedMainTermRefinedAtSqrt`
  with `refinedReservoirCorrected` in place of `refinedReservoir`,
  and verify that the primorial counter-witnesses of P19-T51 / T45 /
  T50 are now **defused** (the extra `log log n` factor in the
  reservoir absorbs the singular-series growth).
* P20-T3 (later): formalise the Mertens-3rd-theorem residue product
  bound `∏_{p ∣ n, p ≥ 3} (p−1)/(p−2) = O(log log n)`, completing
  the analytic justification for the corrected reservoir form. -/

end PathCRefinedReservoirCorrected
end Gdbh

/-! ## Section 6 — Axiom audit -/

#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_def
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_indep_of_z
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_nonneg
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_pos_of_n_ge_three
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_ge_original
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_eq_refinedReservoir_mul_log_log
#print axioms Gdbh.PathCRefinedReservoirCorrected.refinedReservoirCorrected_ratio_ge_log_log
