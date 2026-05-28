/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P18-T3 (Phase 18 / Path C — Honest reduction of the
        `PairedMainTermResidualLowRegion` residual)
-/
import Gdbh.PathC_PairedBrunLargeZ

/-!
# Path C — P18-T3: Honest reduction of `PairedMainTermResidualLowRegion`

This file is the **P18-T3 deliverable** in Phase 18 (Path C residual
splitting).  Its task is to either close
`Gdbh.PathCPairedBrunLargeZ.PairedMainTermResidualLowRegion` honestly,
or — failing that — expose its precise irreducible content as a
named sub-Prop.

## Mathematical analysis (honest)

The residual asks: there exist `C₁ > 0` and `N₀ : ℕ` such that for all
`n z : ℕ` with `0 < n` and (`n < N₀` or `z < Nat.sqrt n`),

```
(goldbachSiftedPair n z : ℝ)
  ≤ C₁ · n · pairedBrunFactor z + n / (log n)² .
```

The two disjuncts behave very differently:

### Disjunct A: `n < N₀` (closable for `N₀ = 3`)

Take `N₀ = 3`.  Then `n ∈ {1, 2}`:

* `n = 1`: the sift set is empty (range `[1, 0]` is empty), so
  `goldbachSiftedPair 1 z = 0` for all `z`.  Bound trivial.

* `n = 2`: `goldbachSiftedPair 2 z ≤ 1` (one element in `[1, 1]`),
  while `refinedReservoir 2 z = 2 / (log 2)² ≈ 4.16 > 1`, so the
  reservoir alone dominates.

Both cases close *unconditionally* with any `C₁ > 0`.

### Disjunct B: `z < Nat.sqrt n` (genuinely a Brun-Bonferroni instance)

Subcase B1: `z ≤ 2`.  Then `pairedBrunFactor z = 1` (empty product),
so the inequality reduces to
`goldbachSiftedPair n z ≤ C₁ · n + n / (log n)²`, satisfied for
`C₁ ≥ 1` by the trivial cardinal bound `goldbachSiftedPair n z ≤ n`
(plus reservoir non-negativity).  Closable with `C₁ = 1`.

Subcase B2: `3 ≤ z < Nat.sqrt n` (which forces `n > 9`).  Here
`pairedBrunFactor z < 1` is strictly decreasing.  We need a uniform
upper bound

```
goldbachSiftedPair n z  ≤  C · n · pairedBrunFactor z + n / (log n)² ,
```

with `C` independent of both `n` and `z` (for `z ∈ [3, √n - 1]`).
This is precisely a Brun-Bonferroni bound *at the threshold `z`*,
parallel to `BrunGoldbachPairedMainTermRefinedAtSqrt` but for the
broader range `z ∈ [3, √n - 1]`.

**Crucially**:

* The AtSqrt slice gives a bound at `z = √n` only, where
  `pairedBrunFactor (√n)` is much smaller than `pairedBrunFactor z`
  for `z < √n`.  Antitonicity of `goldbachSiftedPair` in `z` goes the
  *wrong* direction here:
  `goldbachSiftedPair n z ≥ goldbachSiftedPair n (√n)` for `z ≤ √n`.

* The cardinal bound `goldbachSiftedPair n z ≤ n` does not help:
  the inequality `n ≤ C · n · pairedBrunFactor z + n/(log n)²`
  forces `pairedBrunFactor z ≥ (1 - 1/(log n)²)/C`, but
  `pairedBrunFactor z → 0` as `z → ∞` (along a sub-`√n` window
  whose right endpoint grows with `n`), so no uniform `C` exists.

Therefore Subcase B2 is **NOT closable from existing material**:
it is a genuine Brun-Bonferroni instance, no different in
mathematical content from `BrunGoldbachPairedMainTermRefinedAtSqrt`
restricted to `z = √n`.  We expose it as a named open Prop
`PairedBrunBonferroniSubSqrt` below.

## Deliverables of this file

1. **`PairedBrunBonferroniSubSqrt`** — the precise honest residual,
   covering Subcase B2.

2. **`pairedMainTermResidualLowRegion_of_subSqrt`** — forward bridge
   showing that `PairedBrunBonferroniSubSqrt` together with the
   *unconditional* closures of Disjunct A and Subcase B1 closes
   `PairedMainTermResidualLowRegion`.

3. **Honest assessment** in the docstrings: this residual *is* a
   genuine Brun-Bonferroni instance and cannot be discharged from
   AtSqrt alone.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom budget: `Classical.choice`, `Quot.sound`, `propext` only.
-/

namespace Gdbh
namespace PathCPairedBrunLowRegion

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet mem_goldbachSiftedPairSet
   goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (refinedReservoir_nonneg pairedBrunFactor_eq_one_of_le_two)
open Gdbh.PathCPairedBrunLargeZ
  (PairedMainTermResidualLowRegion
   goldbachSiftedPair_eq_zero_of_large_z_real
   pairedBrunFactor_antitone)

/-! ## Section 1 — Unconditional small-`n` cases

We close the `n ∈ {1, 2}` cases of the residual *without* any
external Prop.  This justifies taking `N₀ = 3` in the bridge below. -/

/-- **`n = 1` collapse.**  For `n = 1`, `goldbachSiftedPair 1 z = 0`
because the range `[1, 0]` is empty. -/
theorem goldbachSiftedPair_one_eq_zero (z : ℕ) :
    goldbachSiftedPair 1 z = 0 := by
  classical
  unfold goldbachSiftedPair goldbachSiftedPairSet
  have h_empty : (Finset.Icc 1 (1 - 1) : Finset ℕ) = ∅ := by
    apply Finset.Icc_eq_empty; omega
  rw [h_empty]
  simp

/-- **`n = 2` cardinal bound.**  `goldbachSiftedPair 2 z ≤ 1`
for every `z`, since the candidate range `[1, 1]` has at most one
element. -/
theorem goldbachSiftedPair_two_le_one (z : ℕ) :
    goldbachSiftedPair 2 z ≤ 1 := by
  classical
  unfold goldbachSiftedPair goldbachSiftedPairSet
  refine le_trans (Finset.card_filter_le _ _) ?_
  -- `Finset.Icc 1 (2 - 1) = Finset.Icc 1 1` has cardinality `1`.
  have : (Finset.Icc 1 (2 - 1) : Finset ℕ).card = 1 := by
    rw [Nat.card_Icc]
  omega

/-- **Reservoir lower bound at `n = 2`.**  `refinedReservoir 2 z =
2/(log 2)² > 1`. -/
theorem refinedReservoir_two_gt_one (z : ℕ) :
    (1 : ℝ) < refinedReservoir 2 z := by
  show (1 : ℝ) < (2 : ℝ) / (Real.log 2)^2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h2_lt_exp : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    have : Real.log 2 < Real.log (Real.exp 1) :=
      Real.log_lt_log (by norm_num) h2_lt_exp
    rwa [Real.log_exp] at this
  have hsq_lt_one : (Real.log 2)^2 < 1 := by
    have h := sq_lt_sq' (by linarith) hlog2_lt_one
    simpa using h
  have hsq_pos : 0 < (Real.log 2)^2 := by positivity
  rw [lt_div_iff₀ hsq_pos]; linarith

/-- **Disjunct A closure** (`n < 3` case).  For `n ∈ {1, 2}` and any
`z`, the residual inequality holds with any `C₁ ≥ 0`. -/
theorem residual_low_region_of_n_lt_three
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) {n z : ℕ} (hn : 0 < n) (h_n_lt_3 : n < 3) :
    (goldbachSiftedPair n z : ℝ)
      ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  have h_main_nn : 0 ≤ C₁ * (n : ℝ) * pairedBrunFactor z :=
    mul_nonneg (mul_nonneg hC₁ h_n_nn) h_pf_nn
  have h_res_nn : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
  interval_cases n
  · -- n = 1: sift = 0.
    have h_sift : (goldbachSiftedPair 1 z : ℝ) = 0 := by
      rw [goldbachSiftedPair_one_eq_zero z]; norm_num
    linarith
  · -- n = 2: sift ≤ 1, reservoir > 1.
    have h_sift_le_one : (goldbachSiftedPair 2 z : ℝ) ≤ 1 := by
      exact_mod_cast goldbachSiftedPair_two_le_one z
    have h_res_gt_one : (1 : ℝ) < refinedReservoir 2 z :=
      refinedReservoir_two_gt_one z
    linarith

/-! ## Section 2 — Subcase B1: `z ≤ 2`

For `z ≤ 2`, `pairedBrunFactor z = 1` (empty product), so the bound
reduces to the trivial cardinal bound. -/

/-- **Subcase B1 closure** (`z ≤ 2`).  For any `n > 0` and `z ≤ 2`,
the residual inequality holds with `C₁ = 1`. -/
theorem residual_low_region_of_z_le_two
    {n z : ℕ} (hn : 0 < n) (hz : z ≤ 2) :
    (goldbachSiftedPair n z : ℝ)
      ≤ 1 * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
  have hM : pairedBrunFactor z = 1 := pairedBrunFactor_eq_one_of_le_two hz
  have hSift : (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le n z
  have hRes : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
  have hRHS :
      1 * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z
        = (n : ℝ) + refinedReservoir n z := by
    rw [hM]; ring
  rw [hRHS]; linarith

/-! ## Section 3 — The honest sub-`√n` Brun-Bonferroni residual

Subcase B2 — `3 ≤ z < Nat.sqrt n` (equivalently, `n ≥ 10` and
`3 ≤ z ≤ Nat.sqrt n - 1`) — is **not closable from existing material**.
Antitonicity of `goldbachSiftedPair` in `z` goes the wrong direction
(it gives a lower bound at `√n`, not an upper bound at `z < √n`),
and `pairedBrunFactor z → 0` as `z` ranges through the (unbounded)
sub-`√n` window, so no uniform constant can absorb the gap from the
trivial cardinal bound `goldbachSiftedPair n z ≤ n`.

We expose this honest content as a named open sub-Prop. -/

/-- **`PairedBrunBonferroniSubSqrt`.**  The sub-`√n` Brun-Bonferroni
bound:

```
∃ C : ℝ, 0 < C ∧ ∀ n z : ℕ, 0 < n → 3 ≤ z → z < Nat.sqrt n →
  (goldbachSiftedPair n z : ℝ)
    ≤ C · n · pairedBrunFactor z + refinedReservoir n z .
```

**Mathematical status**: classical, equivalent to a Brun-Bonferroni
bound at each sub-`√n` threshold.  Proof scaffolding parallel to
`BrunGoldbachPairedMainTermRefinedAtSqrt` (combinatorial inclusion-
exclusion truncation at even depth `k`), but applied uniformly over
the sub-`√n` window.

**Cannot be reduced to AtSqrt alone**: antitonicity of
`goldbachSiftedPair` in `z` goes the wrong way for `z < √n`, and
`pairedBrunFactor z` is too large to absorb the gap. -/
def PairedBrunBonferroniSubSqrt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n z : ℕ, 0 < n → 3 ≤ z → z < Nat.sqrt n →
    (goldbachSiftedPair n z : ℝ)
      ≤ C * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z

/-! ## Section 4 — Forward bridge: SubSqrt closes Residual

Given `PairedBrunBonferroniSubSqrt`, we close
`PairedMainTermResidualLowRegion` using `N₀ = 3` and a constant
`C₁ = max(C_subSqrt, 1) + 1`. -/

/-- **The forward bridge.**  Given the sub-`√n` Brun-Bonferroni
residual, we close `PairedMainTermResidualLowRegion` with
`N₀ = 3`. -/
theorem pairedMainTermResidualLowRegion_of_subSqrt
    (hSubSqrt : PairedBrunBonferroniSubSqrt) :
    PairedMainTermResidualLowRegion := by
  classical
  obtain ⟨C_sub, hC_sub_pos, hSubBd⟩ := hSubSqrt
  -- Uniform absorption constant.
  set C₁ : ℝ := max C_sub 1 + 1 with hC₁_def
  have hC₁_pos : 0 < C₁ := by
    rw [hC₁_def]
    have h_max_nn : 0 ≤ max C_sub 1 :=
      le_max_of_le_left (le_of_lt hC_sub_pos)
    linarith
  have hC₁_nn : 0 ≤ C₁ := le_of_lt hC₁_pos
  refine ⟨C₁, 3, hC₁_pos, ?_⟩
  intro n z hn hcond
  rcases hcond with h_n_lt_3 | h_z_lt_sqrt
  · -- Disjunct A: n < 3.
    exact residual_low_region_of_n_lt_three hC₁_nn hn h_n_lt_3
  · -- Disjunct B: z < √n.
    by_cases hz_le_2 : z ≤ 2
    · -- Subcase B1: z ≤ 2.
      have h := residual_low_region_of_z_le_two hn hz_le_2
      have h_one_le_C₁ : (1 : ℝ) ≤ C₁ := by
        rw [hC₁_def]
        have : (1 : ℝ) ≤ max C_sub 1 := le_max_right _ _
        linarith
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_main_le : 1 * (n : ℝ) * pairedBrunFactor z
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : (1 : ℝ) * ((n : ℝ) * pairedBrunFactor z)
            ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right h_one_le_C₁ h_n_pf_nn
        linarith [this]
      linarith
    · -- Subcase B2: z ≥ 3 AND z < √n.
      push_neg at hz_le_2
      have hz_ge_3 : 3 ≤ z := hz_le_2
      have h := hSubBd n z hn hz_ge_3 h_z_lt_sqrt
      have h_sub_le_C₁ : C_sub ≤ C₁ := by
        rw [hC₁_def]
        have : C_sub ≤ max C_sub 1 := le_max_left _ _
        linarith
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_main_le : C_sub * (n : ℝ) * pairedBrunFactor z
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : C_sub * ((n : ℝ) * pairedBrunFactor z)
            ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right h_sub_le_C₁ h_n_pf_nn
        linarith [this]
      linarith

/-! ## Section 5 — Honest residual exposure

The `PairedMainTermResidualLowRegion` Prop is **not closeable
unconditionally** from existing material.  The honest residual is
`PairedBrunBonferroniSubSqrt`.

The other two sub-disjuncts (`n < 3` and `z ≤ 2`) are closed
unconditionally above.  We package the conclusion as the explicit
reduction `Residual ← SubSqrt`. -/

/-- **Honest exposure of the residual.**  The
`PairedMainTermResidualLowRegion` Prop reduces to a single named
open sub-Prop `PairedBrunBonferroniSubSqrt`.

The reduction is *via the forward bridge*
`pairedMainTermResidualLowRegion_of_subSqrt`. -/
theorem pairedMainTermResidualLowRegion_honest_reduction :
    PairedBrunBonferroniSubSqrt → PairedMainTermResidualLowRegion :=
  pairedMainTermResidualLowRegion_of_subSqrt

/-! ## Section 6 — Catch defusal for the SubSqrt Prop

We check that the refactored SubSqrt Prop is **not** trivially
disproved by any small-`n` witness.  Since the Prop only quantifies
over `n` with `Nat.sqrt n > z ≥ 3`, the smallest relevant `n` is
`n = 10` (with `z = 3` and `Nat.sqrt 10 = 3`, so the range is
`z < 3` which is empty; the smallest non-trivial case is
`n = 16`, `z = 3`, `Nat.sqrt 16 = 4`).

The Prop is therefore vacuous on small `n` (no `z` satisfies the
constraints), so cannot be refuted by a finite witness. -/

/-- **SubSqrt Prop is not vacuously refuted on small `n`.**  For
`n ≤ 9`, no `z` satisfies `3 ≤ z < Nat.sqrt n`, so the Prop's
conjunction is vacuous on these `n`. -/
theorem subSqrt_vacuous_on_small_n
    {n z : ℕ} (h_n_le_9 : n ≤ 9) (hz_ge_3 : 3 ≤ z)
    (hz_lt_sqrt : z < Nat.sqrt n) : False := by
  -- `Nat.sqrt n ≤ Nat.sqrt 9 ≤ 3`, since `4^2 = 16 > 9`.
  have h_sqrt_le_sqrt9 : Nat.sqrt n ≤ Nat.sqrt 9 := Nat.sqrt_le_sqrt h_n_le_9
  have h_sqrt9_lt_4 : Nat.sqrt 9 < 4 := by
    apply Nat.sqrt_lt.mpr
    norm_num
  omega

end PathCPairedBrunLowRegion
end Gdbh
