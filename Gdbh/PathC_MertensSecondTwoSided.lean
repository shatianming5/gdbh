/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T9 (Phase 19 / Path C — symmetric two-sided Mertens 2nd
        extraction + paired-Brun Mertens 3rd LOWER gap closure)
-/
import Gdbh.PathC_AbelInversion
import Gdbh.PathC_AbelPrimeRecipIdentity
import Gdbh.PathC_AbelIntegrandSplit
import Gdbh.PathC_LogRecipIntegral
import Gdbh.PathC_MertensErrorIntegral
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_MertensFirstUpper
import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_MertensThirdProof
import Gdbh.PathC_PairedBrunMertensLowerReal

/-!
# Path C — Symmetric two-sided Mertens 2nd extraction (P19-T9)

This file finishes the dual half of the Abel-summation chain.  The
**P19-T2 finding** observed that the existing `MertensFirstTheoremBound`
is *implicitly* two-sided (its statement uses absolute value).  The
P11-T1 `AbelInversionMertensSecondFromFirst` arrow likewise feeds on
two-sided inputs (`|IntLog − log log z| ≤ C`, `|IntErr| ≤ B'`,
`|M(z) − log z| ≤ B`), but only the *lower* direction is exposed in
`MertensSecondLowerBoundFull`.

The dual upper direction is **closeable by the same arithmetic**, with
all four inequalities flipped from `−` to `+`.  We do that here, then
combine with a clean Taylor bound `log(1 − 2/p) ≥ −2/p − 12/p²` to close
the named open
`Gdbh.PathCPairedBrunMertensLowerReal.PairedBrunMertensThirdLowerGap`.

## Investigation finding

* `MertensFirstTheoremBound` (two-sided `|·| ≤ B`):
  closed axiom-clean as
  `Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds`.

* `AbelInversionMertensSecondFromFirst` is **closed** axiom-clean as
  `Gdbh.PathCClosedReductions.abelInversionMertensSecondFromFirst_holds`,
  but its target `MertensSecondLowerBoundFull` is stated **only as a
  lower bound** (`log log z − B ≤ Σ 1/p`).  All four sub-Props that
  feed into it (`LogReciprocalIntegralAsymptotic`,
  `MertensErrorIntegralBound`, `AbelPrimeReciprocalIdentity`,
  `AbelIntegrandSplit`) are two-sided/symmetric — so the upper
  direction `Σ 1/p ≤ log log z + B''` is *equally available* by the
  same arithmetic with flipped signs.  We do that derivation here.

## Main results

* `MertensSecondUpperBound` — `∃ B, ∃ z₀, ∀ z ≥ z₀,
  Σ_{2 ≤ p ≤ z, prime} 1/p ≤ log log z + B`.
  Closed axiom-clean via the dual Abel argument.

* `MertensSecondUpperBoundOdd` — same bound restricted to `3 ≤ p`.
  Closed axiom-clean (drop `1/2`, keep the constant).

* `log_one_sub_two_div_prime_ge` — Taylor's lower bound
  `log(1 − 2/p) ≥ −2/(p − 2)` for `p ≥ 3` prime.  Closed axiom-clean
  via `Real.log_le_sub_one_of_pos` applied to `(1 − 2/p)⁻¹`.

* `two_div_p_sub_two_le_two_div_p_add_twelve_div_p_sq` — the elementary
  bound `2/(p − 2) ≤ 2/p + 12/p²` for `p ≥ 3`.  Closed by `nlinarith`.

* `sum_inv_sq_prime_le_half` — `Σ_{3 ≤ p ≤ z, prime} 1/p² ≤ 1/2`.
  Closed by telescoping `1/n² ≤ 1/(n(n−1))`.

* `pairedBrunMertensThirdLowerGap_holds` — closure of the named open
  `PairedBrunMertensThirdLowerGap`, axiom-clean.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCMertensSecondTwoSided

open Real Finset
open Gdbh.PathCMertensSecondProof (MertensFirstTheoremBound)
open Gdbh.PathCAbelInversion
  (AbelPrimeReciprocalIdentity LogReciprocalIntegralAsymptotic
   MertensErrorIntegralBound AbelIntegrandSplit mertensFirstSum)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos
  one_sub_two_div_prime_pos)
open Gdbh.PathCMertensThirdProof (log_pairedBrunFactor_eq_sum)
open Gdbh.PathCPairedBrunMertensLowerReal (PairedBrunMertensThirdLowerGap)

/-! ## Section 1 — Definitions: Mertens 2nd UPPER bound -/

/-- **Named Prop**: full (un-restricted) Mertens 2nd upper bound.

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  ∑_{2 ≤ p ≤ z, p prime} 1/p  ≤  log log z + B .
```

The classical Mertens 2nd theorem: `Σ_{p ≤ z} 1/p = log log z + M + o(1)`,
restricted to the upper-bound side. -/
def MertensSecondUpperBound : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (Real.log (z : ℝ)) + B

/-- **Named Prop**: odd-restricted Mertens 2nd upper bound.

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  ∑_{3 ≤ p ≤ z, p prime} 1/p  ≤  log log z + B .
```

Follows from `MertensSecondUpperBound` by dropping the `p = 2` term
`1/2`, keeping `B` (since `1/2 > 0` only decreases the LHS). -/
def MertensSecondUpperBoundOdd : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (Real.log (z : ℝ)) + B

/-! ## Section 2 — Dual Abel argument for the upper direction

The proof is a sign-flipped clone of
`abelInversionMertensSecondFromFirst_of_components`.  All four
sub-Props are two-sided absolute-value bounds, so the same arithmetic
yields the upper bound. -/

/-- **Dual Abel arrow**: the same four sub-Props that close the lower
direction also close the upper direction.

This is the *symmetric* twin of
`Gdbh.PathCAbelInversion.abelInversionMertensSecondFromFirst_of_components`. -/
theorem mertensSecondUpperBound_of_first_and_abel_components
    (hM1 : MertensFirstTheoremBound)
    (hAbelId : AbelPrimeReciprocalIdentity)
    (hLogInt : LogReciprocalIntegralAsymptotic)
    (hErrBd : MertensErrorIntegralBound)
    (hSplit : AbelIntegrandSplit) :
    MertensSecondUpperBound := by
  -- Extract M1 witnesses.
  obtain ⟨B, z₀_M1, hM1bound⟩ := hM1
  -- B ≥ 0 since |·| ≥ 0 at z = max z₀_M1 2.
  have hB_nonneg : 0 ≤ B := by
    have hz : z₀_M1 ≤ max z₀_M1 2 := le_max_left _ _
    have := hM1bound (max z₀_M1 2) hz
    exact le_trans (abs_nonneg _) this
  -- Extract Abel identity witness.
  obtain ⟨z₀_Id, hIdEq⟩ := hAbelId
  -- Extract log-reciprocal integral witness.
  obtain ⟨C, z₀_Int, hIntBd⟩ := hLogInt
  -- Extract error-integral witness (at the M1 constant B).
  obtain ⟨B', z₀_Err, hErrBound⟩ := hErrBd B hB_nonneg
  -- Final constant: C + B' + B/log 2 + 1 (sign-flipped from − 1 in the lower form).
  refine ⟨C + B' + B / Real.log 2 + 1,
    max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)), ?_⟩
  intro z hz
  -- Unpack the nested `max` into individual lower bounds.
  have hz_M1 : z₀_M1 ≤ z := by
    have h1 : z₀_M1 ≤ max z₀_M1 z₀_Id := le_max_left _ _
    have h2 : max z₀_M1 z₀_Id ≤ max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Id : z₀_Id ≤ z := by
    have h1 : z₀_Id ≤ max z₀_M1 z₀_Id := le_max_right _ _
    have h2 : max z₀_M1 z₀_Id ≤ max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Int : z₀_Int ≤ z := by
    have h1 : z₀_Int ≤ max z₀_Int (max z₀_Err 2) := le_max_left _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
    exact (h1.trans h2).trans hz
  have hz_Err : z₀_Err ≤ z := by
    have h0 : z₀_Err ≤ max z₀_Err 2 := le_max_left _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
    exact ((h0.trans h1).trans h2).trans hz
  have hz_two : (2 : ℕ) ≤ z := by
    have h0 : (2 : ℕ) ≤ max z₀_Err 2 := le_max_right _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
    exact ((h0.trans h1).trans h2).trans hz
  have hz_two_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_two
  -- Abbreviate the four quantities.
  set Sum := (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    with hSum_def
  set Mz := mertensFirstSum (z : ℝ) with hMz_def
  set IntM := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
                mertensFirstSum t / (t * (Real.log t)^2) with hIntM_def
  set IntLog := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ), 1 / (t * Real.log t)
    with hIntLog_def
  set IntErr := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
                  (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)
    with hIntErr_def
  -- 1. Abel identity: Sum = Mz/log z + IntM.
  have hId : Sum = Mz / Real.log (z : ℝ) + IntM := hIdEq z hz_Id
  -- 2. Integrand split: IntM = IntLog + IntErr.
  have hSplit_eq : IntM = IntLog + IntErr := by
    rw [hIntM_def, hIntLog_def, hIntErr_def]
    exact hSplit (z : ℝ) hz_two_real
  -- 3. M1 absolute-value bound at the natural endpoint z.
  have hMz_unfold : Mz =
      ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
    simp [hMz_def, mertensFirstSum, Nat.floor_natCast]
  have hM1_z : |Mz - Real.log (z : ℝ)| ≤ B := by
    rw [hMz_unfold]; exact hM1bound z hz_M1
  -- Linearize the absolute-value bound: Mz ≤ log z + B (UPPER direction).
  have hMz_upper : Mz ≤ Real.log (z : ℝ) + B := by
    have hAbs := abs_le.mp hM1_z; linarith [hAbs.2]
  -- 4. Integral asymptotic: IntLog ≤ log log z + C (UPPER direction).
  have hIntLog_abs : |IntLog - Real.log (Real.log (z : ℝ))| ≤ C :=
    hIntBd z hz_Int
  have hIntLog_upper : IntLog ≤ Real.log (Real.log (z : ℝ)) + C := by
    have hAbs := abs_le.mp hIntLog_abs; linarith [hAbs.2]
  -- 5. Error-integral bound: IntErr ≤ B' (UPPER direction).
  have hIntErr_abs : |IntErr| ≤ B' := hErrBound z hz_Err
  have hIntErr_upper : IntErr ≤ B' := by
    have hAbs := abs_le.mp hIntErr_abs; linarith [hAbs.2]
  -- 6. Boundary term: Mz/log z ≤ 1 + B/log 2.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz_pos : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hz_two_real
  have hlogz_ge : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) hz_two_real
  have hMz_over_logz : Mz / Real.log (z : ℝ) ≤ 1 + B / Real.log 2 := by
    -- (log z + B) / log z = 1 + B/log z, and 1 + B/log z ≤ 1 + B/log 2.
    have h_div : Mz / Real.log (z : ℝ)
                  ≤ (Real.log (z : ℝ) + B) / Real.log (z : ℝ) :=
      div_le_div_of_nonneg_right hMz_upper hlogz_pos.le
    have h_split : (Real.log (z : ℝ) + B) / Real.log (z : ℝ)
                    = 1 + B / Real.log (z : ℝ) := by
      field_simp
    have h_mono : B / Real.log (z : ℝ) ≤ B / Real.log 2 :=
      div_le_div_of_nonneg_left hB_nonneg hlog2_pos hlogz_ge
    linarith [h_div, h_split, h_mono]
  -- Goal: Sum ≤ log log z + (C + B' + B/log 2 + 1).
  -- Substitute hId, hSplit_eq:
  -- Sum = Mz/log z + IntM = Mz/log z + IntLog + IntErr.
  -- ≤ (1 + B/log 2) + (log log z + C) + B'.
  rw [hSum_def] at hId
  linarith [hId, hSplit_eq, hMz_over_logz, hIntLog_upper, hIntErr_upper]

/-- **Headline closure** of `MertensSecondUpperBound`.

Combines the closed M1 with the closed Abel-inversion components.  All
five inputs are axiom-clean, so the closure is axiom-clean. -/
theorem mertensSecondUpperBound_holds : MertensSecondUpperBound :=
  mertensSecondUpperBound_of_first_and_abel_components
    Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds
    Gdbh.PathCAbelPrimeRecipIdentity.abelPrimeReciprocalIdentity
    Gdbh.PathCLogRecipIntegral.logReciprocalIntegralAsymptotic_closed
    Gdbh.PathCMertensErrorIntegral.mertensErrorIntegralBound_holds
    Gdbh.PathCAbelIntegrandSplit.abelIntegrandSplit_holds

/-- **Odd-restricted** Mertens 2nd UPPER bound from the full form.

Dropping the `p = 2` contribution `1/2` decreases the sum, so the
upper bound for the full sum implies an upper bound for the odd-only
sum (with the same constant; we keep `B` for simplicity). -/
theorem mertensSecondUpperBoundOdd_of_full
    (h : MertensSecondUpperBound) :
    MertensSecondUpperBoundOdd := by
  obtain ⟨B, z₀, hbound⟩ := h
  refine ⟨B, max z₀ 2, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz2 : 2 ≤ z := le_trans (le_max_right _ _) hz
  -- Σ_{3 ≤ p ≤ z, prime} 1/p = Σ_{2 ≤ p ≤ z, prime} 1/p - 1/2 ≤ Σ_{2 ≤ p ≤ z, prime} 1/p.
  have hsplit :
      (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        = (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          + (1 : ℝ) / 2 := by
    have hIcc2 : Finset.Icc 2 z = insert 2 (Finset.Icc 3 z) := by
      ext n
      simp only [Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact Or.inl rfl
        · exact Or.inr ⟨h1', h2⟩
      · intro h
        rcases h with h | ⟨h1, h2⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, h2⟩
    have h2_not_mem : (2 : ℕ) ∉ Finset.Icc 3 z := by
      simp [Finset.mem_Icc]
    have hfilter_insert :
        (Finset.Icc 2 z).filter Nat.Prime
          = insert 2 ((Finset.Icc 3 z).filter Nat.Prime) := by
      rw [hIcc2]
      rw [Finset.filter_insert]
      simp [Nat.prime_two]
    have h2_not_in_filter :
        (2 : ℕ) ∉ (Finset.Icc 3 z).filter Nat.Prime := by
      intro hmem
      exact h2_not_mem (Finset.mem_filter.mp hmem).1
    rw [hfilter_insert, Finset.sum_insert h2_not_in_filter]
    have : (1 : ℝ) / ((2 : ℕ) : ℝ) = (1 : ℝ) / 2 := by norm_num
    linarith [this]
  have hfull_upper :
      (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B := hbound z hz0
  linarith [hsplit, hfull_upper]

/-- **Headline closure** of `MertensSecondUpperBoundOdd`.  Same constant as the
full form (since dropping `1/2` only makes the LHS smaller). -/
theorem mertensSecondUpperBoundOdd_holds : MertensSecondUpperBoundOdd :=
  mertensSecondUpperBoundOdd_of_full mertensSecondUpperBound_holds

/-! ## Section 3 — Taylor lower bound for `log(1 − 2/p)`

For `p ≥ 3` prime, we use the convex bound

```
log(1 − 2/p) ≥ −2/(p − 2) .
```

This is `Real.log_le_sub_one_of_pos` applied to `(1 − 2/p)⁻¹`.  We
then bound `2/(p − 2) ≤ 2/p + 12/p²` to give a clean two-term Taylor
form. -/

/-- **First-order Taylor lower bound**: for `p ≥ 3` real,
`log(1 − 2/p) ≥ −2/(p − 2)`.

Apply `log y ≤ y − 1` (mathlib `Real.log_le_sub_one_of_pos`) to
`y = (1 − 2/p)⁻¹ > 0`:

```
log((1 − 2/p)⁻¹) ≤ (1 − 2/p)⁻¹ − 1 = (2/p) / (1 − 2/p) = 2/(p − 2) .
```

Since `log((1 − 2/p)⁻¹) = −log(1 − 2/p)`, this gives the lower bound. -/
lemma log_one_sub_two_div_ge_neg_two_div_sub_two
    {p : ℝ} (hp : (3 : ℝ) ≤ p) :
    -(2 / (p - 2)) ≤ Real.log (1 - 2 / p) := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_sub_two_pos : (0 : ℝ) < p - 2 := by linarith
  have h_one_sub : (0 : ℝ) < 1 - 2 / p := by
    have h1 : (2 : ℝ) / p ≤ 2 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
    linarith
  have h_inv : (0 : ℝ) < (1 - 2 / p)⁻¹ := inv_pos.mpr h_one_sub
  -- log y ≤ y - 1 at y = (1 - 2/p)⁻¹.
  have h_log_le : Real.log ((1 - 2 / p)⁻¹) ≤ (1 - 2 / p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos h_inv
  -- log((1 - 2/p)⁻¹) = -log(1 - 2/p).
  have h_log_inv : Real.log ((1 - 2 / p)⁻¹) = -Real.log (1 - 2 / p) := by
    rw [Real.log_inv]
  -- (1 - 2/p)⁻¹ - 1 = 2/(p - 2).
  have h_arith : (1 - 2 / p)⁻¹ - 1 = 2 / (p - 2) := by
    have h_ne : (1 - 2 / p) ≠ 0 := ne_of_gt h_one_sub
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hp_sub_ne : (p - 2) ≠ 0 := ne_of_gt hp_sub_two_pos
    field_simp
    ring
  rw [h_log_inv] at h_log_le
  rw [h_arith] at h_log_le
  linarith

/-- **Two-term Taylor bound**: for real `p ≥ 3`,
`2/(p − 2) ≤ 2/p + 12/p²`.

Direct algebraic verification.  Equivalent to
`2 · p² ≤ (2/p + 12/p²) · p² · (p - 2) = (2p + 12) · (p - 2) = 2p² + 8p - 24`,
i.e., `0 ≤ 8p - 24`, i.e., `p ≥ 3`. -/
lemma two_div_p_sub_two_le_two_div_p_plus_twelve_div_p_sq
    {p : ℝ} (hp : (3 : ℝ) ≤ p) :
    (2 : ℝ) / (p - 2) ≤ 2 / p + 12 / p^2 := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_sq_pos : (0 : ℝ) < p^2 := by positivity
  have hp_sub_two_pos : (0 : ℝ) < p - 2 := by linarith
  -- Multiply through by `p^2 · (p − 2) > 0`.  After clearing denominators:
  -- 2 · p² ≤ (2p + 12) · (p − 2) = 2p² + 8p − 24.  Difference: 0 ≤ 8p − 24, i.e., 3 ≤ p.
  have h_diff : 2 / p + 12 / p^2 - 2 / (p - 2)
      = (2 * p * (p - 2) + 12 * (p - 2) - 2 * p^2) / (p^2 * (p - 2)) := by
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hp_sub_ne : p - 2 ≠ 0 := ne_of_gt hp_sub_two_pos
    field_simp
  have h_numer_nn : (0 : ℝ) ≤ 2 * p * (p - 2) + 12 * (p - 2) - 2 * p^2 := by
    nlinarith [hp]
  have h_denom_pos : (0 : ℝ) < p^2 * (p - 2) := by positivity
  have h_div_nn : (0 : ℝ) ≤ (2 * p * (p - 2) + 12 * (p - 2) - 2 * p^2) / (p^2 * (p - 2)) :=
    div_nonneg h_numer_nn (le_of_lt h_denom_pos)
  linarith [h_diff, h_div_nn]

/-- **Combined Taylor lower bound** for primes:
`log(1 − 2/p) ≥ −2/p − 12/p²` for `p ≥ 3` prime. -/
lemma log_one_sub_two_div_prime_ge {p : ℕ} (hp : 3 ≤ p) :
    -(2 / (p : ℝ)) - 12 / (p : ℝ)^2 ≤ Real.log (1 - 2 / (p : ℝ)) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : -(2 / ((p : ℝ) - 2)) ≤ Real.log (1 - 2 / (p : ℝ)) :=
    log_one_sub_two_div_ge_neg_two_div_sub_two hp_real
  have h2 : (2 : ℝ) / ((p : ℝ) - 2) ≤ 2 / (p : ℝ) + 12 / (p : ℝ)^2 :=
    two_div_p_sub_two_le_two_div_p_plus_twelve_div_p_sq hp_real
  linarith

/-! ## Section 4 — Summed Taylor lower bound -/

/-- **Sum-form Taylor lower bound**: over `3 ≤ p ≤ z` prime,
`Σ log(1 − 2/p) ≥ −2 Σ 1/p − 12 Σ 1/p²`. -/
lemma sum_log_pairedBrunFactor_ge (z : ℕ) :
    -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      - 12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2
      ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          Real.log (1 - 2 / (p : ℝ)) := by
  -- Rewrite RHS-of-≥ as sum of `-2/p - 12/p²`.
  have hsum_eq :
      -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - 12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2
        = ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
            (-(2 / (p : ℝ)) - 12 / (p : ℝ)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [hsum_eq]
  refine Finset.sum_le_sum ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact log_one_sub_two_div_prime_ge hp3

/-! ## Section 5 — The `Σ 1/p²` tail bound -/

/-- **Telescoping bound**: for natural `n ≥ 3`, `1/n² ≤ 1/(n−1) − 1/n`.

Equivalent to `n − 1 ≤ n² · ((1/(n−1)) − (1/n)) = n² · (1/((n−1) · n)) · ((n−n+1))...`
We expand directly: `1/(n(n−1)) − 1/n² = (n − (n−1))/(n²(n−1)) = 1/(n²(n−1))`.
So `1/n² ≤ 1/n² + 1/(n²(n−1)) = 1/(n(n−1))`.  And
`1/(n(n−1)) = 1/(n−1) − 1/n`. -/
lemma one_div_sq_le_telescope {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / (n : ℝ)^2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_sub : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_sub_ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn_sub
  have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hn_sq_ne : (n : ℝ)^2 ≠ 0 := ne_of_gt hn_sq_pos
  -- Show 1/(n−1) − 1/n − 1/n² ≥ 0.
  -- Compute: 1/(n-1) - 1/n - 1/n² = (n² · n − n² · (n−1) − (n−1) · n) / (n² · n · (n−1))
  --                              = (n² − n² + n² − n² + n) / (n² · n · (n−1))   ... let me redo.
  -- Better: 1/(n-1) - 1/n - 1/n² and clear common denominator n²(n-1):
  --   = (n² - n(n-1) - (n-1)) / (n²(n-1)) = (n² - n² + n - n + 1) / (n²(n-1)) = 1 / (n²(n-1)).
  -- So 1/(n-1) - 1/n - 1/n² = 1/(n²(n-1)) ≥ 0.
  have h_eq : (1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ) - 1 / (n : ℝ)^2
      = 1 / ((n : ℝ)^2 * ((n : ℝ) - 1)) := by
    field_simp
    ring
  have h_rhs_pos : (0 : ℝ) ≤ 1 / ((n : ℝ)^2 * ((n : ℝ) - 1)) := by
    apply div_nonneg (by norm_num)
    positivity
  linarith [h_eq, h_rhs_pos]

/-- **Telescoping equality**: for `z ≥ 3`,
`Σ_{3 ≤ n ≤ z} (1/(n−1) − 1/n) = 1/2 − 1/z`. -/
lemma sum_telescope_eq {z : ℕ} (hz : 3 ≤ z) :
    (∑ n ∈ Finset.Icc 3 z, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)))
      = 1 / 2 - 1 / (z : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base =>
    -- z = 3: single term: 1/(3-1) - 1/3 = 1/2 - 1/3.
    simp only [Finset.Icc_self, Finset.sum_singleton]
    push_cast
    norm_num
  | succ k hk ih =>
    -- Step: add the (k+1)-th term.
    have hkk : Finset.Icc 3 (k + 1) = insert (k + 1) (Finset.Icc 3 k) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hkk]
    have hk_succ_not : (k + 1) ∉ Finset.Icc 3 k := by
      simp [Finset.mem_Icc]
    rw [Finset.sum_insert hk_succ_not, ih]
    have hk_real : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
    have hk_succ_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have hk_succ_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hk_succ_pos
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    -- (1/(k+1-1) - 1/(k+1)) + (1/2 - 1/k) = 1/2 - 1/(k+1).
    -- Term added: 1/((k+1)-1) - 1/(k+1) = 1/k - 1/(k+1).
    -- After ih: (1/k - 1/(k+1)) + (1/2 - 1/k) = 1/2 - 1/(k+1).
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have h_sub_one : ((k : ℝ) + 1) - 1 = (k : ℝ) := by ring
    rw [h_sub_one]
    field_simp
    ring

/-- **Σ 1/n² telescoping bound** over `Finset.Icc 3 z`.  Independent of primes. -/
lemma sum_inv_sq_telescoping (z : ℕ) :
    (∑ n ∈ Finset.Icc 3 z, (1 : ℝ) / (n : ℝ)^2) ≤ (1 : ℝ) / 2 := by
  -- Apply telescoping: Σ_{3 ≤ n ≤ z} (1/(n−1) − 1/n) = 1/2 − 1/z ≤ 1/2.
  -- First, bound termwise: 1/n² ≤ 1/(n(n−1)) = 1/(n−1) − 1/n.
  have h_le :
      (∑ n ∈ Finset.Icc 3 z, (1 : ℝ) / (n : ℝ)^2)
        ≤ ∑ n ∈ Finset.Icc 3 z, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
    exact one_div_sq_le_telescope hn3
  refine le_trans h_le ?_
  rcases lt_or_ge z 3 with hz | hz3
  · -- z < 3: Finset.Icc 3 z = ∅.
    have hempty : Finset.Icc 3 z = ∅ := by
      apply Finset.Icc_eq_empty
      omega
    rw [hempty, Finset.sum_empty]
    norm_num
  · -- z ≥ 3: telescoping equals 1/2 - 1/z ≤ 1/2.
    rw [sum_telescope_eq hz3]
    have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
    have hz_pos : (0 : ℝ) < (z : ℝ) := by linarith
    have h_inv_nn : (0 : ℝ) ≤ 1 / (z : ℝ) := by positivity
    linarith

/-- **Σ 1/p² bound**: the prime sum is bounded by the full natural sum, which
is ≤ 1/2 by telescoping. -/
lemma sum_inv_sq_prime_le_half (z : ℕ) :
    (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
      ≤ (1 : ℝ) / 2 := by
  -- Drop the prime filter (the terms are all nonneg).
  refine le_trans ?_ (sum_inv_sq_telescoping z)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · -- (Finset.Icc 3 z).filter Nat.Prime ⊆ Finset.Icc 3 z
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  · intro n _ _
    positivity

/-! ## Section 6 — Closure of `PairedBrunMertensThirdLowerGap` -/

/-- **Auxiliary**: `exp(−2 log log z − D) = exp(−D) / (log z)²` whenever `z ≥ 3`. -/
lemma exp_neg_two_log_log_sub_eq (z : ℕ) (hz : 3 ≤ z) (D : ℝ) :
    Real.exp (-(2 * Real.log (Real.log (z : ℝ))) - D)
      = Real.exp (-D) / (Real.log (z : ℝ))^2 := by
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- exp(-(2 log log z) - D) = exp(-D) * exp(-2 log log z).
  have h1 : Real.exp (-(2 * Real.log (Real.log (z : ℝ))) - D)
      = Real.exp (-D) * Real.exp (-(2 * Real.log (Real.log (z : ℝ)))) := by
    rw [show -(2 * Real.log (Real.log (z : ℝ))) - D
        = (-D) + (-(2 * Real.log (Real.log (z : ℝ)))) from by ring, Real.exp_add]
  have h2 : Real.exp (-(2 * Real.log (Real.log (z : ℝ))))
      = 1 / (Real.log (z : ℝ))^2 := by
    rw [Real.exp_neg]
    have hexp_two : Real.exp (2 * Real.log (Real.log (z : ℝ)))
        = (Real.log (z : ℝ))^2 := by
      have h2x : (2 : ℝ) * Real.log (Real.log (z : ℝ))
          = Real.log (Real.log (z : ℝ)) + Real.log (Real.log (z : ℝ)) := by ring
      rw [h2x, Real.exp_add, Real.exp_log hlogz_pos]
      ring
    rw [hexp_two]
    field_simp
  rw [h1, h2]
  field_simp

/-- **Headline closure**: `PairedBrunMertensThirdLowerGap` holds axiom-clean.

Combines:
- Mertens 2nd UPPER bound (closed via dual Abel argument): `Σ 1/p ≤ log log z + B''`.
- Taylor lower bound: `log(1 − 2/p) ≥ −2/p − 12/p²`.
- `Σ 1/p² ≤ 1/2` (telescoping).
- Log/exp identity for `pairedBrunFactor`.

Reasoning:

```
log(pairedBrunFactor z) = Σ log(1 − 2/p)              [log_pairedBrunFactor_eq_sum]
                       ≥ −2 Σ 1/p − 12 Σ 1/p²        [Taylor]
                       ≥ −2(log log z + B'') − 12·(1/2)  [M2 upper + tail]
                       = −2 log log z − 2 B'' − 6 .
```

Exponentiating: `pairedBrunFactor z ≥ exp(−2 B'' − 6) / (log z)²`.
Take `K := exp(−2 B'' − 6) > 0`. -/
theorem pairedBrunMertensThirdLowerGap_holds :
    PairedBrunMertensThirdLowerGap := by
  -- Extract the closed Mertens 2nd UPPER bound for ODD primes.
  obtain ⟨B'', z₀_M2, hM2⟩ := mertensSecondUpperBoundOdd_holds
  -- Set K and z₀.
  refine ⟨Real.exp (-(2 * B'') - 6), max z₀_M2 3, Real.exp_pos _, ?_⟩
  intro z hz
  have hz_M2 : z₀_M2 ≤ z := le_trans (le_max_left _ _) hz
  have hz3 : 3 ≤ z := le_trans (le_max_right _ _) hz
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  have hlogz_sq_pos : 0 < (Real.log (z : ℝ))^2 := by positivity
  -- M2 upper at z (odd primes): Σ_{3 ≤ p ≤ z, prime} 1/p ≤ log log z + B''.
  have hM2_z :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B'' := hM2 z hz_M2
  -- Taylor sum-form bound.
  have hsum_taylor :
      -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - 12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2
        ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
            Real.log (1 - 2 / (p : ℝ)) := sum_log_pairedBrunFactor_ge z
  -- Σ 1/p² ≤ 1/2.
  have hinv_sq : (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
      ≤ (1 : ℝ) / 2 := sum_inv_sq_prime_le_half z
  -- Combine: Σ log(1-2/p) ≥ -2(log log z + B'') - 12*(1/2) = -2 log log z - 2B'' - 6.
  -- Need: -2 Σ 1/p ≥ -2(log log z + B''), so -2 Σ 1/p ≥ ...
  have hsum_inv_p_nn :
      (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    have hp_pos : (0 : ℝ) < (p : ℝ) := by
      have : (1 : ℝ) ≤ (p : ℝ) := by
        have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        linarith
      linarith
    positivity
  have hsum_inv_sq_nn :
      (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro p _
    positivity
  have hsum_log_lb :
      -2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6
        ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ)) := by
    -- From hM2_z: Σ 1/p ≤ log log z + B''
    --   so 2 · Σ 1/p ≤ 2 (log log z + B'')
    --   so -(2 · Σ 1/p) ≥ -(2 (log log z + B''))  i.e.  -2 Σ 1/p ≥ -2 log log z - 2 B''.
    -- From hinv_sq: Σ 1/p² ≤ 1/2, so -12 Σ 1/p² ≥ -6.
    -- Sum: -2 Σ 1/p - 12 Σ 1/p² ≥ -2 log log z - 2 B'' - 6.
    -- Combined with hsum_taylor: Σ log(1-2/p) ≥ above.
    have h1 : -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≥ -2 * (Real.log (Real.log (z : ℝ)) + B'') := by
      linarith [hM2_z]
    have h2 : -(12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
        ≥ -12 * (1 / 2) := by
      linarith [hinv_sq]
    linarith [h1, h2, hsum_taylor]
  -- log(pairedBrunFactor z) = Σ log(1 - 2/p).
  have hlog_eq :
      Real.log (pairedBrunFactor z)
        = ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ)) :=
    log_pairedBrunFactor_eq_sum z
  have hlog_lb :
      -2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6
        ≤ Real.log (pairedBrunFactor z) := by
    rw [hlog_eq]; exact hsum_log_lb
  -- Exponentiate.  pairedBrunFactor z > 0, so exp(log pairedBrunFactor z) = pairedBrunFactor z.
  have hmpos : 0 < pairedBrunFactor z := pairedBrunFactor_pos z
  -- exp is monotone.
  have hexp_lb :
      Real.exp (-2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6)
        ≤ pairedBrunFactor z := by
    have h_exp_mono : Real.exp (-2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6)
        ≤ Real.exp (Real.log (pairedBrunFactor z)) := Real.exp_le_exp.mpr hlog_lb
    rw [Real.exp_log hmpos] at h_exp_mono
    exact h_exp_mono
  -- Identify exp(-2 log log z - 2 B'' - 6) = exp(-2B'' - 6) / (log z)^2.
  have hexp_eq :
      Real.exp (-2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6)
        = Real.exp (-(2 * B'') - 6) / (Real.log (z : ℝ))^2 := by
    -- -2 log log z - 2 B'' - 6 = -(2 log log z) - (2 B'' + 6),
    -- so exp(...) = exp(-(2 B'' + 6)) / (log z)^2.
    have h_rewrite : -2 * Real.log (Real.log (z : ℝ)) - 2 * B'' - 6
        = -(2 * Real.log (Real.log (z : ℝ))) - (2 * B'' + 6) := by ring
    rw [h_rewrite]
    have := exp_neg_two_log_log_sub_eq z hz3 (2 * B'' + 6)
    -- this : exp(-(2 log log z) - (2 B'' + 6)) = exp(-(2 B'' + 6)) / (log z)^2
    rw [this]
    -- Goal: exp(-(2 B'' + 6)) / (log z)^2 = exp(-(2 B'') - 6) / (log z)^2.
    congr 1
    congr 1
    ring
  -- Final: exp(-2B'' - 6) / (log z)^2 ≤ pairedBrunFactor z.
  -- We need: exp(-(2 B'') - 6) / (log z)^2 ≤ pairedBrunFactor z.
  -- This is exactly the goal after the rewrite.
  rw [hexp_eq] at hexp_lb
  exact hexp_lb

/-! ## Section 7 — Documentation summary -/

/-- **P19-T9 summary, in proof form.**

Deliverables:

1. **Investigation finding**: the existing Abel-inversion chain
   (closed via `abelInversionMertensSecondFromFirst_holds` from the
   four sub-Props) is **implicitly two-sided** — every sub-Prop is an
   absolute-value bound, but only the *lower* direction is exposed in
   `MertensSecondLowerBoundFull`.

2. `MertensSecondUpperBound` — symmetric counterpart of
   `MertensSecondLowerBoundFull`, closed axiom-clean by the dual Abel
   argument (sign-flipped clone of
   `abelInversionMertensSecondFromFirst_of_components`).

3. `MertensSecondUpperBoundOdd` — restricted to odd primes, by
   dropping the `p = 2` term.

4. `log_one_sub_two_div_prime_ge` — Taylor lower bound
   `log(1 − 2/p) ≥ −2/p − 12/p²` for `p ≥ 3` prime.

5. `sum_inv_sq_prime_le_half` — `Σ_{p ≥ 3, prime} 1/p² ≤ 1/2`.

6. **`pairedBrunMertensThirdLowerGap_holds`** — closure of the named
   open Prop
   `Gdbh.PathCPairedBrunMertensLowerReal.PairedBrunMertensThirdLowerGap`,
   axiom-clean via the Mertens 2nd upper + Taylor lower + exponentiation
   chain.

Axiom audit: `[Classical.choice, Quot.sound, propext]`. -/
theorem pathC_p19_t9_summary : True := trivial

end PathCMertensSecondTwoSided
end Gdbh
