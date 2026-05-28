/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix
import Gdbh.PathC_ResidueCanonicalParametricCoarseSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder parametric coarse split

Round 70 reduced the relative-remainder route to the large residual
`10001 ≤ Nat.sqrt n`.  This file mirrors the canonical parametric coarse split:
for any finite upper bound `N`, the finite block
`10001 ≤ Nat.sqrt n ≤ N` is closed with a finite coarse coefficient, reducing
the active worker to the later residual `N + 1 ≤ Nat.sqrt n`.

The constants are intentionally crude but honest.  The proof uses the reusable
cardinality envelope with `(residuePrimeSet z).card ≤ z ≤ N` and the canonical
coarse lower bound `(1 / 3)^N` for the local density.
-/

namespace Gdbh
namespace PathCResidueRemainderParametricCoarseSplit

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtTenThousandOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalParametricCoarseSplit
  (one_third_pow_N_le_goldbachResidueMainFactor_of_le)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the block `10001 ≤ sqrt ≤ N`:
`(2^N)^2 * 2`. -/
noncomputable def sqrtTenThousandOneToAtMostRemainderBound (N : ℕ) : ℝ :=
  residueRemainderCardinalityEnvelope N

/-- Relative coefficient after absorbing the finite remainder by the
`(1 / 3)^N` local-density lower bound. -/
noncomputable def sqrtTenThousandOneToAtMostRelativeCoefficient (N : ℕ) : ℝ :=
  ((3 : ℝ) ^ N) * sqrtTenThousandOneToAtMostRemainderBound N

private lemma residuePrimeSet_card_le_of_le {z N : ℕ} (hzN : z ≤ N) :
    (residuePrimeSet z).card ≤ N := by
  unfold residuePrimeSet
  have hfilter :
      ((Finset.Icc 3 z).filter Nat.Prime).card ≤ (Finset.Icc 3 z).card := by
    exact Finset.card_filter_le (Finset.Icc 3 z) Nat.Prime
  have hIcc : (Finset.Icc 3 z).card ≤ z := by
    rw [Nat.card_Icc]
    omega
  exact hfilter.trans (hIcc.trans hzN)

/-- On a parametric finite block `10001 ≤ Nat.sqrt n ≤ N`, the full signed
CRT remainder is bounded by the coarse finite cardinal envelope
`(2^N)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_ten_thousand_one_to_at_most
    (N : ℕ) {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_ten_thousand_one : 10001 ≤ Nat.sqrt n)
    (hsqrt_le_N : Nat.sqrt n ≤ N) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtTenThousandOneToAtMostRemainderBound N * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ N :=
    residuePrimeSet_card_le_of_le hsqrt_le_N
  simpa [sqrtTenThousandOneToAtMostRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := N) hcard

/-- Fixed-coefficient finite-block worker for
`10001 ≤ Nat.sqrt n ≤ N`. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtTenThousandOneToAtMostAtSqrt
    (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 10001 ≤ Nat.sqrt n → Nat.sqrt n ≤ N →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the parametric finite-block worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtTenThousandOneToAtMostWithConstant
    (N : ℕ) : Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtTenThousandOneToAtMostAtSqrt N A

/-- Residual after a chosen finite upper bound `N`, namely
`N + 1 ≤ Nat.sqrt n`. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeFromSqrtAfterAtSqrtWithConstant
    (N : ℕ) : Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold N A

/-- Every finite block `10001 ≤ Nat.sqrt n ≤ N` is closed with the explicit
coarse coefficient `3^N * ((2^N)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtTenThousandOneToAtMost_explicit
    (N : ℕ) :
    ResidueDoubleDivisorRemainderRelativeSqrtTenThousandOneToAtMostAtSqrt N
      (sqrtTenThousandOneToAtMostRelativeCoefficient N) := by
  refine ⟨by unfold sqrtTenThousandOneToAtMostRelativeCoefficient
              sqrtTenThousandOneToAtMostRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_ten_thousand_one hsqrt_le_N
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_ten_thousand_one_to_at_most
      N hn hsqrt_ge_ten_thousand_one hsqrt_le_N
  have hlocal_pow :
      (1 / 3 : ℝ) ^ N ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_third_pow_N_le_goldbachResidueMainFactor_of_le
        N n (Nat.sqrt n) hsqrt_le_N
  have hfactor_scaled :
      (1 : ℝ) ≤
        (3 : ℝ) ^ N * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ N := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlocal_pow hnonneg
    calc
      (1 : ℝ) = (3 : ℝ) ^ N * (1 / 3 : ℝ) ^ N := by
        rw [← mul_pow]
        norm_num
      _ ≤ (3 : ℝ) ^ N * residueDoubleDivisorLocalDensitySumAtSqrt n := hmul
  have hbound_nonneg : 0 ≤ sqrtTenThousandOneToAtMostRemainderBound N := by
    unfold sqrtTenThousandOneToAtMostRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtTenThousandOneToAtMostRemainderBound N ≤
        sqrtTenThousandOneToAtMostRelativeCoefficient N *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    have hmul :=
      mul_le_mul_of_nonneg_left hfactor_scaled hbound_nonneg
    calc
      sqrtTenThousandOneToAtMostRemainderBound N
          = sqrtTenThousandOneToAtMostRemainderBound N * (1 : ℝ) := by
              ring
      _ ≤
          sqrtTenThousandOneToAtMostRemainderBound N *
            ((3 : ℝ) ^ N * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
            hmul
      _ =
          sqrtTenThousandOneToAtMostRelativeCoefficient N *
            residueDoubleDivisorLocalDensitySumAtSqrt n := by
        unfold sqrtTenThousandOneToAtMostRelativeCoefficient
        ac_rfl
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtTenThousandOneToAtMostRemainderBound N * (n : ℝ) ≤
        sqrtTenThousandOneToAtMostRelativeCoefficient N *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtTenThousandOneToAtMostRemainderBound N * (n : ℝ)
          ≤
            (sqrtTenThousandOneToAtMostRelativeCoefficient N *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtTenThousandOneToAtMostRelativeCoefficient N *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed parametric finite block. -/
theorem residueRemainderRelativeSqrtTenThousandOneToAtMostWithConstant_closed
    (N : ℕ) :
    ResidueDoubleDivisorRemainderRelativeSqrtTenThousandOneToAtMostWithConstant
      N :=
  ⟨sqrtTenThousandOneToAtMostRelativeCoefficient N,
    residueRemainderRelativeSqrtTenThousandOneToAtMost_explicit N⟩

/-- A closed parametric finite block through `N` and a residual after `N`
combine into the active `sqrt ≥ 10001` target. -/
theorem residueRemainderAfterSqrtTenThousandOneFixed_of_parametric_after
    {N : ℕ} {Aafter : ℝ}
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold N Aafter) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 10000
      (max (sqrtTenThousandOneToAtMostRelativeCoefficient N) Aafter) := by
  have hBlock := residueRemainderRelativeSqrtTenThousandOneToAtMost_explicit N
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hAfter with ⟨_hAafter, hAfterBd⟩
  refine ⟨hAblock.trans
      (le_max_left (sqrtTenThousandOneToAtMostRelativeCoefficient N) Aafter),
    ?_⟩
  intro n hn hsqrt_ge_ten_thousand_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_N : Nat.sqrt n ≤ N
  · have hbd := hBlockBd n hn hsqrt_ge_ten_thousand_one hsqrt_le_N
    have hscale :
        sqrtTenThousandOneToAtMostRelativeCoefficient N *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max (sqrtTenThousandOneToAtMostRelativeCoefficient N) Aafter *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left (sqrtTenThousandOneToAtMostRelativeCoefficient N)
          Aafter) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_after : N + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr (lt_of_not_ge hsqrt_le_N)
    have hbd := hAfterBd n hn hsqrt_ge_after
    have hscale :
        Aafter * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max (sqrtTenThousandOneToAtMostRelativeCoefficient N) Aafter *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right (sqrtTenThousandOneToAtMostRelativeCoefficient N)
          Aafter) hmain_nonneg
    exact hbd.trans hscale

/-- For any finite upper bound `N`, the active `sqrt ≥ 10001` residual is
reduced to the later residual `sqrt ≥ N + 1`. -/
theorem residueRemainderAfterSqrtTenThousandOne_of_parametric_after
    (N : ℕ)
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeFromSqrtAfterAtSqrtWithConstant
        N) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant := by
  rcases hAfter with ⟨Aafter, hAfter⟩
  exact ⟨max (sqrtTenThousandOneToAtMostRelativeCoefficient N) Aafter,
    residueRemainderAfterSqrtTenThousandOneFixed_of_parametric_after
      hAfter⟩

/-- Final Path C adapter after the parameterized coarse remainder split. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtAfter_and_countingInput
    (N : ℕ)
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeFromSqrtAfterAtSqrtWithConstant
        N)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtTenThousandOne_and_countingInput
    (residueRemainderAfterSqrtTenThousandOne_of_parametric_after
      N hAfter)
    hCounting

end PathCResidueRemainderParametricCoarseSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderParametricCoarseSplit.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_ten_thousand_one_to_at_most
#print axioms
  Gdbh.PathCResidueRemainderParametricCoarseSplit.residueRemainderRelativeSqrtTenThousandOneToAtMost_explicit
#print axioms
  Gdbh.PathCResidueRemainderParametricCoarseSplit.residueRemainderAfterSqrtTenThousandOne_of_parametric_after
#print axioms
  Gdbh.PathCResidueRemainderParametricCoarseSplit.pathC_kGoldbach_of_remainderAfterSqrtAfter_and_countingInput
