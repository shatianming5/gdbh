/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix
import Gdbh.PathC_ResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 726 to 10000

Round 69 closed the `701 ≤ Nat.sqrt n ≤ 725` finite block and left the tail
beginning at `726 ≤ Nat.sqrt n`.  This file closes the larger coarse block
`726 ≤ Nat.sqrt n ≤ 10000`.

The proof deliberately avoids a 1228-prime explicit table.  Instead, it uses
the reusable cardinal envelope with the honest coarse bound
`(residuePrimeSet z).card ≤ z ≤ 10000`, and absorbs the finite envelope using
the canonical `(1 / 3)^10000` local-density lower bound for this block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix

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
open Gdbh.PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSevenHundredTwentySix_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit
  (one_third_pow_ten_thousand_le_goldbachResidueMainFactor_of_le_ten_thousand)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `726 ≤ sqrt ≤ 10000` block:
`(2^10000)^2 * 2`.  This is deliberately coarser than the actual prime count,
but avoids an explicit 1228-prime table. -/
noncomputable def sqrtSevenHundredTwentySixToTenThousandRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 10000

/-- Relative coefficient after absorbing the finite remainder by the
`(1 / 3)^10000` local-density lower bound. -/
noncomputable def sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient : ℝ :=
  ((3 : ℝ) ^ 10000) *
    sqrtSevenHundredTwentySixToTenThousandRemainderBound

private lemma residuePrimeSet_card_le_ten_thousand_of_le_ten_thousand {z : ℕ}
    (hz10000 : z ≤ 10000) :
    (residuePrimeSet z).card ≤ 10000 := by
  unfold residuePrimeSet
  have hfilter :
      ((Finset.Icc 3 z).filter Nat.Prime).card ≤ (Finset.Icc 3 z).card := by
    exact Finset.card_filter_le (Finset.Icc 3 z) Nat.Prime
  have hIcc : (Finset.Icc 3 z).card ≤ z := by
    rw [Nat.card_Icc]
    omega
  exact hfilter.trans (hIcc.trans hz10000)

/-- On the block `726 ≤ Nat.sqrt n ≤ 10000`, the full signed CRT remainder is
bounded by the coarse finite cardinal envelope `(2^10000)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_twenty_six_to_ten_thousand
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_seven_hundred_twenty_six : 726 ≤ Nat.sqrt n)
    (hsqrt_le_ten_thousand : Nat.sqrt n ≤ 10000) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtSevenHundredTwentySixToTenThousandRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 10000 :=
    residuePrimeSet_card_le_ten_thousand_of_le_ten_thousand
      hsqrt_le_ten_thousand
  simpa [sqrtSevenHundredTwentySixToTenThousandRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 10000) hcard

/-- Fixed-coefficient finite-block worker for the
`726 ≤ Nat.sqrt n ≤ 10000` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 726 ≤ Nat.sqrt n → Nat.sqrt n ≤ 10000 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `726 ≤ sqrt ≤ 10000` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandAtSqrt A

/-- Remaining large-range worker after removing the `726 ≤ sqrt ≤ 10000`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 10000 A

/-- The `726 ≤ Nat.sqrt n ≤ 10000` relative remainder worker is closed with
the explicit coarse coefficient `3^10000 * ((2^10000)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtSevenHundredTwentySixToTenThousand_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandAtSqrt
      sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient := by
  refine ⟨by unfold sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient
              sqrtSevenHundredTwentySixToTenThousandRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_seven_hundred_twenty_six hsqrt_le_ten_thousand
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_twenty_six_to_ten_thousand
      hn hsqrt_ge_seven_hundred_twenty_six hsqrt_le_ten_thousand
  have hlocal_pow :
      (1 / 3 : ℝ) ^ 10000 ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_third_pow_ten_thousand_le_goldbachResidueMainFactor_of_le_ten_thousand
        n (Nat.sqrt n) hsqrt_le_ten_thousand
  have hfactor_scaled :
      (1 : ℝ) ≤
        (3 : ℝ) ^ 10000 * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ 10000 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlocal_pow hnonneg
    calc
      (1 : ℝ) = (3 : ℝ) ^ 10000 * (1 / 3 : ℝ) ^ 10000 := by
        rw [← mul_pow]
        norm_num
      _ ≤
          (3 : ℝ) ^ 10000 * residueDoubleDivisorLocalDensitySumAtSqrt n :=
            hmul
  have hbound_nonneg :
      0 ≤ sqrtSevenHundredTwentySixToTenThousandRemainderBound := by
    unfold sqrtSevenHundredTwentySixToTenThousandRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtSevenHundredTwentySixToTenThousandRemainderBound ≤
        sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    have hmul :=
      mul_le_mul_of_nonneg_left hfactor_scaled hbound_nonneg
    calc
      sqrtSevenHundredTwentySixToTenThousandRemainderBound
          =
            sqrtSevenHundredTwentySixToTenThousandRemainderBound * (1 : ℝ) := by
              ring
      _ ≤
          sqrtSevenHundredTwentySixToTenThousandRemainderBound *
            ((3 : ℝ) ^ 10000 * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
            hmul
      _ =
          sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient *
            residueDoubleDivisorLocalDensitySumAtSqrt n := by
        unfold sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient
        ac_rfl
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtSevenHundredTwentySixToTenThousandRemainderBound * (n : ℝ) ≤
        sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtSevenHundredTwentySixToTenThousandRemainderBound * (n : ℝ)
          ≤
            (sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `726 ≤ sqrt ≤ 10000` block. -/
theorem residueRemainderRelativeSqrtSevenHundredTwentySixToTenThousandWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandWithConstant :=
  ⟨sqrtSevenHundredTwentySixToTenThousandRelativeCoefficient,
    residueRemainderRelativeSqrtSevenHundredTwentySixToTenThousand_explicit⟩

/-- A closed `726 ≤ sqrt ≤ 10000` block and a `sqrt ≥ 10001` tail bound
combine into the Round 69 active `sqrt ≥ 726` target. -/
theorem residueRemainderAfterSqrtSevenHundredTwentySixFixed_of_sqrtSevenHundredTwentySixToTenThousand_and_afterSqrtTenThousandOne
    {Ablock AtenThousandOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandAtSqrt
        Ablock)
    (hTenThousandOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 10000
        AtenThousandOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 725
      (max Ablock AtenThousandOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hTenThousandOne with ⟨_hAtenThousandOne, hTenThousandOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AtenThousandOne), ?_⟩
  intro n hn hsqrt_ge_seven_hundred_twenty_six
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_ten_thousand : Nat.sqrt n ≤ 10000
  · have hbd :=
      hBlockBd n hn hsqrt_ge_seven_hundred_twenty_six hsqrt_le_ten_thousand
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AtenThousandOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AtenThousandOne) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_ten_thousand_one : 10000 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_ten_thousand)
    have hbd := hTenThousandOneBd n hn hsqrt_ge_ten_thousand_one
    have hscale :
        AtenThousandOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AtenThousandOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AtenThousandOne) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 69 active
`sqrt ≥ 726` target. -/
theorem residueRemainderAfterSqrtSevenHundredTwentySix_of_sqrtSevenHundredTwentySixToTenThousand_and_afterSqrtTenThousandOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredTwentySixToTenThousandWithConstant)
    (hTenThousandOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hTenThousandOne with ⟨AtenThousandOne, hAtenThousandOne⟩
  exact ⟨max Ablock AtenThousandOne,
    residueRemainderAfterSqrtSevenHundredTwentySixFixed_of_sqrtSevenHundredTwentySixToTenThousand_and_afterSqrtTenThousandOne
      hAblock hAtenThousandOne⟩

/-- Closing the `726 ≤ sqrt ≤ 10000` block means only the `sqrt ≥ 10001` tail
remains. -/
theorem residueRemainderAfterSqrtSevenHundredTwentySix_of_afterSqrtTenThousandOne
    (hTenThousandOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant :=
  residueRemainderAfterSqrtSevenHundredTwentySix_of_sqrtSevenHundredTwentySixToTenThousand_and_afterSqrtTenThousandOne
    residueRemainderRelativeSqrtSevenHundredTwentySixToTenThousandWithConstant_closed
    hTenThousandOne

/-- Final Path C adapter after closing the `726 ≤ sqrt ≤ 10000` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtTenThousandOne_and_countingInput
    (hTenThousandOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSevenHundredTwentySix_and_countingInput
    (residueRemainderAfterSqrtSevenHundredTwentySix_of_afterSqrtTenThousandOne
      hTenThousandOne)
    hCounting

end PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_twenty_six_to_ten_thousand
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix.residueRemainderRelativeSqrtSevenHundredTwentySixToTenThousand_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix.pathC_kGoldbach_of_remainderAfterSqrtTenThousandOne_and_countingInput
