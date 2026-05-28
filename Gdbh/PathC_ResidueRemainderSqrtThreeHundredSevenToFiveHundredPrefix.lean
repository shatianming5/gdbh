/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtHundredOneToThreeHundredSixPrefix
import Gdbh.PathC_ResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 307 to 500

Round 64 closed the `101 ≤ Nat.sqrt n ≤ 306` finite block and left the tail
beginning at `307 ≤ Nat.sqrt n`.  This file closes the next finite block
`307 ≤ Nat.sqrt n ≤ 500`.

The proof reuses the cardinal envelope from Round 64.  The residue prime set
is a subset of the 94 odd primes from `3` through `500`; the finite envelope is
then absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix

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
open Gdbh.PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtThreeHundredSeven_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_five_hundred
   prime_filter_three_to_five_hundred)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `307 ≤ sqrt ≤ 500` block:
`(2^94)^2 * 2`. -/
noncomputable def sqrtThreeHundredSevenToFiveHundredRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 94

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtThreeHundredSevenToFiveHundredRelativeCoefficient : ℝ :=
  101 * sqrtThreeHundredSevenToFiveHundredRemainderBound

private lemma residuePrimeSet_subset_primes_to_five_hundred {z : ℕ}
    (hz500 : z ≤ 500) :
    residuePrimeSet z ⊆ (Finset.Icc 3 500).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz500⟩, hp.2⟩

private lemma residuePrimeSet_card_le_ninety_four_of_le_five_hundred
    {z : ℕ} (hz500 : z ≤ 500) :
    (residuePrimeSet z).card ≤ 94 := by
  have hsubset := residuePrimeSet_subset_primes_to_five_hundred hz500
  have hcard := Finset.card_le_card hsubset
  have hfive_hundred :
      ((Finset.Icc 3 500).filter Nat.Prime).card = 94 := by
    rw [prime_filter_three_to_five_hundred]
    decide
  simpa [hfive_hundred] using hcard

/-- On the block `307 ≤ Nat.sqrt n ≤ 500`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^94)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_three_hundred_seven_to_five_hundred
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_three_hundred_seven : 307 ≤ Nat.sqrt n)
    (hsqrt_le_five_hundred : Nat.sqrt n ≤ 500) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtThreeHundredSevenToFiveHundredRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 94 :=
    residuePrimeSet_card_le_ninety_four_of_le_five_hundred
      hsqrt_le_five_hundred
  simpa [sqrtThreeHundredSevenToFiveHundredRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 94) hcard

/-- Fixed-coefficient finite-block worker for the
`307 ≤ Nat.sqrt n ≤ 500` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 307 ≤ Nat.sqrt n → Nat.sqrt n ≤ 500 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `307 ≤ sqrt ≤ 500` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredAtSqrt A

/-- Remaining large-range worker after removing the `307 ≤ sqrt ≤ 500`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 500 A

/-- The `307 ≤ Nat.sqrt n ≤ 500` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^94)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtThreeHundredSevenToFiveHundred_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredAtSqrt
      sqrtThreeHundredSevenToFiveHundredRelativeCoefficient := by
  refine ⟨by unfold sqrtThreeHundredSevenToFiveHundredRelativeCoefficient
              sqrtThreeHundredSevenToFiveHundredRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_three_hundred_seven hsqrt_le_five_hundred
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_three_hundred_seven_to_five_hundred
      hn hsqrt_ge_three_hundred_seven hsqrt_le_five_hundred
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_five_hundred
        n (Nat.sqrt n) hsqrt_le_five_hundred
  have hbound_nonneg : 0 ≤ sqrtThreeHundredSevenToFiveHundredRemainderBound := by
    unfold sqrtThreeHundredSevenToFiveHundredRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtThreeHundredSevenToFiveHundredRemainderBound ≤
        sqrtThreeHundredSevenToFiveHundredRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtThreeHundredSevenToFiveHundredRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtThreeHundredSevenToFiveHundredRemainderBound * (n : ℝ) ≤
        sqrtThreeHundredSevenToFiveHundredRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtThreeHundredSevenToFiveHundredRemainderBound * (n : ℝ)
          ≤
            (sqrtThreeHundredSevenToFiveHundredRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtThreeHundredSevenToFiveHundredRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `307 ≤ sqrt ≤ 500` block. -/
theorem residueRemainderRelativeSqrtThreeHundredSevenToFiveHundredWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredWithConstant :=
  ⟨sqrtThreeHundredSevenToFiveHundredRelativeCoefficient,
    residueRemainderRelativeSqrtThreeHundredSevenToFiveHundred_explicit⟩

/-- A closed `307 ≤ sqrt ≤ 500` block and a `sqrt ≥ 501` tail bound combine
into the Round 64 active `sqrt ≥ 307` target. -/
theorem residueRemainderAfterSqrtThreeHundredSevenFixed_of_sqrtThreeHundredSevenToFiveHundred_and_afterSqrtFiveHundredOne
    {Ablock AfiveHundredOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredAtSqrt
        Ablock)
    (hFiveHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 500
        AfiveHundredOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 306
      (max Ablock AfiveHundredOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hFiveHundredOne with ⟨_hAfiveHundredOne,
    hFiveHundredOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AfiveHundredOne), ?_⟩
  intro n hn hsqrt_ge_three_hundred_seven
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_five_hundred : Nat.sqrt n ≤ 500
  · have hbd :=
      hBlockBd n hn hsqrt_ge_three_hundred_seven hsqrt_le_five_hundred
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AfiveHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AfiveHundredOne) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_five_hundred_one : 500 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_five_hundred)
    have hbd := hFiveHundredOneBd n hn hsqrt_ge_five_hundred_one
    have hscale :
        AfiveHundredOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AfiveHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AfiveHundredOne) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 64 active
`sqrt ≥ 307` target. -/
theorem residueRemainderAfterSqrtThreeHundredSeven_of_sqrtThreeHundredSevenToFiveHundred_and_afterSqrtFiveHundredOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtThreeHundredSevenToFiveHundredWithConstant)
    (hFiveHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hFiveHundredOne with ⟨AfiveHundredOne, hAfiveHundredOne⟩
  exact ⟨max Ablock AfiveHundredOne,
    residueRemainderAfterSqrtThreeHundredSevenFixed_of_sqrtThreeHundredSevenToFiveHundred_and_afterSqrtFiveHundredOne
      hAblock hAfiveHundredOne⟩

/-- Closing the `307 ≤ sqrt ≤ 500` block means only the `sqrt ≥ 501` tail
remains. -/
theorem residueRemainderAfterSqrtThreeHundredSeven_of_afterSqrtFiveHundredOne
    (hFiveHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant :=
  residueRemainderAfterSqrtThreeHundredSeven_of_sqrtThreeHundredSevenToFiveHundred_and_afterSqrtFiveHundredOne
    residueRemainderRelativeSqrtThreeHundredSevenToFiveHundredWithConstant_closed
    hFiveHundredOne

/-- Final Path C adapter after closing the `307 ≤ sqrt ≤ 500` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtFiveHundredOne_and_countingInput
    (hFiveHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtThreeHundredSeven_and_countingInput
    (residueRemainderAfterSqrtThreeHundredSeven_of_afterSqrtFiveHundredOne
      hFiveHundredOne)
    hCounting

end PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_three_hundred_seven_to_five_hundred
#print axioms
  Gdbh.PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix.residueRemainderRelativeSqrtThreeHundredSevenToFiveHundred_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix.pathC_kGoldbach_of_remainderAfterSqrtFiveHundredOne_and_countingInput
