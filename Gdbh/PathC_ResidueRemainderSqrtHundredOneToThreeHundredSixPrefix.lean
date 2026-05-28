/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtThirtySevenToHundredPrefix
import Gdbh.PathC_ResidueRemainderCardinalityEnvelope
import Gdbh.PathC_ResidueCanonicalSqrtHundredOneToThreeHundredSixSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt hundred-one to 306

Round 63 closed the `37 ≤ Nat.sqrt n ≤ 100` finite block and left the tail
beginning at `101 ≤ Nat.sqrt n`.  This file closes the next finite block
`101 ≤ Nat.sqrt n ≤ 306`.

The proof supplies the cardinal input required by
`PathC_ResidueRemainderCardinalityEnvelope`: the residue prime set is a subset
of the 61 odd primes from `3` through `306`.  The resulting envelope is then
absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix

set_option maxRecDepth 20000

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderSqrtThirtySevenToHundredPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtHundredOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_three_hundred_six
   prime_filter_three_to_three_hundred_six)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `101 ≤ sqrt ≤ 306` block:
`(2^61)^2 * 2`. -/
noncomputable def sqrtHundredOneToThreeHundredSixRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 61

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtHundredOneToThreeHundredSixRelativeCoefficient : ℝ :=
  101 * sqrtHundredOneToThreeHundredSixRemainderBound

private lemma residuePrimeSet_subset_primes_to_three_hundred_six {z : ℕ}
    (hz306 : z ≤ 306) :
    residuePrimeSet z ⊆ (Finset.Icc 3 306).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz306⟩, hp.2⟩

private lemma residuePrimeSet_card_le_sixty_one_of_le_three_hundred_six
    {z : ℕ} (hz306 : z ≤ 306) :
    (residuePrimeSet z).card ≤ 61 := by
  have hsubset := residuePrimeSet_subset_primes_to_three_hundred_six hz306
  have hcard := Finset.card_le_card hsubset
  have hthree_hundred_six :
      ((Finset.Icc 3 306).filter Nat.Prime).card = 61 := by
    rw [prime_filter_three_to_three_hundred_six]
    decide
  simpa [hthree_hundred_six] using hcard

/-- On the block `101 ≤ Nat.sqrt n ≤ 306`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^61)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_hundred_one_to_three_hundred_six
    {n : ℕ} (_hn : 16 ≤ n) (_hsqrt_ge_hundred_one : 101 ≤ Nat.sqrt n)
    (hsqrt_le_three_hundred_six : Nat.sqrt n ≤ 306) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtHundredOneToThreeHundredSixRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 61 :=
    residuePrimeSet_card_le_sixty_one_of_le_three_hundred_six
      hsqrt_le_three_hundred_six
  simpa [sqrtHundredOneToThreeHundredSixRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 61) hcard

/-- Fixed-coefficient finite-block worker for the
`101 ≤ Nat.sqrt n ≤ 306` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 101 ≤ Nat.sqrt n → Nat.sqrt n ≤ 306 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `101 ≤ sqrt ≤ 306` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixAtSqrt A

/-- Remaining large-range worker after removing the
`101 ≤ sqrt ≤ 306` block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 306 A

/-- The `101 ≤ Nat.sqrt n ≤ 306` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^61)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtHundredOneToThreeHundredSix_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixAtSqrt
      sqrtHundredOneToThreeHundredSixRelativeCoefficient := by
  refine ⟨by unfold sqrtHundredOneToThreeHundredSixRelativeCoefficient
              sqrtHundredOneToThreeHundredSixRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_hundred_one hsqrt_le_three_hundred_six
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_hundred_one_to_three_hundred_six
      hn hsqrt_ge_hundred_one hsqrt_le_three_hundred_six
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_three_hundred_six
        n (Nat.sqrt n) hsqrt_le_three_hundred_six
  have hbound_nonneg : 0 ≤ sqrtHundredOneToThreeHundredSixRemainderBound := by
    unfold sqrtHundredOneToThreeHundredSixRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtHundredOneToThreeHundredSixRemainderBound ≤
        sqrtHundredOneToThreeHundredSixRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtHundredOneToThreeHundredSixRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtHundredOneToThreeHundredSixRemainderBound * (n : ℝ) ≤
        sqrtHundredOneToThreeHundredSixRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtHundredOneToThreeHundredSixRemainderBound * (n : ℝ)
          ≤
            (sqrtHundredOneToThreeHundredSixRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtHundredOneToThreeHundredSixRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `101 ≤ sqrt ≤ 306` block. -/
theorem residueRemainderRelativeSqrtHundredOneToThreeHundredSixWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixWithConstant :=
  ⟨sqrtHundredOneToThreeHundredSixRelativeCoefficient,
    residueRemainderRelativeSqrtHundredOneToThreeHundredSix_explicit⟩

/-- A closed `101 ≤ sqrt ≤ 306` block and a `sqrt ≥ 307` tail bound combine
into the Round 63 active `sqrt ≥ 101` target. -/
theorem residueRemainderAfterSqrtHundredOneFixed_of_sqrtHundredOneToThreeHundredSix_and_afterSqrtThreeHundredSeven
    {Ablock AthreeHundredSeven : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixAtSqrt
        Ablock)
    (hThreeHundredSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 306
        AthreeHundredSeven) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 100
      (max Ablock AthreeHundredSeven) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hThreeHundredSeven with ⟨_hAthreeHundredSeven,
    hThreeHundredSevenBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AthreeHundredSeven), ?_⟩
  intro n hn hsqrt_ge_hundred_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_three_hundred_six : Nat.sqrt n ≤ 306
  · have hbd :=
      hBlockBd n hn hsqrt_ge_hundred_one hsqrt_le_three_hundred_six
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AthreeHundredSeven *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AthreeHundredSeven) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_three_hundred_seven : 306 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_three_hundred_six)
    have hbd := hThreeHundredSevenBd n hn hsqrt_ge_three_hundred_seven
    have hscale :
        AthreeHundredSeven *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AthreeHundredSeven *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AthreeHundredSeven) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 63 active
`sqrt ≥ 101` target. -/
theorem residueRemainderAfterSqrtHundredOne_of_sqrtHundredOneToThreeHundredSix_and_afterSqrtThreeHundredSeven
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtHundredOneToThreeHundredSixWithConstant)
    (hThreeHundredSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hThreeHundredSeven with
    ⟨AthreeHundredSeven, hAthreeHundredSeven⟩
  exact ⟨max Ablock AthreeHundredSeven,
    residueRemainderAfterSqrtHundredOneFixed_of_sqrtHundredOneToThreeHundredSix_and_afterSqrtThreeHundredSeven
      hAblock hAthreeHundredSeven⟩

/-- Closing the `101 ≤ sqrt ≤ 306` block means only the `sqrt ≥ 307` tail
remains. -/
theorem residueRemainderAfterSqrtHundredOne_of_afterSqrtThreeHundredSeven
    (hThreeHundredSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant :=
  residueRemainderAfterSqrtHundredOne_of_sqrtHundredOneToThreeHundredSix_and_afterSqrtThreeHundredSeven
    residueRemainderRelativeSqrtHundredOneToThreeHundredSixWithConstant_closed
    hThreeHundredSeven

/-- Final Path C adapter after closing the `101 ≤ sqrt ≤ 306` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtThreeHundredSeven_and_countingInput
    (hThreeHundredSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreeHundredSevenWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtHundredOne_and_countingInput
    (residueRemainderAfterSqrtHundredOne_of_afterSqrtThreeHundredSeven
      hThreeHundredSeven)
    hCounting

end PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_hundred_one_to_three_hundred_six
#print axioms
  Gdbh.PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix.residueRemainderRelativeSqrtHundredOneToThreeHundredSix_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtHundredOneToThreeHundredSixPrefix.pathC_kGoldbach_of_remainderAfterSqrtThreeHundredSeven_and_countingInput
