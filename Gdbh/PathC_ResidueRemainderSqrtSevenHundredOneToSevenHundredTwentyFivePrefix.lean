/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix
import Gdbh.PathC_ResidueCanonicalSqrtSevenHundredOneToSevenHundredTwentyFiveSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 701 to 725

Round 68 closed the `651 ≤ Nat.sqrt n ≤ 700` finite block and left the tail
beginning at `701 ≤ Nat.sqrt n`.  This file closes the next finite block
`701 ≤ Nat.sqrt n ≤ 725`.

The proof reuses the Round 64 cardinal envelope.  The residue prime set is a
subset of the 127 odd primes from `3` through `725`; the finite envelope is
absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix

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
open Gdbh.PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSevenHundredOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtSevenHundredOneToSevenHundredTwentyFiveSplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred_twenty_five
   prime_filter_three_to_seven_hundred_twenty_five)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `701 ≤ sqrt ≤ 725` block:
`(2^127)^2 * 2`. -/
noncomputable def sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 127

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient : ℝ :=
  101 * sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound

private lemma residuePrimeSet_subset_primes_to_seven_hundred_twenty_five {z : ℕ}
    (hz725 : z ≤ 725) :
    residuePrimeSet z ⊆ (Finset.Icc 3 725).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz725⟩, hp.2⟩

private lemma residuePrimeSet_card_le_one_hundred_twenty_seven_of_le_seven_hundred_twenty_five
    {z : ℕ} (hz725 : z ≤ 725) :
    (residuePrimeSet z).card ≤ 127 := by
  have hsubset := residuePrimeSet_subset_primes_to_seven_hundred_twenty_five hz725
  have hcard := Finset.card_le_card hsubset
  have hseven_hundred_twenty_five :
      ((Finset.Icc 3 725).filter Nat.Prime).card = 127 := by
    rw [prime_filter_three_to_seven_hundred_twenty_five]
    decide
  simpa [hseven_hundred_twenty_five] using hcard

/-- On the block `701 ≤ Nat.sqrt n ≤ 725`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^127)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_one_to_seven_hundred_twenty_five
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_seven_hundred_one : 701 ≤ Nat.sqrt n)
    (hsqrt_le_seven_hundred_twenty_five : Nat.sqrt n ≤ 725) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 127 :=
    residuePrimeSet_card_le_one_hundred_twenty_seven_of_le_seven_hundred_twenty_five
      hsqrt_le_seven_hundred_twenty_five
  simpa [sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 127) hcard

/-- Fixed-coefficient finite-block worker for the `701 ≤ Nat.sqrt n ≤ 725`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 701 ≤ Nat.sqrt n → Nat.sqrt n ≤ 725 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `701 ≤ sqrt ≤ 725` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveAtSqrt A

/-- Remaining large-range worker after removing the `701 ≤ sqrt ≤ 725`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 725 A

/-- The `701 ≤ Nat.sqrt n ≤ 725` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^127)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFive_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveAtSqrt
      sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient := by
  refine ⟨by unfold sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient
              sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_seven_hundred_one hsqrt_le_seven_hundred_twenty_five
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_one_to_seven_hundred_twenty_five
      hn hsqrt_ge_seven_hundred_one hsqrt_le_seven_hundred_twenty_five
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred_twenty_five
        n (Nat.sqrt n) hsqrt_le_seven_hundred_twenty_five
  have hbound_nonneg : 0 ≤ sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound := by
    unfold sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound ≤
        sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound * (n : ℝ) ≤
        sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtSevenHundredOneToSevenHundredTwentyFiveRemainderBound * (n : ℝ)
          ≤
            (sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `701 ≤ sqrt ≤ 725` block. -/
theorem residueRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveWithConstant :=
  ⟨sqrtSevenHundredOneToSevenHundredTwentyFiveRelativeCoefficient,
    residueRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFive_explicit⟩

/-- A closed `701 ≤ sqrt ≤ 725` block and a `sqrt ≥ 726` tail bound combine
into the Round 68 active `sqrt ≥ 701` target. -/
theorem residueRemainderAfterSqrtSevenHundredOneFixed_of_sqrtSevenHundredOneToSevenHundredTwentyFive_and_afterSqrtSevenHundredTwentySix
    {Ablock AsevenHundredTwentySix : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveAtSqrt
        Ablock)
    (hSevenHundredTwentySix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 725
        AsevenHundredTwentySix) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 700
      (max Ablock AsevenHundredTwentySix) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hSevenHundredTwentySix with ⟨_hAsevenHundredTwentySix,
    hSevenHundredTwentySixBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AsevenHundredTwentySix), ?_⟩
  intro n hn hsqrt_ge_seven_hundred_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_seven_hundred_twenty_five : Nat.sqrt n ≤ 725
  · have hbd :=
      hBlockBd n hn hsqrt_ge_seven_hundred_one
        hsqrt_le_seven_hundred_twenty_five
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsevenHundredTwentySix *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AsevenHundredTwentySix) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_seven_hundred_twenty_six : 725 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_seven_hundred_twenty_five)
    have hbd :=
      hSevenHundredTwentySixBd n hn hsqrt_ge_seven_hundred_twenty_six
    have hscale :
        AsevenHundredTwentySix *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsevenHundredTwentySix *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AsevenHundredTwentySix) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 68 active
`sqrt ≥ 701` target. -/
theorem residueRemainderAfterSqrtSevenHundredOne_of_sqrtSevenHundredOneToSevenHundredTwentyFive_and_afterSqrtSevenHundredTwentySix
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveWithConstant)
    (hSevenHundredTwentySix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hSevenHundredTwentySix with
    ⟨AsevenHundredTwentySix, hAsevenHundredTwentySix⟩
  exact ⟨max Ablock AsevenHundredTwentySix,
    residueRemainderAfterSqrtSevenHundredOneFixed_of_sqrtSevenHundredOneToSevenHundredTwentyFive_and_afterSqrtSevenHundredTwentySix
      hAblock hAsevenHundredTwentySix⟩

/-- Closing the `701 ≤ sqrt ≤ 725` block means only the `sqrt ≥ 726` tail
remains. -/
theorem residueRemainderAfterSqrtSevenHundredOne_of_afterSqrtSevenHundredTwentySix
    (hSevenHundredTwentySix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant :=
  residueRemainderAfterSqrtSevenHundredOne_of_sqrtSevenHundredOneToSevenHundredTwentyFive_and_afterSqrtSevenHundredTwentySix
    residueRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFiveWithConstant_closed
    hSevenHundredTwentySix

/-- Final Path C adapter after closing the `701 ≤ sqrt ≤ 725` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSevenHundredTwentySix_and_countingInput
    (hSevenHundredTwentySix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredTwentySixWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSevenHundredOne_and_countingInput
    (residueRemainderAfterSqrtSevenHundredOne_of_afterSqrtSevenHundredTwentySix
      hSevenHundredTwentySix)
    hCounting

end PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_seven_hundred_one_to_seven_hundred_twenty_five
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix.residueRemainderRelativeSqrtSevenHundredOneToSevenHundredTwentyFive_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenHundredOneToSevenHundredTwentyFivePrefix.pathC_kGoldbach_of_remainderAfterSqrtSevenHundredTwentySix_and_countingInput
