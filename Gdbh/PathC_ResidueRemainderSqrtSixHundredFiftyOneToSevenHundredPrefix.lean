/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix
import Gdbh.PathC_ResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 651 to 700

Round 67 closed the `601 ≤ Nat.sqrt n ≤ 650` finite block and left the tail
beginning at `651 ≤ Nat.sqrt n`.  This file closes the next finite block
`651 ≤ Nat.sqrt n ≤ 700`.

The proof reuses the Round 64 cardinal envelope.  The residue prime set is a
subset of the 124 odd primes from `3` through `700`; the finite envelope is
absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix

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
open Gdbh.PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSixHundredFiftyOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred
   prime_filter_three_to_seven_hundred)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `651 ≤ sqrt ≤ 700` block:
`(2^124)^2 * 2`. -/
noncomputable def sqrtSixHundredFiftyOneToSevenHundredRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 124

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient : ℝ :=
  101 * sqrtSixHundredFiftyOneToSevenHundredRemainderBound

private lemma residuePrimeSet_subset_primes_to_seven_hundred {z : ℕ}
    (hz700 : z ≤ 700) :
    residuePrimeSet z ⊆ (Finset.Icc 3 700).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz700⟩, hp.2⟩

private lemma residuePrimeSet_card_le_one_hundred_twenty_four_of_le_seven_hundred
    {z : ℕ} (hz700 : z ≤ 700) :
    (residuePrimeSet z).card ≤ 124 := by
  have hsubset := residuePrimeSet_subset_primes_to_seven_hundred hz700
  have hcard := Finset.card_le_card hsubset
  have hseven_hundred :
      ((Finset.Icc 3 700).filter Nat.Prime).card = 124 := by
    rw [prime_filter_three_to_seven_hundred]
    decide
  simpa [hseven_hundred] using hcard

/-- On the block `651 ≤ Nat.sqrt n ≤ 700`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^124)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_fifty_one_to_seven_hundred
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_six_hundred_fifty_one : 651 ≤ Nat.sqrt n)
    (hsqrt_le_seven_hundred : Nat.sqrt n ≤ 700) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtSixHundredFiftyOneToSevenHundredRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 124 :=
    residuePrimeSet_card_le_one_hundred_twenty_four_of_le_seven_hundred
      hsqrt_le_seven_hundred
  simpa [sqrtSixHundredFiftyOneToSevenHundredRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 124) hcard

/-- Fixed-coefficient finite-block worker for the `651 ≤ Nat.sqrt n ≤ 700`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 651 ≤ Nat.sqrt n → Nat.sqrt n ≤ 700 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `651 ≤ sqrt ≤ 700` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredAtSqrt A

/-- Remaining large-range worker after removing the `651 ≤ sqrt ≤ 700`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 700 A

/-- The `651 ≤ Nat.sqrt n ≤ 700` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^124)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtSixHundredFiftyOneToSevenHundred_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredAtSqrt
      sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient := by
  refine ⟨by unfold sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient
              sqrtSixHundredFiftyOneToSevenHundredRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_six_hundred_fifty_one hsqrt_le_seven_hundred
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_fifty_one_to_seven_hundred
      hn hsqrt_ge_six_hundred_fifty_one hsqrt_le_seven_hundred
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred
        n (Nat.sqrt n) hsqrt_le_seven_hundred
  have hbound_nonneg : 0 ≤ sqrtSixHundredFiftyOneToSevenHundredRemainderBound := by
    unfold sqrtSixHundredFiftyOneToSevenHundredRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtSixHundredFiftyOneToSevenHundredRemainderBound ≤
        sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtSixHundredFiftyOneToSevenHundredRemainderBound * (n : ℝ) ≤
        sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtSixHundredFiftyOneToSevenHundredRemainderBound * (n : ℝ)
          ≤
            (sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `651 ≤ sqrt ≤ 700` block. -/
theorem residueRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredWithConstant :=
  ⟨sqrtSixHundredFiftyOneToSevenHundredRelativeCoefficient,
    residueRemainderRelativeSqrtSixHundredFiftyOneToSevenHundred_explicit⟩

/-- A closed `651 ≤ sqrt ≤ 700` block and a `sqrt ≥ 701` tail bound combine
into the Round 67 active `sqrt ≥ 651` target. -/
theorem residueRemainderAfterSqrtSixHundredFiftyOneFixed_of_sqrtSixHundredFiftyOneToSevenHundred_and_afterSqrtSevenHundredOne
    {Ablock AsevenHundredOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredAtSqrt
        Ablock)
    (hSevenHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 700
        AsevenHundredOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 650
      (max Ablock AsevenHundredOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hSevenHundredOne with ⟨_hAsevenHundredOne,
    hSevenHundredOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AsevenHundredOne), ?_⟩
  intro n hn hsqrt_ge_six_hundred_fifty_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_seven_hundred : Nat.sqrt n ≤ 700
  · have hbd :=
      hBlockBd n hn hsqrt_ge_six_hundred_fifty_one hsqrt_le_seven_hundred
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsevenHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AsevenHundredOne) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_seven_hundred_one : 700 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_seven_hundred)
    have hbd := hSevenHundredOneBd n hn hsqrt_ge_seven_hundred_one
    have hscale :
        AsevenHundredOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsevenHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AsevenHundredOne) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 67 active
`sqrt ≥ 651` target. -/
theorem residueRemainderAfterSqrtSixHundredFiftyOne_of_sqrtSixHundredFiftyOneToSevenHundred_and_afterSqrtSevenHundredOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredWithConstant)
    (hSevenHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hSevenHundredOne with
    ⟨AsevenHundredOne, hAsevenHundredOne⟩
  exact ⟨max Ablock AsevenHundredOne,
    residueRemainderAfterSqrtSixHundredFiftyOneFixed_of_sqrtSixHundredFiftyOneToSevenHundred_and_afterSqrtSevenHundredOne
      hAblock hAsevenHundredOne⟩

/-- Closing the `651 ≤ sqrt ≤ 700` block means only the `sqrt ≥ 701` tail
remains. -/
theorem residueRemainderAfterSqrtSixHundredFiftyOne_of_afterSqrtSevenHundredOne
    (hSevenHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant :=
  residueRemainderAfterSqrtSixHundredFiftyOne_of_sqrtSixHundredFiftyOneToSevenHundred_and_afterSqrtSevenHundredOne
    residueRemainderRelativeSqrtSixHundredFiftyOneToSevenHundredWithConstant_closed
    hSevenHundredOne

/-- Final Path C adapter after closing the `651 ≤ sqrt ≤ 700` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSevenHundredOne_and_countingInput
    (hSevenHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenHundredOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSixHundredFiftyOne_and_countingInput
    (residueRemainderAfterSqrtSixHundredFiftyOne_of_afterSqrtSevenHundredOne
      hSevenHundredOne)
    hCounting

end PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_fifty_one_to_seven_hundred
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix.residueRemainderRelativeSqrtSixHundredFiftyOneToSevenHundred_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredFiftyOneToSevenHundredPrefix.pathC_kGoldbach_of_remainderAfterSqrtSevenHundredOne_and_countingInput
