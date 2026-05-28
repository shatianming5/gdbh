/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix
import Gdbh.PathC_ResidueCanonicalSqrtFiveHundredOneToSixHundredSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 501 to 600

Round 65 closed the `307 ≤ Nat.sqrt n ≤ 500` finite block and left the tail
beginning at `501 ≤ Nat.sqrt n`.  This file closes the next finite block
`501 ≤ Nat.sqrt n ≤ 600`.

The proof reuses the Round 64 cardinal envelope.  The residue prime set is a
subset of the 108 odd primes from `3` through `600`; the finite envelope is
absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix

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
open Gdbh.PathCResidueRemainderSqrtThreeHundredSevenToFiveHundredPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtFiveHundredOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred
   prime_filter_three_to_six_hundred)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `501 ≤ sqrt ≤ 600` block:
`(2^108)^2 * 2`. -/
noncomputable def sqrtFiveHundredOneToSixHundredRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 108

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtFiveHundredOneToSixHundredRelativeCoefficient : ℝ :=
  101 * sqrtFiveHundredOneToSixHundredRemainderBound

private lemma residuePrimeSet_subset_primes_to_six_hundred {z : ℕ}
    (hz600 : z ≤ 600) :
    residuePrimeSet z ⊆ (Finset.Icc 3 600).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz600⟩, hp.2⟩

private lemma residuePrimeSet_card_le_one_hundred_eight_of_le_six_hundred
    {z : ℕ} (hz600 : z ≤ 600) :
    (residuePrimeSet z).card ≤ 108 := by
  have hsubset := residuePrimeSet_subset_primes_to_six_hundred hz600
  have hcard := Finset.card_le_card hsubset
  have hsix_hundred :
      ((Finset.Icc 3 600).filter Nat.Prime).card = 108 := by
    rw [prime_filter_three_to_six_hundred]
    decide
  simpa [hsix_hundred] using hcard

/-- On the block `501 ≤ Nat.sqrt n ≤ 600`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^108)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_five_hundred_one_to_six_hundred
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_five_hundred_one : 501 ≤ Nat.sqrt n)
    (hsqrt_le_six_hundred : Nat.sqrt n ≤ 600) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtFiveHundredOneToSixHundredRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 108 :=
    residuePrimeSet_card_le_one_hundred_eight_of_le_six_hundred
      hsqrt_le_six_hundred
  simpa [sqrtFiveHundredOneToSixHundredRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 108) hcard

/-- Fixed-coefficient finite-block worker for the `501 ≤ Nat.sqrt n ≤ 600`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 501 ≤ Nat.sqrt n → Nat.sqrt n ≤ 600 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `501 ≤ sqrt ≤ 600` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredAtSqrt A

/-- Remaining large-range worker after removing the `501 ≤ sqrt ≤ 600`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 600 A

/-- The `501 ≤ Nat.sqrt n ≤ 600` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^108)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtFiveHundredOneToSixHundred_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredAtSqrt
      sqrtFiveHundredOneToSixHundredRelativeCoefficient := by
  refine ⟨by unfold sqrtFiveHundredOneToSixHundredRelativeCoefficient
              sqrtFiveHundredOneToSixHundredRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_five_hundred_one hsqrt_le_six_hundred
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_five_hundred_one_to_six_hundred
      hn hsqrt_ge_five_hundred_one hsqrt_le_six_hundred
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred
        n (Nat.sqrt n) hsqrt_le_six_hundred
  have hbound_nonneg : 0 ≤ sqrtFiveHundredOneToSixHundredRemainderBound := by
    unfold sqrtFiveHundredOneToSixHundredRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtFiveHundredOneToSixHundredRemainderBound ≤
        sqrtFiveHundredOneToSixHundredRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtFiveHundredOneToSixHundredRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtFiveHundredOneToSixHundredRemainderBound * (n : ℝ) ≤
        sqrtFiveHundredOneToSixHundredRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtFiveHundredOneToSixHundredRemainderBound * (n : ℝ)
          ≤
            (sqrtFiveHundredOneToSixHundredRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtFiveHundredOneToSixHundredRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `501 ≤ sqrt ≤ 600` block. -/
theorem residueRemainderRelativeSqrtFiveHundredOneToSixHundredWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredWithConstant :=
  ⟨sqrtFiveHundredOneToSixHundredRelativeCoefficient,
    residueRemainderRelativeSqrtFiveHundredOneToSixHundred_explicit⟩

/-- A closed `501 ≤ sqrt ≤ 600` block and a `sqrt ≥ 601` tail bound combine
into the Round 65 active `sqrt ≥ 501` target. -/
theorem residueRemainderAfterSqrtFiveHundredOneFixed_of_sqrtFiveHundredOneToSixHundred_and_afterSqrtSixHundredOne
    {Ablock AsixHundredOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredAtSqrt
        Ablock)
    (hSixHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 600
        AsixHundredOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 500
      (max Ablock AsixHundredOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hSixHundredOne with ⟨_hAsixHundredOne, hSixHundredOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AsixHundredOne), ?_⟩
  intro n hn hsqrt_ge_five_hundred_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_six_hundred : Nat.sqrt n ≤ 600
  · have hbd := hBlockBd n hn hsqrt_ge_five_hundred_one hsqrt_le_six_hundred
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsixHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AsixHundredOne) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_six_hundred_one : 600 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_six_hundred)
    have hbd := hSixHundredOneBd n hn hsqrt_ge_six_hundred_one
    have hscale :
        AsixHundredOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsixHundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AsixHundredOne) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 65 active
`sqrt ≥ 501` target. -/
theorem residueRemainderAfterSqrtFiveHundredOne_of_sqrtFiveHundredOneToSixHundred_and_afterSqrtSixHundredOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtFiveHundredOneToSixHundredWithConstant)
    (hSixHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hSixHundredOne with ⟨AsixHundredOne, hAsixHundredOne⟩
  exact ⟨max Ablock AsixHundredOne,
    residueRemainderAfterSqrtFiveHundredOneFixed_of_sqrtFiveHundredOneToSixHundred_and_afterSqrtSixHundredOne
      hAblock hAsixHundredOne⟩

/-- Closing the `501 ≤ sqrt ≤ 600` block means only the `sqrt ≥ 601` tail
remains. -/
theorem residueRemainderAfterSqrtFiveHundredOne_of_afterSqrtSixHundredOne
    (hSixHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveHundredOneWithConstant :=
  residueRemainderAfterSqrtFiveHundredOne_of_sqrtFiveHundredOneToSixHundred_and_afterSqrtSixHundredOne
    residueRemainderRelativeSqrtFiveHundredOneToSixHundredWithConstant_closed
    hSixHundredOne

/-- Final Path C adapter after closing the `501 ≤ sqrt ≤ 600` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSixHundredOne_and_countingInput
    (hSixHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtFiveHundredOne_and_countingInput
    (residueRemainderAfterSqrtFiveHundredOne_of_afterSqrtSixHundredOne
      hSixHundredOne)
    hCounting

end PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_five_hundred_one_to_six_hundred
#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix.residueRemainderRelativeSqrtFiveHundredOneToSixHundred_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix.pathC_kGoldbach_of_remainderAfterSqrtSixHundredOne_and_countingInput
