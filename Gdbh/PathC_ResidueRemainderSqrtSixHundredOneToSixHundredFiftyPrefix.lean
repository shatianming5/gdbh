/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtFiveHundredOneToSixHundredPrefix
import Gdbh.PathC_ResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt 601 to 650

Round 66 closed the `501 ≤ Nat.sqrt n ≤ 600` finite block and left the tail
beginning at `601 ≤ Nat.sqrt n`.  This file closes the next finite block
`601 ≤ Nat.sqrt n ≤ 650`.

The proof reuses the Round 64 cardinal envelope.  The residue prime set is a
subset of the 117 odd primes from `3` through `650`; the finite envelope is
absorbed using the canonical `1 / 101` local-density lower bound for this
block.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix

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
open Gdbh.PathCResidueRemainderSqrtFiveHundredOneToSixHundredPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSixHundredOne_and_countingInput)
open Gdbh.PathCResidueRemainderCardinalityEnvelope
  (residueRemainderCardinalityEnvelope
   residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope)
open Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit
  (one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred_fifty
   prime_filter_three_to_six_hundred_fifty)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `601 ≤ sqrt ≤ 650` block:
`(2^117)^2 * 2`. -/
noncomputable def sqrtSixHundredOneToSixHundredFiftyRemainderBound : ℝ :=
  residueRemainderCardinalityEnvelope 117

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 101` local-density lower bound. -/
noncomputable def sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient : ℝ :=
  101 * sqrtSixHundredOneToSixHundredFiftyRemainderBound

private lemma residuePrimeSet_subset_primes_to_six_hundred_fifty {z : ℕ}
    (hz650 : z ≤ 650) :
    residuePrimeSet z ⊆ (Finset.Icc 3 650).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz650⟩, hp.2⟩

private lemma residuePrimeSet_card_le_one_hundred_seventeen_of_le_six_hundred_fifty
    {z : ℕ} (hz650 : z ≤ 650) :
    (residuePrimeSet z).card ≤ 117 := by
  have hsubset := residuePrimeSet_subset_primes_to_six_hundred_fifty hz650
  have hcard := Finset.card_le_card hsubset
  have hsix_hundred_fifty :
      ((Finset.Icc 3 650).filter Nat.Prime).card = 117 := by
    rw [prime_filter_three_to_six_hundred_fifty]
    decide
  simpa [hsix_hundred_fifty] using hcard

/-- On the block `601 ≤ Nat.sqrt n ≤ 650`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^117)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_one_to_six_hundred_fifty
    {n : ℕ} (_hn : 16 ≤ n)
    (_hsqrt_ge_six_hundred_one : 601 ≤ Nat.sqrt n)
    (hsqrt_le_six_hundred_fifty : Nat.sqrt n ≤ 650) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtSixHundredOneToSixHundredFiftyRemainderBound * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ 117 :=
    residuePrimeSet_card_le_one_hundred_seventeen_of_le_six_hundred_fifty
      hsqrt_le_six_hundred_fifty
  simpa [sqrtSixHundredOneToSixHundredFiftyRemainderBound] using
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
      (n := n) (M := 117) hcard

/-- Fixed-coefficient finite-block worker for the `601 ≤ Nat.sqrt n ≤ 650`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 601 ≤ Nat.sqrt n → Nat.sqrt n ≤ 650 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `601 ≤ sqrt ≤ 650` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyAtSqrt A

/-- Remaining large-range worker after removing the `601 ≤ sqrt ≤ 650`
block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 650 A

/-- The `601 ≤ Nat.sqrt n ≤ 650` relative remainder worker is closed with the
explicit symbolic coefficient `101 * ((2^117)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtSixHundredOneToSixHundredFifty_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyAtSqrt
      sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient := by
  refine ⟨by unfold sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient
              sqrtSixHundredOneToSixHundredFiftyRemainderBound
              residueRemainderCardinalityEnvelope; positivity, ?_⟩
  intro n hn hsqrt_ge_six_hundred_one hsqrt_le_six_hundred_fifty
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_one_to_six_hundred_fifty
      hn hsqrt_ge_six_hundred_one hsqrt_le_six_hundred_fifty
  have hlocal_one_hundred_first :
      (1 / 101 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred_fifty
        n (Nat.sqrt n) hsqrt_le_six_hundred_fifty
  have hbound_nonneg : 0 ≤ sqrtSixHundredOneToSixHundredFiftyRemainderBound := by
    unfold sqrtSixHundredOneToSixHundredFiftyRemainderBound
      residueRemainderCardinalityEnvelope
    positivity
  have hscale :
      sqrtSixHundredOneToSixHundredFiftyRemainderBound ≤
        sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtSixHundredOneToSixHundredFiftyRemainderBound * (n : ℝ) ≤
        sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtSixHundredOneToSixHundredFiftyRemainderBound * (n : ℝ)
          ≤
            (sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `601 ≤ sqrt ≤ 650` block. -/
theorem residueRemainderRelativeSqrtSixHundredOneToSixHundredFiftyWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyWithConstant :=
  ⟨sqrtSixHundredOneToSixHundredFiftyRelativeCoefficient,
    residueRemainderRelativeSqrtSixHundredOneToSixHundredFifty_explicit⟩

/-- A closed `601 ≤ sqrt ≤ 650` block and a `sqrt ≥ 651` tail bound combine
into the Round 66 active `sqrt ≥ 601` target. -/
theorem residueRemainderAfterSqrtSixHundredOneFixed_of_sqrtSixHundredOneToSixHundredFifty_and_afterSqrtSixHundredFiftyOne
    {Ablock AsixHundredFiftyOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyAtSqrt
        Ablock)
    (hSixHundredFiftyOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 650
        AsixHundredFiftyOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 600
      (max Ablock AsixHundredFiftyOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hSixHundredFiftyOne with ⟨_hAsixHundredFiftyOne,
    hSixHundredFiftyOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AsixHundredFiftyOne), ?_⟩
  intro n hn hsqrt_ge_six_hundred_one
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_six_hundred_fifty : Nat.sqrt n ≤ 650
  · have hbd :=
      hBlockBd n hn hsqrt_ge_six_hundred_one hsqrt_le_six_hundred_fifty
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsixHundredFiftyOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_left Ablock AsixHundredFiftyOne) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_six_hundred_fifty_one : 650 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr
        (lt_of_not_ge hsqrt_le_six_hundred_fifty)
    have hbd := hSixHundredFiftyOneBd n hn hsqrt_ge_six_hundred_fifty_one
    have hscale :
        AsixHundredFiftyOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AsixHundredFiftyOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right
        (le_max_right Ablock AsixHundredFiftyOne) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 66 active
`sqrt ≥ 601` target. -/
theorem residueRemainderAfterSqrtSixHundredOne_of_sqrtSixHundredOneToSixHundredFifty_and_afterSqrtSixHundredFiftyOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSixHundredOneToSixHundredFiftyWithConstant)
    (hSixHundredFiftyOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hSixHundredFiftyOne with
    ⟨AsixHundredFiftyOne, hAsixHundredFiftyOne⟩
  exact ⟨max Ablock AsixHundredFiftyOne,
    residueRemainderAfterSqrtSixHundredOneFixed_of_sqrtSixHundredOneToSixHundredFifty_and_afterSqrtSixHundredFiftyOne
      hAblock hAsixHundredFiftyOne⟩

/-- Closing the `601 ≤ sqrt ≤ 650` block means only the `sqrt ≥ 651` tail
remains. -/
theorem residueRemainderAfterSqrtSixHundredOne_of_afterSqrtSixHundredFiftyOne
    (hSixHundredFiftyOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredOneWithConstant :=
  residueRemainderAfterSqrtSixHundredOne_of_sqrtSixHundredOneToSixHundredFifty_and_afterSqrtSixHundredFiftyOne
    residueRemainderRelativeSqrtSixHundredOneToSixHundredFiftyWithConstant_closed
    hSixHundredFiftyOne

/-- Final Path C adapter after closing the `601 ≤ sqrt ≤ 650` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSixHundredFiftyOne_and_countingInput
    (hSixHundredFiftyOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixHundredFiftyOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSixHundredOne_and_countingInput
    (residueRemainderAfterSqrtSixHundredOne_of_afterSqrtSixHundredFiftyOne
      hSixHundredFiftyOne)
    hCounting

end PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_six_hundred_one_to_six_hundred_fifty
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix.residueRemainderRelativeSqrtSixHundredOneToSixHundredFifty_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixHundredOneToSixHundredFiftyPrefix.pathC_kGoldbach_of_remainderAfterSqrtSixHundredFiftyOne_and_countingInput
