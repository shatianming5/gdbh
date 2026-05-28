/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit

/-!
# Path C -- corrected residue canonical sqrt-six-hundred-fifty-one-to-seven-hundred split

Round 36 removed the block `601 ≤ Nat.sqrt n ≤ 650` from the corrected residue
canonical target.  This file removes the next block
`651 ≤ Nat.sqrt n ≤ 700`, keeping the coefficient `101` and advancing the
large-range worker residual to `701 ≤ Nat.sqrt n`.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
  (residueFactorProduct_lower_two_of_three_le)
open Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit
  (crudeResidueFactor crudeResidueFactorProduct_antitone_of_subset)
open Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit
  (ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrt
   ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSixHundredFiftyOne
   pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredFiftyOne_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSixHundredFiftyOne)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`651 ≤ Nat.sqrt n ≤ 700`. -/
def ResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 651 ≤ Nat.sqrt n → Nat.sqrt n ≤ 700 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`651 ≤ sqrt n ≤ 700`. -/
def ResidueCanonicalFromSqrtSevenHundredOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 701 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 701` residual. -/
def ResidueCanonicalFromSqrtSevenHundredOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSevenHundredOneAtSqrt C₁

/-! ## Crude product lower bound through 700 -/

/-- Explicit odd-prime set through `700`. -/
theorem prime_filter_three_to_seven_hundred :
    (Finset.Icc 3 700).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
        307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569,
        571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647,
        653, 659, 661, 673, 677, 683, 691} : Finset ℕ) := by
  decide

/-- The fixed crude product through `700` is still at least `1 / 101`. -/
theorem one_over_one_hundred_one_le_crudeResidueFactorProduct_to_seven_hundred :
    (1 / 101 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 700).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_seven_hundred]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 700`, the odd-prime residue main factor is at least
`1 / 101`. -/
theorem one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred
    (n z : ℕ) (hz700 : z ≤ 700) :
    (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let P700 : Finset ℕ := (Finset.Icc 3 700).filter Nat.Prime
  have hsubset : Pz ⊆ P700 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz700⟩, hp'.2⟩
  have h3_700 : ∀ p ∈ P700, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ P700, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_700
  have hcrude_z :
      (1 / 101 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_over_one_hundred_one_le_crudeResidueFactorProduct_to_seven_hundred.trans
      hanti
  have hactual :
      (∏ p ∈ Pz, crudeResidueFactor p) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
    simpa [crudeResidueFactor] using
      residueFactorProduct_lower_two_of_three_le n Pz h3_z
  have hmain :
      (1 / 101 : ℝ) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
    hcrude_z.trans hactual
  simpa [goldbachResidueMainFactor, Pz] using hmain

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `651 ≤ Nat.sqrt n ≤ 700` of the corrected residual is
closed with coefficient `101`, by the trivial count bound and the `1 / 101`
local-factor lower bound. -/
theorem residueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt_one_hundred_one :
    ResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt 101 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_six_hundred_fifty_one hsqrt_le_seven_hundred
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_one_hundred_first :
      (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred
      n (Nat.sqrt n) hsqrt_le_seven_hundred
  have hfactor_scaled :
      (1 : ℝ) ≤ 101 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (101 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (101 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (101 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `651 ≤ sqrt n ≤ 700` block and a `sqrt n ≥ 701` residual combine
into the Round 36 residual `sqrt n ≥ 651`. -/
theorem residueCanonicalFromSqrtSixHundredFiftyOneAtSqrt_of_sqrtSixHundredFiftyOneToSevenHundred_and_fromSqrtSevenHundredOne
    {Cblock C701 : ℝ}
    (hBlock : ResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt Cblock)
    (hSevenHundredOne : ResidueCanonicalFromSqrtSevenHundredOneAtSqrt C701) :
    ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrt (max Cblock C701) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hSevenHundredOne with ⟨_hC701_pos, hSevenHundredOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C701), ?_⟩
  intro n hn hsqrt_ge_six_hundred_fifty_one
  by_cases hsqrt_le_seven_hundred : Nat.sqrt n ≤ 700
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C701)
      (hBlockBd n hn hsqrt_ge_six_hundred_fifty_one hsqrt_le_seven_hundred)
  · have hsqrt_ge_seven_hundred_one : 701 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C701)
      (hSevenHundredOneBd n hn hsqrt_ge_seven_hundred_one)

/-- The only remaining finite-sieve worker target after the closed
`651 ≤ sqrt n ≤ 700` block is the `sqrt n ≥ 701` residual. -/
theorem residueCanonicalFromSqrtSixHundredFiftyOneWithConstant_of_fromSqrtSevenHundredOne
    (hSevenHundredOne : ResidueCanonicalFromSqrtSevenHundredOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant := by
  rcases hSevenHundredOne with ⟨C701, hSevenHundredOne⟩
  exact ⟨max 101 C701,
    residueCanonicalFromSqrtSixHundredFiftyOneAtSqrt_of_sqrtSixHundredFiftyOneToSevenHundred_and_fromSqrtSevenHundredOne
      residueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt_one_hundred_one
      hSevenHundredOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSevenHundredOne
    (hSevenHundredOne : ResidueCanonicalFromSqrtSevenHundredOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSixHundredFiftyOne
    (residueCanonicalFromSqrtSixHundredFiftyOneWithConstant_of_fromSqrtSevenHundredOne
      hSevenHundredOne)

/-- `sqrt n ≥ 701` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSevenHundredOne
    (hSevenHundredOne : ResidueCanonicalFromSqrtSevenHundredOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSixHundredFiftyOne
    (residueCanonicalFromSqrtSixHundredFiftyOneWithConstant_of_fromSqrtSevenHundredOne
      hSevenHundredOne)

/-- Final Path C adapter after the closed `651 ≤ sqrt n ≤ 700` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 701` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSevenHundredOne_and_countingInput
    (hSevenHundredOne : ResidueCanonicalFromSqrtSevenHundredOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredFiftyOne_and_countingInput
    (residueCanonicalFromSqrtSixHundredFiftyOneWithConstant_of_fromSqrtSevenHundredOne
      hSevenHundredOne)
    hCounting

end PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_seven_hundred
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.residueCanonicalSqrtSixHundredFiftyOneToSevenHundredAtSqrt_one_hundred_one
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.residueCanonicalFromSqrtSixHundredFiftyOneAtSqrt_of_sqrtSixHundredFiftyOneToSevenHundred_and_fromSqrtSevenHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.residueCanonicalFromSqrtSixHundredFiftyOneWithConstant_of_fromSqrtSevenHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.residueCanonicalWithConstant_of_fromSqrtSevenHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.finiteSieveInput_of_residueCanonicalFromSqrtSevenHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredFiftyOneToSevenHundredSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSevenHundredOne_and_countingInput
