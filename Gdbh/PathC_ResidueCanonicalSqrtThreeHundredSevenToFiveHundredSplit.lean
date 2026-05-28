/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtHundredOneToThreeHundredSixSplit

/-!
# Path C -- corrected residue canonical sqrt-three-hundred-seven-to-five-hundred split

Round 33 removed the block `101 ≤ Nat.sqrt n ≤ 306` from the corrected residue
canonical target.  This file removes the next block
`307 ≤ Nat.sqrt n ≤ 500`.  The larger candidate upper bound `1000` was rejected
for this round because its explicit-prime verification exceeded the default
heartbeat budget; the `500` block is still a strict, score-positive residual
shrink and verifies with the existing crude-product pattern.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit

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
open Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit
  (ResidueCanonicalFromSqrtThreeHundredSevenAtSqrt
   ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtThreeHundredSeven
   pathC_kGoldbach_of_residueCanonicalFromSqrtThreeHundredSeven_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtThreeHundredSeven)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`307 ≤ Nat.sqrt n ≤ 500`. -/
def ResidueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 307 ≤ Nat.sqrt n → Nat.sqrt n ≤ 500 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`307 ≤ sqrt n ≤ 500`. -/
def ResidueCanonicalFromSqrtFiveHundredOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 501 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 501` residual. -/
def ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtFiveHundredOneAtSqrt C₁

/-! ## Crude product lower bound through 500 -/

/-- Explicit odd-prime set through `500`. -/
theorem prime_filter_three_to_five_hundred :
    (Finset.Icc 3 500).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
        307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499} : Finset ℕ) := by
  decide

/-- The fixed crude product through `500` is still at least `1 / 101`. -/
theorem one_over_one_hundred_one_le_crudeResidueFactorProduct_to_five_hundred :
    (1 / 101 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 500).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_five_hundred]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 500`, the odd-prime residue main factor is at least
`1 / 101`. -/
theorem one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_five_hundred
    (n z : ℕ) (hz500 : z ≤ 500) :
    (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let P500 : Finset ℕ := (Finset.Icc 3 500).filter Nat.Prime
  have hsubset : Pz ⊆ P500 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz500⟩, hp'.2⟩
  have h3_500 : ∀ p ∈ P500, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ P500, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_500
  have hcrude_z :
      (1 / 101 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_over_one_hundred_one_le_crudeResidueFactorProduct_to_five_hundred.trans
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

/-- The whole block `307 ≤ Nat.sqrt n ≤ 500` of the corrected residual is
closed with coefficient `101`, by the trivial count bound and the `1 / 101`
local-factor lower bound. -/
theorem residueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt_one_hundred_one :
    ResidueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt 101 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_three_hundred_seven hsqrt_le_five_hundred
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_one_hundred_first :
      (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_five_hundred
      n (Nat.sqrt n) hsqrt_le_five_hundred
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

/-- A closed `307 ≤ sqrt n ≤ 500` block and a `sqrt n ≥ 501` residual combine
into the Round 33 residual `sqrt n ≥ 307`. -/
theorem residueCanonicalFromSqrtThreeHundredSevenAtSqrt_of_sqrtThreeHundredSevenToFiveHundred_and_fromSqrtFiveHundredOne
    {Cblock C501 : ℝ}
    (hBlock : ResidueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt Cblock)
    (hFiveHundredOne : ResidueCanonicalFromSqrtFiveHundredOneAtSqrt C501) :
    ResidueCanonicalFromSqrtThreeHundredSevenAtSqrt (max Cblock C501) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hFiveHundredOne with ⟨_hC501_pos, hFiveHundredOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C501), ?_⟩
  intro n hn hsqrt_ge_three_hundred_seven
  by_cases hsqrt_le_five_hundred : Nat.sqrt n ≤ 500
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C501)
      (hBlockBd n hn hsqrt_ge_three_hundred_seven hsqrt_le_five_hundred)
  · have hsqrt_ge_five_hundred_one : 501 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C501)
      (hFiveHundredOneBd n hn hsqrt_ge_five_hundred_one)

/-- The only remaining finite-sieve worker target after the closed
`307 ≤ sqrt n ≤ 500` block is the `sqrt n ≥ 501` residual. -/
theorem residueCanonicalFromSqrtThreeHundredSevenWithConstant_of_fromSqrtFiveHundredOne
    (hFiveHundredOne : ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant := by
  rcases hFiveHundredOne with ⟨C501, hFiveHundredOne⟩
  exact ⟨max 101 C501,
    residueCanonicalFromSqrtThreeHundredSevenAtSqrt_of_sqrtThreeHundredSevenToFiveHundred_and_fromSqrtFiveHundredOne
      residueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt_one_hundred_one
      hFiveHundredOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtFiveHundredOne
    (hFiveHundredOne : ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtThreeHundredSeven
    (residueCanonicalFromSqrtThreeHundredSevenWithConstant_of_fromSqrtFiveHundredOne
      hFiveHundredOne)

/-- `sqrt n ≥ 501` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtFiveHundredOne
    (hFiveHundredOne : ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtThreeHundredSeven
    (residueCanonicalFromSqrtThreeHundredSevenWithConstant_of_fromSqrtFiveHundredOne
      hFiveHundredOne)

/-- Final Path C adapter after the closed `307 ≤ sqrt n ≤ 500` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 501` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtFiveHundredOne_and_countingInput
    (hFiveHundredOne : ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtThreeHundredSeven_and_countingInput
    (residueCanonicalFromSqrtThreeHundredSevenWithConstant_of_fromSqrtFiveHundredOne
      hFiveHundredOne)
    hCounting

end PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_five_hundred
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.residueCanonicalSqrtThreeHundredSevenToFiveHundredAtSqrt_one_hundred_one
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.residueCanonicalFromSqrtThreeHundredSevenAtSqrt_of_sqrtThreeHundredSevenToFiveHundred_and_fromSqrtFiveHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.residueCanonicalFromSqrtThreeHundredSevenWithConstant_of_fromSqrtFiveHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.residueCanonicalWithConstant_of_fromSqrtFiveHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.finiteSieveInput_of_residueCanonicalFromSqrtFiveHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtFiveHundredOne_and_countingInput
