/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit

/-!
# Path C -- corrected residue canonical sqrt-five-hundred-one-to-six-hundred split

Round 34 removed the block `307 ≤ Nat.sqrt n ≤ 500` from the corrected residue
canonical target.  This file removes the next block
`501 ≤ Nat.sqrt n ≤ 600`.  The larger candidate upper bound `700` was rejected
for this round because its explicit-prime verification ran too long; the
`600` block is a stable score-positive shrink and keeps the same coefficient
`101`.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit

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
open Gdbh.PathCResidueCanonicalSqrtThreeHundredSevenToFiveHundredSplit
  (ResidueCanonicalFromSqrtFiveHundredOneAtSqrt
   ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtFiveHundredOne
   pathC_kGoldbach_of_residueCanonicalFromSqrtFiveHundredOne_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtFiveHundredOne)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`501 ≤ Nat.sqrt n ≤ 600`. -/
def ResidueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 501 ≤ Nat.sqrt n → Nat.sqrt n ≤ 600 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`501 ≤ sqrt n ≤ 600`. -/
def ResidueCanonicalFromSqrtSixHundredOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 601 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 601` residual. -/
def ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSixHundredOneAtSqrt C₁

/-! ## Crude product lower bound through 600 -/

/-- Explicit odd-prime set through `600`. -/
theorem prime_filter_three_to_six_hundred :
    (Finset.Icc 3 600).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
        307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569,
        571, 577, 587, 593, 599} : Finset ℕ) := by
  decide

/-- The fixed crude product through `600` is still at least `1 / 101`. -/
theorem one_over_one_hundred_one_le_crudeResidueFactorProduct_to_six_hundred :
    (1 / 101 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 600).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_six_hundred]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 600`, the odd-prime residue main factor is at least
`1 / 101`. -/
theorem one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred
    (n z : ℕ) (hz600 : z ≤ 600) :
    (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let P600 : Finset ℕ := (Finset.Icc 3 600).filter Nat.Prime
  have hsubset : Pz ⊆ P600 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz600⟩, hp'.2⟩
  have h3_600 : ∀ p ∈ P600, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ P600, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_600
  have hcrude_z :
      (1 / 101 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_over_one_hundred_one_le_crudeResidueFactorProduct_to_six_hundred.trans
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

/-- The whole block `501 ≤ Nat.sqrt n ≤ 600` of the corrected residual is
closed with coefficient `101`, by the trivial count bound and the `1 / 101`
local-factor lower bound. -/
theorem residueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt_one_hundred_one :
    ResidueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt 101 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_five_hundred_one hsqrt_le_six_hundred
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_one_hundred_first :
      (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred
      n (Nat.sqrt n) hsqrt_le_six_hundred
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

/-- A closed `501 ≤ sqrt n ≤ 600` block and a `sqrt n ≥ 601` residual combine
into the Round 34 residual `sqrt n ≥ 501`. -/
theorem residueCanonicalFromSqrtFiveHundredOneAtSqrt_of_sqrtFiveHundredOneToSixHundred_and_fromSqrtSixHundredOne
    {Cblock C601 : ℝ}
    (hBlock : ResidueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt Cblock)
    (hSixHundredOne : ResidueCanonicalFromSqrtSixHundredOneAtSqrt C601) :
    ResidueCanonicalFromSqrtFiveHundredOneAtSqrt (max Cblock C601) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hSixHundredOne with ⟨_hC601_pos, hSixHundredOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C601), ?_⟩
  intro n hn hsqrt_ge_five_hundred_one
  by_cases hsqrt_le_six_hundred : Nat.sqrt n ≤ 600
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C601)
      (hBlockBd n hn hsqrt_ge_five_hundred_one hsqrt_le_six_hundred)
  · have hsqrt_ge_six_hundred_one : 601 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C601)
      (hSixHundredOneBd n hn hsqrt_ge_six_hundred_one)

/-- The only remaining finite-sieve worker target after the closed
`501 ≤ sqrt n ≤ 600` block is the `sqrt n ≥ 601` residual. -/
theorem residueCanonicalFromSqrtFiveHundredOneWithConstant_of_fromSqrtSixHundredOne
    (hSixHundredOne : ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtFiveHundredOneAtSqrtWithConstant := by
  rcases hSixHundredOne with ⟨C601, hSixHundredOne⟩
  exact ⟨max 101 C601,
    residueCanonicalFromSqrtFiveHundredOneAtSqrt_of_sqrtFiveHundredOneToSixHundred_and_fromSqrtSixHundredOne
      residueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt_one_hundred_one
      hSixHundredOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSixHundredOne
    (hSixHundredOne : ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtFiveHundredOne
    (residueCanonicalFromSqrtFiveHundredOneWithConstant_of_fromSqrtSixHundredOne
      hSixHundredOne)

/-- `sqrt n ≥ 601` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSixHundredOne
    (hSixHundredOne : ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtFiveHundredOne
    (residueCanonicalFromSqrtFiveHundredOneWithConstant_of_fromSqrtSixHundredOne
      hSixHundredOne)

/-- Final Path C adapter after the closed `501 ≤ sqrt n ≤ 600` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 601` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredOne_and_countingInput
    (hSixHundredOne : ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtFiveHundredOne_and_countingInput
    (residueCanonicalFromSqrtFiveHundredOneWithConstant_of_fromSqrtSixHundredOne
      hSixHundredOne)
    hCounting

end PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.residueCanonicalSqrtFiveHundredOneToSixHundredAtSqrt_one_hundred_one
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.residueCanonicalFromSqrtFiveHundredOneAtSqrt_of_sqrtFiveHundredOneToSixHundred_and_fromSqrtSixHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.residueCanonicalFromSqrtFiveHundredOneWithConstant_of_fromSqrtSixHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.residueCanonicalWithConstant_of_fromSqrtSixHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.finiteSieveInput_of_residueCanonicalFromSqrtSixHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredOne_and_countingInput
