/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtThirtySevenToHundredSplit

/-!
# Path C -- corrected residue canonical sqrt-hundred-one-to-three-hundred-six split

Round 32 removed the block `37 ≤ Nat.sqrt n ≤ 100` from the corrected residue
canonical target.  This file removes the next block
`101 ≤ Nat.sqrt n ≤ 306`, using the same crude-product monotonicity pattern:
the fixed product through `306` is still at least `1 / 101`, so the finite
block closes with coefficient `101` and leaves the strictly smaller residual
`307 ≤ Nat.sqrt n`.
-/

set_option maxRecDepth 20000

namespace Gdbh
namespace PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit

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
  (ResidueCanonicalFromSqrtHundredOneAtSqrt
   ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant
   crudeResidueFactor crudeResidueFactorProduct_antitone_of_subset
   finiteSieveInput_of_residueCanonicalFromSqrtHundredOne
   pathC_kGoldbach_of_residueCanonicalFromSqrtHundredOne_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtHundredOne)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`101 ≤ Nat.sqrt n ≤ 306`. -/
def ResidueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 101 ≤ Nat.sqrt n → Nat.sqrt n ≤ 306 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`101 ≤ sqrt n ≤ 306`. -/
def ResidueCanonicalFromSqrtThreeHundredSevenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 307 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 307` residual. -/
def ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtThreeHundredSevenAtSqrt C₁

/-! ## Crude product lower bound through 306 -/

/-- Explicit odd-prime set through `306`. -/
theorem prime_filter_three_to_three_hundred_six :
    (Finset.Icc 3 306).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
        293} : Finset ℕ) := by
  decide

/-- The fixed crude product through `306` is still at least `1 / 101`. -/
theorem one_over_one_hundred_one_le_crudeResidueFactorProduct_to_three_hundred_six :
    (1 / 101 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 306).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_three_hundred_six]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 306`, the odd-prime residue main factor is at least
`1 / 101`. -/
theorem one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_three_hundred_six
    (n z : ℕ) (hz306 : z ≤ 306) :
    (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let P306 : Finset ℕ := (Finset.Icc 3 306).filter Nat.Prime
  have hsubset : Pz ⊆ P306 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz306⟩, hp'.2⟩
  have h3_306 : ∀ p ∈ P306, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ P306, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_306
  have hcrude_z :
      (1 / 101 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_over_one_hundred_one_le_crudeResidueFactorProduct_to_three_hundred_six.trans
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

/-- The whole block `101 ≤ Nat.sqrt n ≤ 306` of the corrected residual is
closed with coefficient `101`, by the trivial count bound and the `1 / 101`
local-factor lower bound. -/
theorem residueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt_one_hundred_one :
    ResidueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt 101 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_hundred_one hsqrt_le_three_hundred_six
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_one_hundred_first :
      (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_three_hundred_six
      n (Nat.sqrt n) hsqrt_le_three_hundred_six
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

/-- A closed `101 ≤ sqrt n ≤ 306` block and a `sqrt n ≥ 307` residual combine
into the Round 32 residual `sqrt n ≥ 101`. -/
theorem residueCanonicalFromSqrtHundredOneAtSqrt_of_sqrtHundredOneToThreeHundredSix_and_fromSqrtThreeHundredSeven
    {Cblock C307 : ℝ}
    (hBlock : ResidueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt Cblock)
    (hThreeHundredSeven : ResidueCanonicalFromSqrtThreeHundredSevenAtSqrt C307) :
    ResidueCanonicalFromSqrtHundredOneAtSqrt (max Cblock C307) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hThreeHundredSeven with ⟨_hC307_pos, hThreeHundredSevenBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C307), ?_⟩
  intro n hn hsqrt_ge_hundred_one
  by_cases hsqrt_le_three_hundred_six : Nat.sqrt n ≤ 306
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C307)
      (hBlockBd n hn hsqrt_ge_hundred_one hsqrt_le_three_hundred_six)
  · have hsqrt_ge_three_hundred_seven : 307 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C307)
      (hThreeHundredSevenBd n hn hsqrt_ge_three_hundred_seven)

/-- The only remaining finite-sieve worker target after the closed
`101 ≤ sqrt n ≤ 306` block is the `sqrt n ≥ 307` residual. -/
theorem residueCanonicalFromSqrtHundredOneWithConstant_of_fromSqrtThreeHundredSeven
    (hThreeHundredSeven : ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant := by
  rcases hThreeHundredSeven with ⟨C307, hThreeHundredSeven⟩
  exact ⟨max 101 C307,
    residueCanonicalFromSqrtHundredOneAtSqrt_of_sqrtHundredOneToThreeHundredSix_and_fromSqrtThreeHundredSeven
      residueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt_one_hundred_one
      hThreeHundredSeven⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtThreeHundredSeven
    (hThreeHundredSeven : ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtHundredOne
    (residueCanonicalFromSqrtHundredOneWithConstant_of_fromSqrtThreeHundredSeven
      hThreeHundredSeven)

/-- `sqrt n ≥ 307` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtThreeHundredSeven
    (hThreeHundredSeven : ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtHundredOne
    (residueCanonicalFromSqrtHundredOneWithConstant_of_fromSqrtThreeHundredSeven
      hThreeHundredSeven)

/-- Final Path C adapter after the closed `101 ≤ sqrt n ≤ 306` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 307` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtThreeHundredSeven_and_countingInput
    (hThreeHundredSeven : ResidueCanonicalFromSqrtThreeHundredSevenAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtHundredOne_and_countingInput
    (residueCanonicalFromSqrtHundredOneWithConstant_of_fromSqrtThreeHundredSeven
      hThreeHundredSeven)
    hCounting

end PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_three_hundred_six
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.residueCanonicalSqrtHundredOneToThreeHundredSixAtSqrt_one_hundred_one
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.residueCanonicalFromSqrtHundredOneAtSqrt_of_sqrtHundredOneToThreeHundredSix_and_fromSqrtThreeHundredSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.residueCanonicalFromSqrtHundredOneWithConstant_of_fromSqrtThreeHundredSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.residueCanonicalWithConstant_of_fromSqrtThreeHundredSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.finiteSieveInput_of_residueCanonicalFromSqrtThreeHundredSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtHundredOneToThreeHundredSixSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtThreeHundredSeven_and_countingInput
