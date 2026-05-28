/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSplit

/-!
# Path C -- corrected residue canonical sqrt-five split

Round 26 removed the `Nat.sqrt n = 4` prefix from the corrected residue
canonical target.  This file removes the next finite prefix, `Nat.sqrt n = 5`,
and leaves the strictly smaller residual `6 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtFiveSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   ResidueCanonicalFromSqrtFiveAtSqrt
   ResidueCanonicalFromSqrtFiveAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtFive
   pathC_kGoldbach_of_residueCanonicalFromSqrtFive_and_countingInput
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite prefix of the corrected residual: `Nat.sqrt n = 5`. -/
def ResidueCanonicalSqrtFiveAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 5 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the `sqrt n = 5`
prefix. -/
def ResidueCanonicalFromSqrtSixAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 6 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 6` residual. -/
def ResidueCanonicalFromSqrtSixAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSixAtSqrt C₁

/-! ## Elementary closed prefix -/

/-- At `z = 5`, the odd-prime residue main factor is always at least `1 / 5`.
The odd-prime range is `{3, 5}`, and each bad-residue cardinal is at most two. -/
theorem one_fifth_le_goldbachResidueMainFactor_at_five (n : ℕ) :
    (1 / 5 : ℝ) ≤ goldbachResidueMainFactor n 5 := by
  classical
  have hfilter :
      (Finset.Icc 3 5).filter Nat.Prime = ({3, 5} : Finset ℕ) := by
    decide
  rw [goldbachResidueMainFactor, hfilter]
  rw [show ({3, 5} : Finset ℕ) = insert 3 ({5} : Finset ℕ) from rfl]
  rw [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have hcard_three_nat : (goldbachBadResidueSet n 3).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 3
  have hcard_five_nat : (goldbachBadResidueSet n 5).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 5
  have hcard_three : ((goldbachBadResidueSet n 3).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_three_nat
  have hcard_five : ((goldbachBadResidueSet n 5).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_five_nat
  have hthree :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hthree_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hmul := mul_le_mul hthree hfive (by norm_num : (0 : ℝ) ≤ 3 / 5)
    hthree_nonneg
  norm_num at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The whole `Nat.sqrt n = 5` prefix of the corrected residual is closed with
coefficient `5`, by the trivial count bound and the `1 / 5` local-factor lower
bound. -/
theorem residueCanonicalSqrtFiveAtSqrt_five :
    ResidueCanonicalSqrtFiveAtSqrt 5 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_fifth :
      (1 / 5 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) := by
    simpa [hsqrt] using one_fifth_le_goldbachResidueMainFactor_at_five n
  have hfactor_scaled :
      (1 : ℝ) ≤ 5 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (5 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (5 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (5 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-! ## Bridge from the new large residual back to the Round 26 residual -/

/-- A closed `sqrt n = 5` prefix and a `sqrt n ≥ 6` residual combine into the
Round 26 residual `sqrt n ≥ 5`. -/
theorem residueCanonicalFromSqrtFiveAtSqrt_of_sqrtFive_and_fromSqrtSix
    {C₅ C₆ : ℝ}
    (hFivePrefix : ResidueCanonicalSqrtFiveAtSqrt C₅)
    (hSix : ResidueCanonicalFromSqrtSixAtSqrt C₆) :
    ResidueCanonicalFromSqrtFiveAtSqrt (max C₅ C₆) := by
  rcases hFivePrefix with ⟨hC₅_pos, hFiveBd⟩
  rcases hSix with ⟨_hC₆_pos, hSixBd⟩
  refine ⟨lt_of_lt_of_le hC₅_pos (le_max_left C₅ C₆), ?_⟩
  intro n hn hsqrt_ge_five
  by_cases hsqrt : Nat.sqrt n = 5
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left C₅ C₆) (hFiveBd n hn hsqrt)
  · have hsqrt_ge_six : 6 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right C₅ C₆) (hSixBd n hn hsqrt_ge_six)

/-- The only remaining finite-sieve worker target after the closed `sqrt n = 5`
prefix is the `sqrt n ≥ 6` residual. -/
theorem residueCanonicalFromSqrtFiveWithConstant_of_fromSqrtSix
    (hSix : ResidueCanonicalFromSqrtSixAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtFiveAtSqrtWithConstant := by
  rcases hSix with ⟨C₆, hSix⟩
  exact ⟨max 5 C₆,
    residueCanonicalFromSqrtFiveAtSqrt_of_sqrtFive_and_fromSqrtSix
      residueCanonicalSqrtFiveAtSqrt_five hSix⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSix
    (hSix : ResidueCanonicalFromSqrtSixAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  Gdbh.PathCResidueCanonicalSqrtSplit.residueCanonicalWithConstant_of_fromSqrtFive
    (residueCanonicalFromSqrtFiveWithConstant_of_fromSqrtSix hSix)

/-- `sqrt n ≥ 6` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSix
    (hSix : ResidueCanonicalFromSqrtSixAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtFive
    (residueCanonicalFromSqrtFiveWithConstant_of_fromSqrtSix hSix)

/-- Final Path C adapter after the closed `sqrt n = 5` prefix: the finite-sieve
worker only has to prove the `sqrt n ≥ 6` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSix_and_countingInput
    (hSix : ResidueCanonicalFromSqrtSixAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtFive_and_countingInput
    (residueCanonicalFromSqrtFiveWithConstant_of_fromSqrtSix hSix) hCounting

end PathCResidueCanonicalSqrtFiveSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.one_fifth_le_goldbachResidueMainFactor_at_five
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.residueCanonicalSqrtFiveAtSqrt_five
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.residueCanonicalFromSqrtFiveAtSqrt_of_sqrtFive_and_fromSqrtSix
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.residueCanonicalFromSqrtFiveWithConstant_of_fromSqrtSix
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.residueCanonicalWithConstant_of_fromSqrtSix
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.finiteSieveInput_of_residueCanonicalFromSqrtSix
#print axioms
  Gdbh.PathCResidueCanonicalSqrtFiveSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSix_and_countingInput
