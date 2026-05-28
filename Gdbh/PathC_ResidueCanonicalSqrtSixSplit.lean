/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtFiveSplit

/-!
# Path C -- corrected residue canonical sqrt-six split

Round 27 removed the `Nat.sqrt n = 5` prefix from the corrected residue
canonical target.  This file removes the next finite prefix, `Nat.sqrt n = 6`,
and leaves the strictly smaller residual `7 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtSixSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtFiveSplit
  (ResidueCanonicalFromSqrtSixAtSqrt
   ResidueCanonicalFromSqrtSixAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSix
   pathC_kGoldbach_of_residueCanonicalFromSqrtSix_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSix)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite prefix of the corrected residual: `Nat.sqrt n = 6`. -/
def ResidueCanonicalSqrtSixAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 6 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the `sqrt n = 6`
prefix. -/
def ResidueCanonicalFromSqrtSevenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 7 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 7` residual. -/
def ResidueCanonicalFromSqrtSevenAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSevenAtSqrt C₁

/-! ## Elementary closed prefix -/

/-- At `z = 6`, the odd-prime residue main factor is always at least `1 / 5`.
The odd-prime range is still `{3, 5}`, and each bad-residue cardinal is at
most two. -/
theorem one_fifth_le_goldbachResidueMainFactor_at_six (n : ℕ) :
    (1 / 5 : ℝ) ≤ goldbachResidueMainFactor n 6 := by
  classical
  have hfilter :
      (Finset.Icc 3 6).filter Nat.Prime = ({3, 5} : Finset ℕ) := by
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

/-- The whole `Nat.sqrt n = 6` prefix of the corrected residual is closed with
coefficient `5`, by the trivial count bound and the `1 / 5` local-factor lower
bound. -/
theorem residueCanonicalSqrtSixAtSqrt_five :
    ResidueCanonicalSqrtSixAtSqrt 5 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_fifth :
      (1 / 5 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) := by
    simpa [hsqrt] using one_fifth_le_goldbachResidueMainFactor_at_six n
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

/-! ## Bridge from the new large residual back to the Round 27 residual -/

/-- A closed `sqrt n = 6` prefix and a `sqrt n ≥ 7` residual combine into the
Round 27 residual `sqrt n ≥ 6`. -/
theorem residueCanonicalFromSqrtSixAtSqrt_of_sqrtSix_and_fromSqrtSeven
    {C₆ C₇ : ℝ}
    (hSixPrefix : ResidueCanonicalSqrtSixAtSqrt C₆)
    (hSeven : ResidueCanonicalFromSqrtSevenAtSqrt C₇) :
    ResidueCanonicalFromSqrtSixAtSqrt (max C₆ C₇) := by
  rcases hSixPrefix with ⟨hC₆_pos, hSixBd⟩
  rcases hSeven with ⟨_hC₇_pos, hSevenBd⟩
  refine ⟨lt_of_lt_of_le hC₆_pos (le_max_left C₆ C₇), ?_⟩
  intro n hn hsqrt_ge_six
  by_cases hsqrt : Nat.sqrt n = 6
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left C₆ C₇) (hSixBd n hn hsqrt)
  · have hsqrt_ge_seven : 7 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right C₆ C₇) (hSevenBd n hn hsqrt_ge_seven)

/-- The only remaining finite-sieve worker target after the closed `sqrt n = 6`
prefix is the `sqrt n ≥ 7` residual. -/
theorem residueCanonicalFromSqrtSixWithConstant_of_fromSqrtSeven
    (hSeven : ResidueCanonicalFromSqrtSevenAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSixAtSqrtWithConstant := by
  rcases hSeven with ⟨C₇, hSeven⟩
  exact ⟨max 5 C₇,
    residueCanonicalFromSqrtSixAtSqrt_of_sqrtSix_and_fromSqrtSeven
      residueCanonicalSqrtSixAtSqrt_five hSeven⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSeven
    (hSeven : ResidueCanonicalFromSqrtSevenAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSix
    (residueCanonicalFromSqrtSixWithConstant_of_fromSqrtSeven hSeven)

/-- `sqrt n ≥ 7` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSeven
    (hSeven : ResidueCanonicalFromSqrtSevenAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSix
    (residueCanonicalFromSqrtSixWithConstant_of_fromSqrtSeven hSeven)

/-- Final Path C adapter after the closed `sqrt n = 6` prefix: the finite-sieve
worker only has to prove the `sqrt n ≥ 7` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSeven_and_countingInput
    (hSeven : ResidueCanonicalFromSqrtSevenAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSix_and_countingInput
    (residueCanonicalFromSqrtSixWithConstant_of_fromSqrtSeven hSeven) hCounting

end PathCResidueCanonicalSqrtSixSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.one_fifth_le_goldbachResidueMainFactor_at_six
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.residueCanonicalSqrtSixAtSqrt_five
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.residueCanonicalFromSqrtSixAtSqrt_of_sqrtSix_and_fromSqrtSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.residueCanonicalFromSqrtSixWithConstant_of_fromSqrtSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.residueCanonicalWithConstant_of_fromSqrtSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.finiteSieveInput_of_residueCanonicalFromSqrtSeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSeven_and_countingInput
