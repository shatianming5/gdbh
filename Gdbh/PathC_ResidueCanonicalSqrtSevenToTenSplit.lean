/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSixSplit

/-!
# Path C -- corrected residue canonical sqrt-seven-to-ten split

Round 28 removed the `Nat.sqrt n = 6` prefix from the corrected residue
canonical target.  This file removes the whole next block
`7 ≤ Nat.sqrt n ≤ 10`, where the odd-prime residue range is still exactly
`{3, 5, 7}`, and leaves the strictly smaller residual `11 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtSevenToTenSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtSixSplit
  (ResidueCanonicalFromSqrtSevenAtSqrt
   ResidueCanonicalFromSqrtSevenAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSeven
   pathC_kGoldbach_of_residueCanonicalFromSqrtSeven_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSeven)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual: `7 ≤ Nat.sqrt n ≤ 10`. -/
def ResidueCanonicalSqrtSevenToTenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 7 ≤ Nat.sqrt n → Nat.sqrt n ≤ 10 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`7 ≤ sqrt n ≤ 10`. -/
def ResidueCanonicalFromSqrtElevenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 11 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 11` residual. -/
def ResidueCanonicalFromSqrtElevenAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtElevenAtSqrt C₁

/-! ## Elementary closed prefix block -/

/-- For `7 ≤ z ≤ 10`, the odd-prime residue main factor is always at least
`1 / 7`.  In this range the odd-prime set is exactly `{3, 5, 7}`, and each
bad-residue cardinal is at most two. -/
theorem one_seventh_le_goldbachResidueMainFactor_of_seven_le_of_le_ten
    (n z : ℕ) (hz7 : 7 ≤ z) (hz10 : z ≤ 10) :
    (1 / 7 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime = ({3, 5, 7} : Finset ℕ) := by
    interval_cases z <;> decide
  rw [goldbachResidueMainFactor, hfilter]
  rw [show ({3, 5, 7} : Finset ℕ) =
      insert 3 (insert 5 ({7} : Finset ℕ)) from rfl]
  rw [Finset.prod_insert (by decide : (3 : ℕ) ∉ insert 5 ({7} : Finset ℕ))]
  rw [Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have hcard_three_nat : (goldbachBadResidueSet n 3).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 3
  have hcard_five_nat : (goldbachBadResidueSet n 5).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 5
  have hcard_seven_nat : (goldbachBadResidueSet n 7).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 7
  have hcard_three : ((goldbachBadResidueSet n 3).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_three_nat
  have hcard_five : ((goldbachBadResidueSet n 5).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_five_nat
  have hcard_seven : ((goldbachBadResidueSet n 7).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_seven_nat
  have hthree :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hseven :
      (5 / 7 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 := by
    nlinarith
  have hthree_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hmul_five_seven :=
    mul_le_mul hfive hseven (by norm_num : (0 : ℝ) ≤ 5 / 7) hfive_nonneg
  have hmul_all :=
    mul_le_mul hthree hmul_five_seven
      (by norm_num : (0 : ℝ) ≤ (3 / 5) * (5 / 7)) hthree_nonneg
  norm_num at hmul_all
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all

/-- The whole block `7 ≤ Nat.sqrt n ≤ 10` of the corrected residual is closed
with coefficient `7`, by the trivial count bound and the `1 / 7` local-factor
lower bound. -/
theorem residueCanonicalSqrtSevenToTenAtSqrt_seven :
    ResidueCanonicalSqrtSevenToTenAtSqrt 7 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt_ge_seven hsqrt_le_ten
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_seventh :
      (1 / 7 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_seventh_le_goldbachResidueMainFactor_of_seven_le_of_le_ten
      n (Nat.sqrt n) hsqrt_ge_seven hsqrt_le_ten
  have hfactor_scaled :
      (1 : ℝ) ≤ 7 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (7 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (7 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (7 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-! ## Bridge from the new large residual back to the Round 28 residual -/

/-- A closed `7 ≤ sqrt n ≤ 10` block and a `sqrt n ≥ 11` residual combine into
the Round 28 residual `sqrt n ≥ 7`. -/
theorem residueCanonicalFromSqrtSevenAtSqrt_of_sqrtSevenToTen_and_fromSqrtEleven
    {Cblock C₁₁ : ℝ}
    (hSevenToTen : ResidueCanonicalSqrtSevenToTenAtSqrt Cblock)
    (hEleven : ResidueCanonicalFromSqrtElevenAtSqrt C₁₁) :
    ResidueCanonicalFromSqrtSevenAtSqrt (max Cblock C₁₁) := by
  rcases hSevenToTen with ⟨hCblock_pos, hSevenToTenBd⟩
  rcases hEleven with ⟨_hC₁₁_pos, hElevenBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C₁₁), ?_⟩
  intro n hn hsqrt_ge_seven
  by_cases hsqrt_le_ten : Nat.sqrt n ≤ 10
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C₁₁)
      (hSevenToTenBd n hn hsqrt_ge_seven hsqrt_le_ten)
  · have hsqrt_ge_eleven : 11 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C₁₁)
      (hElevenBd n hn hsqrt_ge_eleven)

/-- The only remaining finite-sieve worker target after the closed
`7 ≤ sqrt n ≤ 10` block is the `sqrt n ≥ 11` residual. -/
theorem residueCanonicalFromSqrtSevenWithConstant_of_fromSqrtEleven
    (hEleven : ResidueCanonicalFromSqrtElevenAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSevenAtSqrtWithConstant := by
  rcases hEleven with ⟨C₁₁, hEleven⟩
  exact ⟨max 7 C₁₁,
    residueCanonicalFromSqrtSevenAtSqrt_of_sqrtSevenToTen_and_fromSqrtEleven
      residueCanonicalSqrtSevenToTenAtSqrt_seven hEleven⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtEleven
    (hEleven : ResidueCanonicalFromSqrtElevenAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSeven
    (residueCanonicalFromSqrtSevenWithConstant_of_fromSqrtEleven hEleven)

/-- `sqrt n ≥ 11` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtEleven
    (hEleven : ResidueCanonicalFromSqrtElevenAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSeven
    (residueCanonicalFromSqrtSevenWithConstant_of_fromSqrtEleven hEleven)

/-- Final Path C adapter after the closed `7 ≤ sqrt n ≤ 10` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 11` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtEleven_and_countingInput
    (hEleven : ResidueCanonicalFromSqrtElevenAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSeven_and_countingInput
    (residueCanonicalFromSqrtSevenWithConstant_of_fromSqrtEleven hEleven)
    hCounting

end PathCResidueCanonicalSqrtSevenToTenSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.one_seventh_le_goldbachResidueMainFactor_of_seven_le_of_le_ten
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.residueCanonicalSqrtSevenToTenAtSqrt_seven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.residueCanonicalFromSqrtSevenAtSqrt_of_sqrtSevenToTen_and_fromSqrtEleven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.residueCanonicalFromSqrtSevenWithConstant_of_fromSqrtEleven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.residueCanonicalWithConstant_of_fromSqrtEleven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.finiteSieveInput_of_residueCanonicalFromSqrtEleven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtEleven_and_countingInput
