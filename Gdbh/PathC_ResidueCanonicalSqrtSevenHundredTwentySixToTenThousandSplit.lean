/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSevenHundredOneToSevenHundredTwentyFiveSplit

/-!
# Path C -- corrected residue canonical sqrt-seven-hundred-twenty-six-to-ten-thousand split

Round 38 left the corrected residue canonical target with the residual
`726 ≤ Nat.sqrt n`.  The long explicit-prime products used by the preceding
finite blocks become expensive past this point.  This file switches to a
coarser but uniform product lower bound: every crude residue factor with
`3 ≤ p` is at least `1 / 3`, so every finite range `z ≤ N` has a positive
lower bound `(1 / 3)^N`.

The resulting constant is large, but finite and non-vacuous.  It removes the
entire block `726 ≤ Nat.sqrt n ≤ 10000` and advances the worker residual to
`10001 ≤ Nat.sqrt n`.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit

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
  (crudeResidueFactor crudeResidueFactor_nonneg_of_three_le)
open Gdbh.PathCResidueCanonicalSqrtSevenHundredOneToSevenHundredTwentyFiveSplit
  (ResidueCanonicalFromSqrtSevenHundredTwentySixAtSqrt
   ResidueCanonicalFromSqrtSevenHundredTwentySixAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSevenHundredTwentySix
   pathC_kGoldbach_of_residueCanonicalFromSqrtSevenHundredTwentySix_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSevenHundredTwentySix)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`726 ≤ Nat.sqrt n ≤ 10000`. -/
def ResidueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt
    (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 726 ≤ Nat.sqrt n → Nat.sqrt n ≤ 10000 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`726 ≤ sqrt n ≤ 10000`. -/
def ResidueCanonicalFromSqrtTenThousandOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 10001 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 10001` residual. -/
def ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtTenThousandOneAtSqrt C₁

/-! ## Uniform coarse product lower bound -/

/-- Every crude residue factor in the odd-prime range is at least `1 / 3`. -/
theorem crudeResidueFactor_lower_one_third_of_three_le {p : ℕ} (hp3 : 3 ≤ p) :
    (1 / 3 : ℝ) ≤ crudeResidueFactor p := by
  unfold crudeResidueFactor
  have hp : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp_pos : (0 : ℝ) < (p : ℝ) := by nlinarith
  field_simp [hp_pos.ne']
  nlinarith

/-- A product of crude factors is bounded below by `(1 / 3)` to its
cardinality. -/
theorem one_third_pow_card_le_crudeResidueFactorProduct
    {s : Finset ℕ} (h3s : ∀ p ∈ s, 3 ≤ p) :
    (1 / 3 : ℝ) ^ s.card ≤ ∏ p ∈ s, crudeResidueFactor p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h3a : 3 ≤ a := h3s a (Finset.mem_insert_self a s)
      have h3s' : ∀ p ∈ s, 3 ≤ p := by
        intro p hp
        exact h3s p (Finset.mem_insert_of_mem hp)
      have ih' := ih h3s'
      have hfac : (1 / 3 : ℝ) ≤ crudeResidueFactor a :=
        crudeResidueFactor_lower_one_third_of_three_le h3a
      have hpow_nonneg : 0 ≤ (1 / 3 : ℝ) ^ s.card := by positivity
      have hmul :
          (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ s.card ≤
            crudeResidueFactor a * ∏ p ∈ s, crudeResidueFactor p := by
        exact mul_le_mul hfac ih' hpow_nonneg
          (crudeResidueFactor_nonneg_of_three_le h3a)
      simpa [Finset.prod_insert, ha, pow_succ, mul_comm, mul_left_comm,
        mul_assoc] using hmul

/-- If the product has at most `N` factors, the coarser lower bound `(1 / 3)^N`
applies. -/
theorem one_third_pow_bound_le_crudeResidueFactorProduct
    {s : Finset ℕ} {N : ℕ} (hcard : s.card ≤ N) (h3s : ∀ p ∈ s, 3 ≤ p) :
    (1 / 3 : ℝ) ^ N ≤ ∏ p ∈ s, crudeResidueFactor p := by
  have hpow : (1 / 3 : ℝ) ^ N ≤ (1 / 3 : ℝ) ^ s.card := by
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 / 3 : ℝ) ≤ 1) hcard
  exact hpow.trans (one_third_pow_card_le_crudeResidueFactorProduct h3s)

/-- Uniform coarse lower bound for the residue main factor through `z ≤ 10000`. -/
theorem one_third_pow_ten_thousand_le_goldbachResidueMainFactor_of_le_ten_thousand
    (n z : ℕ) (hz10000 : z ≤ 10000) :
    (1 / 3 : ℝ) ^ 10000 ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hcard_le_z : Pz.card ≤ z := by
    have hfilter : Pz.card ≤ (Finset.Icc 3 z).card := by
      simpa [Pz] using Finset.card_filter_le (Finset.Icc 3 z) Nat.Prime
    have hIcc : (Finset.Icc 3 z).card ≤ z := by
      rw [Nat.card_Icc]
      omega
    exact hfilter.trans hIcc
  have hcard : Pz.card ≤ 10000 := hcard_le_z.trans hz10000
  have hcrude_z :
      (1 / 3 : ℝ) ^ 10000 ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_third_pow_bound_le_crudeResidueFactorProduct hcard h3_z
  have hactual :
      (∏ p ∈ Pz, crudeResidueFactor p) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
    simpa [crudeResidueFactor] using
      residueFactorProduct_lower_two_of_three_le n Pz h3_z
  have hmain :
      (1 / 3 : ℝ) ^ 10000 ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
    hcrude_z.trans hactual
  simpa [goldbachResidueMainFactor, Pz] using hmain

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `726 ≤ Nat.sqrt n ≤ 10000` of the corrected residual is
closed with the finite coarse constant `3^10000`. -/
theorem residueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt_three_pow :
    ResidueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt
      ((3 : ℝ) ^ 10000) := by
  refine ⟨by positivity, ?_⟩
  intro n _hn _hsqrt_ge_seven_hundred_twenty_six hsqrt_le_ten_thousand
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_lower :
      (1 / 3 : ℝ) ^ 10000 ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_third_pow_ten_thousand_le_goldbachResidueMainFactor_of_le_ten_thousand
      n (Nat.sqrt n) hsqrt_le_ten_thousand
  have hfactor_scaled :
      (1 : ℝ) ≤
        (3 : ℝ) ^ 10000 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ 10000 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hfactor_lower hnonneg
    calc
      (1 : ℝ) = (3 : ℝ) ^ 10000 * (1 / 3 : ℝ) ^ 10000 := by
        rw [← mul_pow]
        norm_num
      _ ≤ (3 : ℝ) ^ 10000 * goldbachResidueMainFactor n (Nat.sqrt n) := hmul
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        ((3 : ℝ) ^ 10000) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (((3 : ℝ) ^ 10000) *
            goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = ((3 : ℝ) ^ 10000) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ac_rfl
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `726 ≤ sqrt n ≤ 10000` block and a `sqrt n ≥ 10001` residual
combine into the Round 38 residual `sqrt n ≥ 726`. -/
theorem residueCanonicalFromSqrtSevenHundredTwentySixAtSqrt_of_sqrtSevenHundredTwentySixToTenThousand_and_fromSqrtTenThousandOne
    {Cblock C10001 : ℝ}
    (hBlock : ResidueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt Cblock)
    (hTenThousandOne : ResidueCanonicalFromSqrtTenThousandOneAtSqrt C10001) :
    ResidueCanonicalFromSqrtSevenHundredTwentySixAtSqrt (max Cblock C10001) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hTenThousandOne with ⟨_hC10001_pos, hTenThousandOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C10001), ?_⟩
  intro n hn hsqrt_ge_seven_hundred_twenty_six
  by_cases hsqrt_le_ten_thousand : Nat.sqrt n ≤ 10000
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C10001)
      (hBlockBd n hn hsqrt_ge_seven_hundred_twenty_six hsqrt_le_ten_thousand)
  · have hsqrt_ge_ten_thousand_one : 10001 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C10001)
      (hTenThousandOneBd n hn hsqrt_ge_ten_thousand_one)

/-- The only remaining finite-sieve worker target after the closed
`726 ≤ sqrt n ≤ 10000` block is the `sqrt n ≥ 10001` residual. -/
theorem residueCanonicalFromSqrtSevenHundredTwentySixWithConstant_of_fromSqrtTenThousandOne
    (hTenThousandOne : ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSevenHundredTwentySixAtSqrtWithConstant := by
  rcases hTenThousandOne with ⟨C10001, hTenThousandOne⟩
  exact ⟨max ((3 : ℝ) ^ 10000) C10001,
    residueCanonicalFromSqrtSevenHundredTwentySixAtSqrt_of_sqrtSevenHundredTwentySixToTenThousand_and_fromSqrtTenThousandOne
      residueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt_three_pow
      hTenThousandOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtTenThousandOne
    (hTenThousandOne : ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSevenHundredTwentySix
    (residueCanonicalFromSqrtSevenHundredTwentySixWithConstant_of_fromSqrtTenThousandOne
      hTenThousandOne)

/-- `sqrt n ≥ 10001` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtTenThousandOne
    (hTenThousandOne : ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSevenHundredTwentySix
    (residueCanonicalFromSqrtSevenHundredTwentySixWithConstant_of_fromSqrtTenThousandOne
      hTenThousandOne)

/-- Final Path C adapter after the closed `726 ≤ sqrt n ≤ 10000` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 10001` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtTenThousandOne_and_countingInput
    (hTenThousandOne : ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSevenHundredTwentySix_and_countingInput
    (residueCanonicalFromSqrtSevenHundredTwentySixWithConstant_of_fromSqrtTenThousandOne
      hTenThousandOne)
    hCounting

end PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.one_third_pow_ten_thousand_le_goldbachResidueMainFactor_of_le_ten_thousand
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.residueCanonicalSqrtSevenHundredTwentySixToTenThousandAtSqrt_three_pow
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.residueCanonicalFromSqrtSevenHundredTwentySixAtSqrt_of_sqrtSevenHundredTwentySixToTenThousand_and_fromSqrtTenThousandOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.residueCanonicalFromSqrtSevenHundredTwentySixWithConstant_of_fromSqrtTenThousandOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.residueCanonicalWithConstant_of_fromSqrtTenThousandOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.finiteSieveInput_of_residueCanonicalFromSqrtTenThousandOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtTenThousandOne_and_countingInput
