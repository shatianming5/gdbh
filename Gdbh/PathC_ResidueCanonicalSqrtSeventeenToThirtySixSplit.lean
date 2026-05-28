/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtElevenToSixteenSplit

/-!
# Path C -- corrected residue canonical sqrt-seventeen-to-thirty-six split

Round 30 removed the block `11 ≤ Nat.sqrt n ≤ 16` from the corrected residue
canonical target.  This file removes the next larger block
`17 ≤ Nat.sqrt n ≤ 36`.  The crude residue-factor lower bound
`∏ p ≤ 36, p prime, p ≥ 3, (1 - 2 / p) ≥ 1 / 17` is still strong enough in
this range, so the block closes with coefficient `17` and leaves the strictly
smaller residual `37 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtSeventeenToThirtySixSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit
  (ResidueCanonicalFromSqrtSeventeenAtSqrt
   ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSeventeen
   pathC_kGoldbach_of_residueCanonicalFromSqrtSeventeen_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSeventeen
   residueFactorTerm_lower_two)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual: `17 ≤ Nat.sqrt n ≤ 36`. -/
def ResidueCanonicalSqrtSeventeenToThirtySixAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 17 ≤ Nat.sqrt n → Nat.sqrt n ≤ 36 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`17 ≤ sqrt n ≤ 36`. -/
def ResidueCanonicalFromSqrtThirtySevenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 37 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 37` residual. -/
def ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtThirtySevenAtSqrt C₁

/-! ## Local-factor lower bounds -/

/-- The crude `1 - 2 / p` lower bounds multiply over any explicit odd-prime
set whose elements are at least three. -/
theorem residueFactorProduct_lower_two_of_three_le (n : ℕ) (s : Finset ℕ)
    (h3 : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, (1 - (2 : ℝ) / (p : ℝ))) ≤
      ∏ p ∈ s,
        (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
  classical
  refine Finset.prod_le_prod ?nonneg ?hle
  · intro p hp
    have hp3 : 3 ≤ p := h3 p hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hp3)
    have htwo_le : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hp3)
    have hdiv_le_one : (2 : ℝ) / (p : ℝ) ≤ 1 := by
      rw [div_le_one hp_pos]
      exact htwo_le
    linarith
  · intro p hp
    exact residueFactorTerm_lower_two n p
      (lt_of_lt_of_le (by norm_num : 0 < 3) (h3 p hp))

/-- Any explicit odd-prime factor set whose crude product is at least
`1 / 17` gives the corresponding residue-main-factor lower bound. -/
theorem one_seventeenth_le_residueFactorProduct_of_three_le
    (n : ℕ) (s : Finset ℕ)
    (h3 : ∀ p ∈ s, 3 ≤ p)
    (hconst :
      (1 / 17 : ℝ) ≤ ∏ p ∈ s, (1 - (2 : ℝ) / (p : ℝ))) :
    (1 / 17 : ℝ) ≤
      ∏ p ∈ s,
        (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
  hconst.trans (residueFactorProduct_lower_two_of_three_le n s h3)

/-- For `17 ≤ z ≤ 18`, the odd-prime residue main factor is at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_eighteen
    (n z : ℕ) (hz17 : 17 ≤ z) (hz18 : z ≤ 18) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime =
        ({3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    interval_cases z <;> decide
  simpa [goldbachResidueMainFactor, hfilter] using
    one_seventeenth_le_residueFactorProduct_of_three_le n
      ({3, 5, 7, 11, 13, 17} : Finset ℕ) (by decide) (by norm_num)

/-- For `19 ≤ z ≤ 22`, the odd-prime residue main factor is at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_nineteen_le_of_le_twenty_two
    (n z : ℕ) (hz19 : 19 ≤ z) (hz22 : z ≤ 22) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime =
        ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by
    interval_cases z <;> decide
  simpa [goldbachResidueMainFactor, hfilter] using
    one_seventeenth_le_residueFactorProduct_of_three_le n
      ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) (by decide) (by norm_num)

/-- For `23 ≤ z ≤ 28`, the odd-prime residue main factor is at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_twenty_three_le_of_le_twenty_eight
    (n z : ℕ) (hz23 : 23 ≤ z) (hz28 : z ≤ 28) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime =
        ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by
    interval_cases z <;> decide
  simpa [goldbachResidueMainFactor, hfilter] using
    one_seventeenth_le_residueFactorProduct_of_three_le n
      ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) (by decide) (by norm_num)

/-- For `29 ≤ z ≤ 30`, the odd-prime residue main factor is at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_twenty_nine_le_of_le_thirty
    (n z : ℕ) (hz29 : 29 ≤ z) (hz30 : z ≤ 30) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime =
        ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
    interval_cases z <;> decide
  simpa [goldbachResidueMainFactor, hfilter] using
    one_seventeenth_le_residueFactorProduct_of_three_le n
      ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) (by decide) (by norm_num)

/-- For `31 ≤ z ≤ 36`, the odd-prime residue main factor is at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_thirty_one_le_of_le_thirty_six
    (n z : ℕ) (hz31 : 31 ≤ z) (hz36 : z ≤ 36) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  have hfilter :
      (Finset.Icc 3 z).filter Nat.Prime =
        ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by
    interval_cases z <;> decide
  simpa [goldbachResidueMainFactor, hfilter] using
    one_seventeenth_le_residueFactorProduct_of_three_le n
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) (by decide)
      (by norm_num)

/-- For `17 ≤ z ≤ 36`, the odd-prime residue main factor is always at least
`1 / 17`. -/
theorem one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_thirty_six
    (n z : ℕ) (hz17 : 17 ≤ z) (hz36 : z ≤ 36) :
    (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n z := by
  by_cases hz18 : z ≤ 18
  · exact
      one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_eighteen
        n z hz17 hz18
  by_cases hz22 : z ≤ 22
  · have hz19 : 19 ≤ z := by omega
    exact
      one_seventeenth_le_goldbachResidueMainFactor_of_nineteen_le_of_le_twenty_two
        n z hz19 hz22
  by_cases hz28 : z ≤ 28
  · have hz23 : 23 ≤ z := by omega
    exact
      one_seventeenth_le_goldbachResidueMainFactor_of_twenty_three_le_of_le_twenty_eight
        n z hz23 hz28
  by_cases hz30 : z ≤ 30
  · have hz29 : 29 ≤ z := by omega
    exact
      one_seventeenth_le_goldbachResidueMainFactor_of_twenty_nine_le_of_le_thirty
        n z hz29 hz30
  · have hz31 : 31 ≤ z := by omega
    exact
      one_seventeenth_le_goldbachResidueMainFactor_of_thirty_one_le_of_le_thirty_six
        n z hz31 hz36

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `17 ≤ Nat.sqrt n ≤ 36` of the corrected residual is closed
with coefficient `17`, by the trivial count bound and the `1 / 17`
local-factor lower bound. -/
theorem residueCanonicalSqrtSeventeenToThirtySixAtSqrt_seventeen :
    ResidueCanonicalSqrtSeventeenToThirtySixAtSqrt 17 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt_ge_seventeen hsqrt_le_thirty_six
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_seventeenth :
      (1 / 17 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_thirty_six
      n (Nat.sqrt n) hsqrt_ge_seventeen hsqrt_le_thirty_six
  have hfactor_scaled :
      (1 : ℝ) ≤ 17 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (17 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (17 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (17 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `17 ≤ sqrt n ≤ 36` block and a `sqrt n ≥ 37` residual combine
into the Round 30 residual `sqrt n ≥ 17`. -/
theorem residueCanonicalFromSqrtSeventeenAtSqrt_of_sqrtSeventeenToThirtySix_and_fromSqrtThirtySeven
    {Cblock C37 : ℝ}
    (hBlock : ResidueCanonicalSqrtSeventeenToThirtySixAtSqrt Cblock)
    (hThirtySeven : ResidueCanonicalFromSqrtThirtySevenAtSqrt C37) :
    ResidueCanonicalFromSqrtSeventeenAtSqrt (max Cblock C37) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hThirtySeven with ⟨_hC37_pos, hThirtySevenBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C37), ?_⟩
  intro n hn hsqrt_ge_seventeen
  by_cases hsqrt_le_thirty_six : Nat.sqrt n ≤ 36
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C37)
      (hBlockBd n hn hsqrt_ge_seventeen hsqrt_le_thirty_six)
  · have hsqrt_ge_thirty_seven : 37 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C37)
      (hThirtySevenBd n hn hsqrt_ge_thirty_seven)

/-- The only remaining finite-sieve worker target after the closed
`17 ≤ sqrt n ≤ 36` block is the `sqrt n ≥ 37` residual. -/
theorem residueCanonicalFromSqrtSeventeenWithConstant_of_fromSqrtThirtySeven
    (hThirtySeven : ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant := by
  rcases hThirtySeven with ⟨C37, hThirtySeven⟩
  exact ⟨max 17 C37,
    residueCanonicalFromSqrtSeventeenAtSqrt_of_sqrtSeventeenToThirtySix_and_fromSqrtThirtySeven
      residueCanonicalSqrtSeventeenToThirtySixAtSqrt_seventeen hThirtySeven⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtThirtySeven
    (hThirtySeven : ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSeventeen
    (residueCanonicalFromSqrtSeventeenWithConstant_of_fromSqrtThirtySeven
      hThirtySeven)

/-- `sqrt n ≥ 37` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtThirtySeven
    (hThirtySeven : ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSeventeen
    (residueCanonicalFromSqrtSeventeenWithConstant_of_fromSqrtThirtySeven
      hThirtySeven)

/-- Final Path C adapter after the closed `17 ≤ sqrt n ≤ 36` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 37` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtThirtySeven_and_countingInput
    (hThirtySeven : ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSeventeen_and_countingInput
    (residueCanonicalFromSqrtSeventeenWithConstant_of_fromSqrtThirtySeven
      hThirtySeven)
    hCounting

end PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.residueFactorProduct_lower_two_of_three_le
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_thirty_six
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.residueCanonicalSqrtSeventeenToThirtySixAtSqrt_seventeen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.residueCanonicalFromSqrtSeventeenAtSqrt_of_sqrtSeventeenToThirtySix_and_fromSqrtThirtySeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.residueCanonicalFromSqrtSeventeenWithConstant_of_fromSqrtThirtySeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.residueCanonicalWithConstant_of_fromSqrtThirtySeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.finiteSieveInput_of_residueCanonicalFromSqrtThirtySeven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtThirtySeven_and_countingInput
