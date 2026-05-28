/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSevenToTenSplit

/-!
# Path C -- corrected residue canonical sqrt-eleven-to-sixteen split

Round 29 removed the block `7 ≤ Nat.sqrt n ≤ 10` from the corrected residue
canonical target.  This file removes the next block `11 ≤ Nat.sqrt n ≤ 16`,
where the odd-prime residue range is either `{3, 5, 7, 11}` or
`{3, 5, 7, 11, 13}`, and leaves the strictly smaller residual
`17 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtElevenToSixteenSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtSevenToTenSplit
  (ResidueCanonicalFromSqrtElevenAtSqrt
   ResidueCanonicalFromSqrtElevenAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtEleven
   pathC_kGoldbach_of_residueCanonicalFromSqrtEleven_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtEleven)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual: `11 ≤ Nat.sqrt n ≤ 16`. -/
def ResidueCanonicalSqrtElevenToSixteenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 11 ≤ Nat.sqrt n → Nat.sqrt n ≤ 16 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`11 ≤ sqrt n ≤ 16`. -/
def ResidueCanonicalFromSqrtSeventeenAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 17 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 17` residual. -/
def ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSeventeenAtSqrt C₁

/-! ## Elementary local-factor lower bounds -/

/-- Each odd-prime residue factor is bounded below by the crude
`1 - 2 / p`, because the bad residue set has cardinal at most two. -/
theorem residueFactorTerm_lower_two (n p : ℕ) (hp : 0 < p) :
    1 - (2 : ℝ) / (p : ℝ)
      ≤ 1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) := by
  have hcard_nat : (goldbachBadResidueSet n p).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n p
  have hcard : ((goldbachBadResidueSet n p).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_nat
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  have hdiv :
      ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)
        ≤ (2 : ℝ) / (p : ℝ) :=
    div_le_div_of_nonneg_right hcard (le_of_lt hp_pos)
  linarith

/-- Four-prime lower bound for residue factors `{3, 5, 7, 11}`. -/
theorem one_eleventh_le_residueFactorProduct_three_five_seven_eleven (n : ℕ) :
    (1 / 11 : ℝ) ≤
      ∏ p ∈ ({3, 5, 7, 11} : Finset ℕ),
        (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
  classical
  rw [show ({3, 5, 7, 11} : Finset ℕ) =
      insert 3 (insert 5 (insert 7 ({11} : Finset ℕ))) from rfl]
  rw [Finset.prod_insert
      (by decide : (3 : ℕ) ∉ insert 5 (insert 7 ({11} : Finset ℕ)))]
  rw [Finset.prod_insert
      (by decide : (5 : ℕ) ∉ insert 7 ({11} : Finset ℕ))]
  rw [Finset.prod_insert (by decide : (7 : ℕ) ∉ ({11} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have h3 :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    have h := residueFactorTerm_lower_two n 3 (by norm_num)
    norm_num at h
    exact h
  have h5 :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    have h := residueFactorTerm_lower_two n 5 (by norm_num)
    norm_num at h
    exact h
  have h7 :
      (5 / 7 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 := by
    have h := residueFactorTerm_lower_two n 7 (by norm_num)
    norm_num at h
    exact h
  have h11 :
      (9 / 11 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 11).card : ℝ) / 11 := by
    have h := residueFactorTerm_lower_two n 11 (by norm_num)
    norm_num at h
    exact h
  have h3_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 :=
    (by norm_num : (0 : ℝ) ≤ 1 / 3).trans h3
  have h5_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 :=
    (by norm_num : (0 : ℝ) ≤ 3 / 5).trans h5
  have h7_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 :=
    (by norm_num : (0 : ℝ) ≤ 5 / 7).trans h7
  have hmul_7_11 :=
    mul_le_mul h7 h11 (by norm_num : (0 : ℝ) ≤ 9 / 11) h7_nonneg
  have hmul_5_tail :=
    mul_le_mul h5 hmul_7_11
      (by norm_num : (0 : ℝ) ≤ (5 / 7 : ℝ) * (9 / 11)) h5_nonneg
  have hmul_all :=
    mul_le_mul h3 hmul_5_tail
      (by norm_num : (0 : ℝ) ≤ (3 / 5 : ℝ) * ((5 / 7) * (9 / 11)))
      h3_nonneg
  have hmul_all' :
      (9 / 77 : ℝ) ≤
        (1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3) *
          ((1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5) *
            ((1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7) *
              (1 - ((goldbachBadResidueSet n 11).card : ℝ) / 11))) := by
    norm_num at hmul_all
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all
  exact (by norm_num : (1 / 11 : ℝ) ≤ 9 / 77).trans
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all')

/-- Five-prime lower bound for residue factors `{3, 5, 7, 11, 13}`. -/
theorem one_eleventh_le_residueFactorProduct_three_five_seven_eleven_thirteen
    (n : ℕ) :
    (1 / 11 : ℝ) ≤
      ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
        (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
  classical
  rw [show ({3, 5, 7, 11, 13} : Finset ℕ) =
      insert 3 (insert 5 (insert 7 (insert 11 ({13} : Finset ℕ)))) from rfl]
  rw [Finset.prod_insert
      (by decide : (3 : ℕ) ∉ insert 5 (insert 7 (insert 11 ({13} : Finset ℕ))))]
  rw [Finset.prod_insert
      (by decide : (5 : ℕ) ∉ insert 7 (insert 11 ({13} : Finset ℕ)))]
  rw [Finset.prod_insert
      (by decide : (7 : ℕ) ∉ insert 11 ({13} : Finset ℕ))]
  rw [Finset.prod_insert (by decide : (11 : ℕ) ∉ ({13} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have h3 :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    have h := residueFactorTerm_lower_two n 3 (by norm_num)
    norm_num at h
    exact h
  have h5 :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    have h := residueFactorTerm_lower_two n 5 (by norm_num)
    norm_num at h
    exact h
  have h7 :
      (5 / 7 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 := by
    have h := residueFactorTerm_lower_two n 7 (by norm_num)
    norm_num at h
    exact h
  have h11 :
      (9 / 11 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 11).card : ℝ) / 11 := by
    have h := residueFactorTerm_lower_two n 11 (by norm_num)
    norm_num at h
    exact h
  have h13 :
      (11 / 13 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 13).card : ℝ) / 13 := by
    have h := residueFactorTerm_lower_two n 13 (by norm_num)
    norm_num at h
    exact h
  have h3_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 :=
    (by norm_num : (0 : ℝ) ≤ 1 / 3).trans h3
  have h5_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 :=
    (by norm_num : (0 : ℝ) ≤ 3 / 5).trans h5
  have h7_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 :=
    (by norm_num : (0 : ℝ) ≤ 5 / 7).trans h7
  have h11_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 11).card : ℝ) / 11 :=
    (by norm_num : (0 : ℝ) ≤ 9 / 11).trans h11
  have hmul_11_13 :=
    mul_le_mul h11 h13 (by norm_num : (0 : ℝ) ≤ 11 / 13) h11_nonneg
  have hmul_7_tail :=
    mul_le_mul h7 hmul_11_13
      (by norm_num : (0 : ℝ) ≤ (9 / 11 : ℝ) * (11 / 13)) h7_nonneg
  have hmul_5_tail :=
    mul_le_mul h5 hmul_7_tail
      (by norm_num :
        (0 : ℝ) ≤ (5 / 7 : ℝ) * ((9 / 11) * (11 / 13))) h5_nonneg
  have hmul_all :=
    mul_le_mul h3 hmul_5_tail
      (by norm_num :
        (0 : ℝ) ≤ (3 / 5 : ℝ) * ((5 / 7) * ((9 / 11) * (11 / 13))))
      h3_nonneg
  have hmul_all' :
      (9 / 91 : ℝ) ≤
        (1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3) *
          ((1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5) *
            ((1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7) *
              ((1 - ((goldbachBadResidueSet n 11).card : ℝ) / 11) *
                (1 - ((goldbachBadResidueSet n 13).card : ℝ) / 13)))) := by
    norm_num at hmul_all
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all
  exact (by norm_num : (1 / 11 : ℝ) ≤ 9 / 91).trans
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all')

/-- For `11 ≤ z ≤ 16`, the odd-prime residue main factor is always at least
`1 / 11`. -/
theorem one_eleventh_le_goldbachResidueMainFactor_of_eleven_le_of_le_sixteen
    (n z : ℕ) (hz11 : 11 ≤ z) (hz16 : z ≤ 16) :
    (1 / 11 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  interval_cases z
  · have hfilter :
        (Finset.Icc 3 11).filter Nat.Prime =
          ({3, 5, 7, 11} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven n
  · have hfilter :
        (Finset.Icc 3 12).filter Nat.Prime =
          ({3, 5, 7, 11} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven n
  · have hfilter :
        (Finset.Icc 3 13).filter Nat.Prime =
          ({3, 5, 7, 11, 13} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven_thirteen n
  · have hfilter :
        (Finset.Icc 3 14).filter Nat.Prime =
          ({3, 5, 7, 11, 13} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven_thirteen n
  · have hfilter :
        (Finset.Icc 3 15).filter Nat.Prime =
          ({3, 5, 7, 11, 13} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven_thirteen n
  · have hfilter :
        (Finset.Icc 3 16).filter Nat.Prime =
          ({3, 5, 7, 11, 13} : Finset ℕ) := by
      decide
    simpa [goldbachResidueMainFactor, hfilter] using
      one_eleventh_le_residueFactorProduct_three_five_seven_eleven_thirteen n

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `11 ≤ Nat.sqrt n ≤ 16` of the corrected residual is closed
with coefficient `11`, by the trivial count bound and the `1 / 11`
local-factor lower bound. -/
theorem residueCanonicalSqrtElevenToSixteenAtSqrt_eleven :
    ResidueCanonicalSqrtElevenToSixteenAtSqrt 11 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt_ge_eleven hsqrt_le_sixteen
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_eleventh :
      (1 / 11 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_eleventh_le_goldbachResidueMainFactor_of_eleven_le_of_le_sixteen
      n (Nat.sqrt n) hsqrt_ge_eleven hsqrt_le_sixteen
  have hfactor_scaled :
      (1 : ℝ) ≤ 11 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (11 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (11 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (11 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `11 ≤ sqrt n ≤ 16` block and a `sqrt n ≥ 17` residual combine
into the Round 29 residual `sqrt n ≥ 11`. -/
theorem residueCanonicalFromSqrtElevenAtSqrt_of_sqrtElevenToSixteen_and_fromSqrtSeventeen
    {Cblock C17 : ℝ}
    (hBlock : ResidueCanonicalSqrtElevenToSixteenAtSqrt Cblock)
    (hSeventeen : ResidueCanonicalFromSqrtSeventeenAtSqrt C17) :
    ResidueCanonicalFromSqrtElevenAtSqrt (max Cblock C17) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hSeventeen with ⟨_hC17_pos, hSeventeenBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C17), ?_⟩
  intro n hn hsqrt_ge_eleven
  by_cases hsqrt_le_sixteen : Nat.sqrt n ≤ 16
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C17)
      (hBlockBd n hn hsqrt_ge_eleven hsqrt_le_sixteen)
  · have hsqrt_ge_seventeen : 17 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C17)
      (hSeventeenBd n hn hsqrt_ge_seventeen)

/-- The only remaining finite-sieve worker target after the closed
`11 ≤ sqrt n ≤ 16` block is the `sqrt n ≥ 17` residual. -/
theorem residueCanonicalFromSqrtElevenWithConstant_of_fromSqrtSeventeen
    (hSeventeen : ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtElevenAtSqrtWithConstant := by
  rcases hSeventeen with ⟨C17, hSeventeen⟩
  exact ⟨max 11 C17,
    residueCanonicalFromSqrtElevenAtSqrt_of_sqrtElevenToSixteen_and_fromSqrtSeventeen
      residueCanonicalSqrtElevenToSixteenAtSqrt_eleven hSeventeen⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSeventeen
    (hSeventeen : ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtEleven
    (residueCanonicalFromSqrtElevenWithConstant_of_fromSqrtSeventeen hSeventeen)

/-- `sqrt n ≥ 17` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSeventeen
    (hSeventeen : ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtEleven
    (residueCanonicalFromSqrtElevenWithConstant_of_fromSqrtSeventeen hSeventeen)

/-- Final Path C adapter after the closed `11 ≤ sqrt n ≤ 16` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 17` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSeventeen_and_countingInput
    (hSeventeen : ResidueCanonicalFromSqrtSeventeenAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtEleven_and_countingInput
    (residueCanonicalFromSqrtElevenWithConstant_of_fromSqrtSeventeen hSeventeen)
    hCounting

end PathCResidueCanonicalSqrtElevenToSixteenSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.residueFactorTerm_lower_two
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.one_eleventh_le_goldbachResidueMainFactor_of_eleven_le_of_le_sixteen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.residueCanonicalSqrtElevenToSixteenAtSqrt_eleven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.residueCanonicalFromSqrtElevenAtSqrt_of_sqrtElevenToSixteen_and_fromSqrtSeventeen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.residueCanonicalFromSqrtElevenWithConstant_of_fromSqrtSeventeen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.residueCanonicalWithConstant_of_fromSqrtSeventeen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.finiteSieveInput_of_residueCanonicalFromSqrtSeventeen
#print axioms
  Gdbh.PathCResidueCanonicalSqrtElevenToSixteenSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSeventeen_and_countingInput
