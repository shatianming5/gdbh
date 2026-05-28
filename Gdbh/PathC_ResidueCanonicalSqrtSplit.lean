/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalCorrectedRoute

/-!
# Path C -- corrected residue canonical sqrt split

`PathC_ResidueCanonicalCorrectedRoute` replaces the false coefficient-`1`
canonical residue target by a fixed-constant target.  This file peels off the
first nontrivial at-sqrt range, `Nat.sqrt n = 4`, and leaves the genuinely
asymptotic work as the strictly smaller residual `5 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor goldbachResidueMainFactor_nonneg
   goldbachResidueSiftedCount goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (ResidueCanonicalFixedConstantAtSqrt
   BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant
   finiteSieveInput_of_residueCanonicalWithConstant
   pathC_kGoldbach_of_residueCanonicalWithConstant_and_countingInput
   residueCanonicalWithConstant_of_fixed)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- The pointwise at-sqrt inequality for a fixed main-term coefficient. -/
def ResidueCanonicalAtSqrtInequality (C₁ : ℝ) (n : ℕ) : Prop :=
  (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
    ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
      + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Closed finite prefix of the corrected target: `Nat.sqrt n = 4`. -/
def ResidueCanonicalSqrtFourAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 4 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected target after removing the `sqrt n = 4`
prefix. -/
def ResidueCanonicalFromSqrtFiveAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 5 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the large-range residual. -/
def ResidueCanonicalFromSqrtFiveAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtFiveAtSqrt C₁

/-! ## Elementary closed prefix -/

/-- At `z = 4`, the odd-prime residue main factor only sees `p = 3`, so it is
always at least `1 / 3`. -/
theorem one_third_le_goldbachResidueMainFactor_at_four (n : ℕ) :
    (1 / 3 : ℝ) ≤ goldbachResidueMainFactor n 4 := by
  classical
  have hfilter :
      (Finset.Icc 3 4).filter Nat.Prime = ({3} : Finset ℕ) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hp3, hp4⟩, hpprime⟩
      interval_cases p
      · rfl
      · norm_num at hpprime
    · intro hp
      subst p
      exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  rw [goldbachResidueMainFactor, hfilter]
  simp only [Finset.prod_singleton]
  have hcard_le_nat : (goldbachBadResidueSet n 3).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 3
  have hcard_le : ((goldbachBadResidueSet n 3).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_le_nat
  have hdiv_le :
      ((goldbachBadResidueSet n 3).card : ℝ) / 3 ≤ (2 / 3 : ℝ) := by
    nlinarith
  nlinarith

/-- Increasing the fixed main-term coefficient preserves the pointwise
corrected at-sqrt inequality. -/
theorem residueCanonicalAtSqrtInequality_mono
    {C₁ C₂ : ℝ} {n : ℕ} (hC : C₁ ≤ C₂)
    (h : ResidueCanonicalAtSqrtInequality C₁ n) :
    ResidueCanonicalAtSqrtInequality C₂ n := by
  dsimp [ResidueCanonicalAtSqrtInequality] at h ⊢
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hfactor_nonneg :
      0 ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    goldbachResidueMainFactor_nonneg n (Nat.sqrt n)
  have hmul_n :
      C₁ * (n : ℝ) ≤ C₂ * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hC hn_nonneg
  have hmain :
      C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
        ≤ C₂ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) :=
    mul_le_mul_of_nonneg_right hmul_n hfactor_nonneg
  linarith

/-- The whole `Nat.sqrt n = 4` prefix of the corrected target is closed with
coefficient `3`, by the trivial count bound and the `1 / 3` local-factor
lower bound. -/
theorem residueCanonicalSqrtFourAtSqrt_three :
    ResidueCanonicalSqrtFourAtSqrt 3 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn hsqrt
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_third :
      (1 / 3 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) := by
    simpa [hsqrt] using one_third_le_goldbachResidueMainFactor_at_four n
  have hfactor_scaled :
      (1 : ℝ) ≤ 3 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (3 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (3 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (3 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-! ## Bridge from the large residual back to the corrected route -/

/-- A closed `sqrt n = 4` prefix and a `sqrt n ≥ 5` residual combine into the
fixed-constant corrected target, with the maximum of the two coefficients. -/
theorem residueCanonicalFixedConstantAtSqrt_of_sqrtFour_and_fromSqrtFive
    {C₄ C₅ : ℝ}
    (hFour : ResidueCanonicalSqrtFourAtSqrt C₄)
    (hFive : ResidueCanonicalFromSqrtFiveAtSqrt C₅) :
    ResidueCanonicalFixedConstantAtSqrt (max C₄ C₅) := by
  rcases hFour with ⟨hC₄_pos, hFourBd⟩
  rcases hFive with ⟨_hC₅_pos, hFiveBd⟩
  refine ⟨lt_of_lt_of_le hC₄_pos (le_max_left C₄ C₅), ?_⟩
  intro n hn
  have hsqrt_ge_four : 4 ≤ Nat.sqrt n := by
    refine Nat.le_sqrt.mpr ?_
    nlinarith
  by_cases hsqrt : Nat.sqrt n = 4
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left C₄ C₅) (hFourBd n hn hsqrt)
  · have hsqrt_ge_five : 5 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right C₄ C₅) (hFiveBd n hn hsqrt_ge_five)

/-- The only remaining finite-sieve worker target after the closed prefix is
the `sqrt n ≥ 5` residual. -/
theorem residueCanonicalWithConstant_of_fromSqrtFive
    (hFive : ResidueCanonicalFromSqrtFiveAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant := by
  rcases hFive with ⟨C₅, hFive⟩
  exact residueCanonicalWithConstant_of_fixed
    (residueCanonicalFixedConstantAtSqrt_of_sqrtFour_and_fromSqrtFive
      residueCanonicalSqrtFourAtSqrt_three hFive)

/-- Large-range residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtFive
    (hFive : ResidueCanonicalFromSqrtFiveAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalWithConstant
    (residueCanonicalWithConstant_of_fromSqrtFive hFive)

/-- Final Path C adapter after the closed prefix: the finite-sieve worker only
has to prove the `sqrt n ≥ 5` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtFive_and_countingInput
    (hFive : ResidueCanonicalFromSqrtFiveAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalWithConstant_and_countingInput
    (residueCanonicalWithConstant_of_fromSqrtFive hFive) hCounting

end PathCResidueCanonicalSqrtSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.one_third_le_goldbachResidueMainFactor_at_four
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.residueCanonicalAtSqrtInequality_mono
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.residueCanonicalSqrtFourAtSqrt_three
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.residueCanonicalFixedConstantAtSqrt_of_sqrtFour_and_fromSqrtFive
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.residueCanonicalWithConstant_of_fromSqrtFive
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.finiteSieveInput_of_residueCanonicalFromSqrtFive
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtFive_and_countingInput
