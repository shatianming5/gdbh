/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit

/-!
# Path C -- corrected residue canonical parametric coarse split

Round 39 introduced a uniform coarse product lower bound that closes every
finite `z ≤ N` block with the finite constant `(3 : ℝ)^N`.  This file turns
that into a reusable parameterized residual: for any natural `N`, the active
`sqrt n ≥ 10001` worker target is reduced to the strictly later residual
`sqrt n ≥ N + 1`.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalParametricCoarseSplit

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
  (crudeResidueFactor)
open Gdbh.PathCResidueCanonicalSqrtSevenHundredTwentySixToTenThousandSplit
  (ResidueCanonicalFromSqrtTenThousandOneAtSqrt
   ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtTenThousandOne
   one_third_pow_bound_le_crudeResidueFactorProduct
   pathC_kGoldbach_of_residueCanonicalFromSqrtTenThousandOne_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtTenThousandOne)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Parameterized residuals -/

/-- Closed finite block from the active `sqrt n ≥ 10001` threshold up to an
arbitrary bound `N`. -/
def ResidueCanonicalSqrtTenThousandOneToAtMostAtSqrt (N : ℕ) (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 10001 ≤ Nat.sqrt n → Nat.sqrt n ≤ N →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the finite block
up to `N`: `N + 1 ≤ Nat.sqrt n`. -/
def ResidueCanonicalFromSqrtAfterAtSqrt (N : ℕ) (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the parameterized `sqrt n ≥ N + 1` residual. -/
def ResidueCanonicalFromSqrtAfterAtSqrtWithConstant (N : ℕ) : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtAfterAtSqrt N C₁

/-! ## Generic coarse lower bound and finite block -/

/-- Uniform coarse lower bound for the residue main factor through any finite
upper bound `N`. -/
theorem one_third_pow_N_le_goldbachResidueMainFactor_of_le
    (N n z : ℕ) (hzN : z ≤ N) :
    (1 / 3 : ℝ) ^ N ≤ goldbachResidueMainFactor n z := by
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
  have hcard : Pz.card ≤ N := hcard_le_z.trans hzN
  have hcrude_z :
      (1 / 3 : ℝ) ^ N ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_third_pow_bound_le_crudeResidueFactorProduct hcard h3_z
  have hactual :
      (∏ p ∈ Pz, crudeResidueFactor p) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
    simpa [crudeResidueFactor] using
      residueFactorProduct_lower_two_of_three_le n Pz h3_z
  have hmain :
      (1 / 3 : ℝ) ^ N ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
    hcrude_z.trans hactual
  simpa [goldbachResidueMainFactor, Pz] using hmain

/-- Every finite block `10001 ≤ Nat.sqrt n ≤ N` is closed with the explicit
finite coarse constant `(3 : ℝ)^N`. -/
theorem residueCanonicalSqrtTenThousandOneToAtMostAtSqrt_three_pow
    (N : ℕ) :
    ResidueCanonicalSqrtTenThousandOneToAtMostAtSqrt N ((3 : ℝ) ^ N) := by
  refine ⟨by positivity, ?_⟩
  intro n _hn _hsqrt_ge_ten_thousand_one hsqrt_le_N
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_lower :
      (1 / 3 : ℝ) ^ N ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_third_pow_N_le_goldbachResidueMainFactor_of_le
      N n (Nat.sqrt n) hsqrt_le_N
  have hfactor_scaled :
      (1 : ℝ) ≤
        (3 : ℝ) ^ N * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ N := by positivity
    have hmul := mul_le_mul_of_nonneg_left hfactor_lower hnonneg
    calc
      (1 : ℝ) = (3 : ℝ) ^ N * (1 / 3 : ℝ) ^ N := by
        rw [← mul_pow]
        norm_num
      _ ≤ (3 : ℝ) ^ N * goldbachResidueMainFactor n (Nat.sqrt n) := hmul
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        ((3 : ℝ) ^ N) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (((3 : ℝ) ^ N) *
            goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = ((3 : ℝ) ^ N) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ac_rfl
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-! ## Bridges back to the active corrected route -/

/-- A closed block through `N` and a residual after `N` combine into the active
Round 39 residual `sqrt n ≥ 10001`. -/
theorem residueCanonicalFromSqrtTenThousandOneAtSqrt_of_parametric_after
    {N : ℕ} {Cafter : ℝ}
    (hAfter : ResidueCanonicalFromSqrtAfterAtSqrt N Cafter) :
    ResidueCanonicalFromSqrtTenThousandOneAtSqrt
      (max ((3 : ℝ) ^ N) Cafter) := by
  have hBlock := residueCanonicalSqrtTenThousandOneToAtMostAtSqrt_three_pow N
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hAfter with ⟨_hCafter_pos, hAfterBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left ((3 : ℝ) ^ N) Cafter), ?_⟩
  intro n hn hsqrt_ge_ten_thousand_one
  by_cases hsqrt_le_N : Nat.sqrt n ≤ N
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left ((3 : ℝ) ^ N) Cafter)
      (hBlockBd n hn hsqrt_ge_ten_thousand_one hsqrt_le_N)
  · have hsqrt_ge_after : N + 1 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right ((3 : ℝ) ^ N) Cafter)
      (hAfterBd n hn hsqrt_ge_after)

/-- For any finite upper bound `N`, the active `sqrt n ≥ 10001` residual is
reduced to the later residual `sqrt n ≥ N + 1`. -/
theorem residueCanonicalFromSqrtTenThousandOneWithConstant_of_parametric_after
    (N : ℕ) (hAfter : ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N) :
    ResidueCanonicalFromSqrtTenThousandOneAtSqrtWithConstant := by
  rcases hAfter with ⟨Cafter, hAfter⟩
  exact ⟨max ((3 : ℝ) ^ N) Cafter,
    residueCanonicalFromSqrtTenThousandOneAtSqrt_of_parametric_after hAfter⟩

/-- Parameterized residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_parametric_after
    (N : ℕ) (hAfter : ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtTenThousandOne
    (residueCanonicalFromSqrtTenThousandOneWithConstant_of_parametric_after
      N hAfter)

/-- Parameterized residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtAfter
    (N : ℕ) (hAfter : ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtTenThousandOne
    (residueCanonicalFromSqrtTenThousandOneWithConstant_of_parametric_after
      N hAfter)

/-- Final Path C adapter after the parameterized coarse split. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput
    (N : ℕ) (hAfter : ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtTenThousandOne_and_countingInput
    (residueCanonicalFromSqrtTenThousandOneWithConstant_of_parametric_after
      N hAfter)
    hCounting

end PathCResidueCanonicalParametricCoarseSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.one_third_pow_N_le_goldbachResidueMainFactor_of_le
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.residueCanonicalSqrtTenThousandOneToAtMostAtSqrt_three_pow
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.residueCanonicalFromSqrtTenThousandOneAtSqrt_of_parametric_after
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.residueCanonicalFromSqrtTenThousandOneWithConstant_of_parametric_after
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.residueCanonicalWithConstant_of_parametric_after
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.finiteSieveInput_of_residueCanonicalFromSqrtAfter
#print axioms
  Gdbh.PathCResidueCanonicalParametricCoarseSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput
