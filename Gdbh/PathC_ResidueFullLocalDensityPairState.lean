/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityStateProduct

/-!
# Path C -- pair-state factorization

Round 16 isolated the pair-local state factorization residual.  This file
closes that residual by splitting it into the two strictly smaller local
cases: compatible overlaps and incompatible overlaps.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityPairState

open scoped BigOperators
open Finset

open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residuePairCompatibilityWeight)
open Gdbh.PathCResidueFullLocalDensityUnionFiber
  (residueSignedPairTerm)
open Gdbh.PathCResidueFullLocalDensityStateProduct
  (ResidueSignedPairTermPrimeStateFactorization
   ResidueSignedUnionFiberStateProductExpansion
   ResidueSignedUnionFiberStateProductExpansionAtSqrt
   residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_pairState
   residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
   residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_pairState
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_pairState
   residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_pairState
   residueSignedPairPrimeStateFactor)
open Gdbh.PathCResidueFullLocalDensityFiberProduct
  (ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation
   ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberProduct)

/-! ## Smaller pair-state residuals -/

/-- Compatible-overlap local case for one ordered pair.  If every prime in
`d₁ ∩ d₂` divides `n`, then the product of state factors is the expected
signed reciprocal of the union product. -/
def ResidueSignedPairTermPrimeStateCompatibleProduct : Prop :=
  ∀ n : ℕ, ∀ d₁ d₂ : Finset ℕ,
    (∀ p ∈ d₁ ∩ d₂, p ∣ n) →
      (∏ p ∈ d₁ ∪ d₂, residueSignedPairPrimeStateFactor n p d₁ d₂) =
        ((-1 : ℝ) ^ d₁.card) * ((-1 : ℝ) ^ d₂.card) *
          (1 / (((d₁ ∪ d₂).prod id : ℕ) : ℝ))

/-- Incompatible-overlap local case for one ordered pair.  If some prime in
`d₁ ∩ d₂` fails to divide `n`, then one local state factor is zero. -/
def ResidueSignedPairTermPrimeStateIncompatibleVanishing : Prop :=
  ∀ n : ℕ, ∀ d₁ d₂ : Finset ℕ,
    (¬ ∀ p ∈ d₁ ∩ d₂, p ∣ n) →
      (∏ p ∈ d₁ ∪ d₂, residueSignedPairPrimeStateFactor n p d₁ d₂) = 0

private lemma cast_prod_eq_prod_cast (u : Finset ℕ) :
    ((u.prod id : ℕ) : ℝ) = ∏ p ∈ u, (p : ℝ) := by
  classical
  have hprod_eq : (u.prod id : ℕ) = ∏ p ∈ u, (id p : ℕ) := rfl
  rw [hprod_eq, Nat.cast_prod]
  simp

private lemma stateFactor_eq_signed_reciprocal
    (n p : ℕ) (d₁ d₂ : Finset ℕ)
    (hcompat : ∀ q ∈ d₁ ∩ d₂, q ∣ n)
    (hpU : p ∈ d₁ ∪ d₂) :
    residueSignedPairPrimeStateFactor n p d₁ d₂ =
      ((if p ∈ d₁ then (-1 : ℝ) else 1) *
        (if p ∈ d₂ then (-1 : ℝ) else 1)) * (1 / (p : ℝ)) := by
  classical
  by_cases hp₁ : p ∈ d₁
  · by_cases hp₂ : p ∈ d₂
    · have hpI : p ∈ d₁ ∩ d₂ := Finset.mem_inter.mpr ⟨hp₁, hp₂⟩
      have hdiv : p ∣ n := hcompat p hpI
      simp [residueSignedPairPrimeStateFactor, hpI, hp₁, hp₂, hdiv]
    · have hpI : p ∉ d₁ ∩ d₂ := by
        intro h
        exact hp₂ (Finset.mem_inter.mp h).2
      simp [residueSignedPairPrimeStateFactor, hpI, hp₁, hp₂]
  · by_cases hp₂ : p ∈ d₂
    · have hpI : p ∉ d₁ ∩ d₂ := by
        intro h
        exact hp₁ (Finset.mem_inter.mp h).1
      simp [residueSignedPairPrimeStateFactor, hpI, hp₁, hp₂]
    · exact False.elim ((Finset.mem_union.mp hpU).elim hp₁ hp₂)

private lemma prod_left_membership_sign_union (d₁ d₂ : Finset ℕ) :
    (∏ p ∈ d₁ ∪ d₂, (if p ∈ d₁ then (-1 : ℝ) else 1)) =
      (-1 : ℝ) ^ d₁.card := by
  classical
  have hsub : d₁ ⊆ d₁ ∪ d₂ := Finset.subset_union_left
  calc
    (∏ p ∈ d₁ ∪ d₂, (if p ∈ d₁ then (-1 : ℝ) else 1))
        = ∏ p ∈ d₁, (if p ∈ d₁ then (-1 : ℝ) else 1) := by
          exact (Finset.prod_subset hsub (by
            intro p _hpU hpnot
            simp [hpnot])).symm
    _ = (-1 : ℝ) ^ d₁.card := by
      simp [Finset.prod_const]

private lemma prod_right_membership_sign_union (d₁ d₂ : Finset ℕ) :
    (∏ p ∈ d₁ ∪ d₂, (if p ∈ d₂ then (-1 : ℝ) else 1)) =
      (-1 : ℝ) ^ d₂.card := by
  classical
  have hsub : d₂ ⊆ d₁ ∪ d₂ := Finset.subset_union_right
  calc
    (∏ p ∈ d₁ ∪ d₂, (if p ∈ d₂ then (-1 : ℝ) else 1))
        = ∏ p ∈ d₂, (if p ∈ d₂ then (-1 : ℝ) else 1) := by
          exact (Finset.prod_subset hsub (by
            intro p _hpU hpnot
            simp [hpnot])).symm
    _ = (-1 : ℝ) ^ d₂.card := by
      simp [Finset.prod_const]

private lemma prod_reciprocal_eq_reciprocal_prod (u : Finset ℕ) :
    (∏ p ∈ u, (1 / (p : ℝ))) = 1 / (∏ p ∈ u, (p : ℝ)) := by
  classical
  rw [Finset.prod_div_distrib]
  simp

/-- The compatible-overlap case of pair-state factorization. -/
theorem residueSignedPairTermPrimeStateCompatibleProduct :
    ResidueSignedPairTermPrimeStateCompatibleProduct := by
  classical
  intro n d₁ d₂ hcompat
  let u : Finset ℕ := d₁ ∪ d₂
  let A : ℕ → ℝ := fun p => if p ∈ d₁ then (-1 : ℝ) else 1
  let B : ℕ → ℝ := fun p => if p ∈ d₂ then (-1 : ℝ) else 1
  let C : ℕ → ℝ := fun p => 1 / (p : ℝ)
  have hpoint :
      (∏ p ∈ u, residueSignedPairPrimeStateFactor n p d₁ d₂) =
        ∏ p ∈ u, (A p * B p) * C p := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    simpa [u, A, B, C] using
      stateFactor_eq_signed_reciprocal n p d₁ d₂ hcompat (by simpa [u] using hp)
  have hsplit :
      (∏ p ∈ u, (A p * B p) * C p) =
        (∏ p ∈ u, A p) * (∏ p ∈ u, B p) * (∏ p ∈ u, C p) := by
    calc
      (∏ p ∈ u, (A p * B p) * C p)
          = (∏ p ∈ u, A p * B p) * (∏ p ∈ u, C p) := by
            exact Finset.prod_mul_distrib
      _ = ((∏ p ∈ u, A p) * (∏ p ∈ u, B p)) * (∏ p ∈ u, C p) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ u, A p) * (∏ p ∈ u, B p) * (∏ p ∈ u, C p) := by
            ring
  have hA : (∏ p ∈ u, A p) = (-1 : ℝ) ^ d₁.card := by
    simp [u, A, prod_left_membership_sign_union d₁ d₂]
  have hB : (∏ p ∈ u, B p) = (-1 : ℝ) ^ d₂.card := by
    simp [u, B, prod_right_membership_sign_union d₁ d₂]
  have hC : (∏ p ∈ u, C p) = 1 / (((d₁ ∪ d₂).prod id : ℕ) : ℝ) := by
    have hrec := prod_reciprocal_eq_reciprocal_prod u
    have hcast := cast_prod_eq_prod_cast u
    rw [hrec, ← hcast]
  dsimp [u] at hpoint hsplit hA hB hC
  calc
    (∏ p ∈ d₁ ∪ d₂, residueSignedPairPrimeStateFactor n p d₁ d₂)
        = (∏ p ∈ d₁ ∪ d₂, (A p * B p) * C p) := hpoint
    _ = (∏ p ∈ d₁ ∪ d₂, A p) * (∏ p ∈ d₁ ∪ d₂, B p) *
          (∏ p ∈ d₁ ∪ d₂, C p) := hsplit
    _ = ((-1 : ℝ) ^ d₁.card) * ((-1 : ℝ) ^ d₂.card) *
          (1 / (((d₁ ∪ d₂).prod id : ℕ) : ℝ)) := by
        rw [hA, hB, hC]

/-- The incompatible-overlap case of pair-state factorization. -/
theorem residueSignedPairTermPrimeStateIncompatibleVanishing :
    ResidueSignedPairTermPrimeStateIncompatibleVanishing := by
  classical
  intro n d₁ d₂ hbad
  push Not at hbad
  rcases hbad with ⟨p, hp, hpndvd⟩
  have hp_union : p ∈ d₁ ∪ d₂ :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hp).1)
  exact Finset.prod_eq_zero hp_union (by
    simp [residueSignedPairPrimeStateFactor, hp, hpndvd])

/-- The two local cases close the original Round 16 pair-state residual. -/
theorem residueSignedPairTermPrimeStateFactorization_of_cases
    (hCompat : ResidueSignedPairTermPrimeStateCompatibleProduct)
    (hIncompat : ResidueSignedPairTermPrimeStateIncompatibleVanishing) :
    ResidueSignedPairTermPrimeStateFactorization := by
  classical
  intro n d₁ d₂
  unfold residueSignedPairTerm residuePairCompatibilityWeight
  by_cases hcompat : ∀ p ∈ d₁ ∩ d₂, p ∣ n
  · rw [if_pos hcompat, hCompat n d₁ d₂ hcompat]
  · rw [if_neg hcompat, hIncompat n d₁ d₂ hcompat]
    ring

/-- Closed pair-state factorization for one ordered pair. -/
theorem residueSignedPairTermPrimeStateFactorization :
    ResidueSignedPairTermPrimeStateFactorization :=
  residueSignedPairTermPrimeStateFactorization_of_cases
    residueSignedPairTermPrimeStateCompatibleProduct
    residueSignedPairTermPrimeStateIncompatibleVanishing

/-! ## Bridges with the closed pair-state factorization -/

/-- With pair-state factorization closed, only the fixed-union state-product
expansion is needed to close the product-form fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
    residueSignedPairTermPrimeStateFactorization hState

/-- At-sqrt version with the closed pair-state factorization. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansionAtSqrt) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_pairState
    residueSignedPairTermPrimeStateFactorization hState

/-- The remaining state expansion closes the Round 14 fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensityUnionFiber.ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_pairState
    residueSignedPairTermPrimeStateFactorization hState

/-- The remaining state expansion closes the signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedUnionReduction :=
  residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_pairState
    residueSignedPairTermPrimeStateFactorization hState

/-- The remaining state expansion closes the signed prime-factorization
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_pairState
    residueSignedPairTermPrimeStateFactorization hState

/-- At-sqrt signed prime-factorization bridge with closed pair states. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_stateExpansion
    (hState : ResidueSignedUnionFiberStateProductExpansionAtSqrt) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberProduct
    (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_stateExpansion
      hState)

end PathCResidueFullLocalDensityPairState
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityPairState.residueSignedPairTermPrimeStateFactorization
#print axioms
  Gdbh.PathCResidueFullLocalDensityPairState.residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_stateExpansion
#print axioms
  Gdbh.PathCResidueFullLocalDensityPairState.residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_stateExpansion
