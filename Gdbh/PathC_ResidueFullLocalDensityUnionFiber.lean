/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensitySigned

/-!
# Path C -- signed union-fiber decomposition

Round 13 reduced the active Euler algebra target to the signed union
reduction: a double signed powerset sum should equal the single signed
Goldbach-density powerset sum.

This file performs the next mechanical decomposition.  It groups the double
sum by the union `u = d₁ ∪ d₂`.  The remaining residual is now pointwise in
each union fiber: evaluate the finite sum over all ordered pairs with fixed
union `u`.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityUnionFiber

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residuePairCompatibilityWeight)
open Gdbh.PathCResidueFullLocalDensitySigned
  (ResidueDoubleDivisorFullLocalDensitySignedUnionReduction
   ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_unionReduction
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_unionReduction
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_unionReduction_all
   residueDoubleDivisorFullLocalDensitySignedSum
   residueGoldbachDensitySignedMainSum)
open Gdbh.PathCLocalDensityEulerFactor (goldbachDensity)

/-! ## Union fibers -/

/-- The signed summand for one ordered pair of divisor subsets. -/
noncomputable def residueSignedPairTerm
    (n : ℕ) (d₁ d₂ : Finset ℕ) : ℝ :=
  ((-1 : ℝ) ^ d₁.card) * ((-1 : ℝ) ^ d₂.card) *
    residuePairCompatibilityWeight n d₁ d₂

/-- The fiber of the signed double sum over ordered pairs whose union is
the fixed set `u`.  The ambient set `P` records the original powerset domain. -/
noncomputable def residueSignedUnionFiberSum
    (n : ℕ) (P u : Finset ℕ) : ℝ :=
  ∑ pair ∈ (P.powerset ×ˢ P.powerset).filter
      (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
    residueSignedPairTerm n pair.1 pair.2

/-- The single signed term indexed by a fixed union set. -/
noncomputable def residueGoldbachDensitySignedFiberTerm
    (n : ℕ) (u : Finset ℕ) : ℝ :=
  ((-1 : ℝ) ^ u.card) *
    (∏ p ∈ u, goldbachDensity n p) / ((u.prod id : ℕ) : ℝ)

/-- The signed double sum grouped by union fibers. -/
theorem residueDoubleDivisorFullLocalDensitySignedSum_eq_unionFiberSum
    (n z : ℕ) :
    residueDoubleDivisorFullLocalDensitySignedSum n z =
      ∑ u ∈ (residuePrimeSet z).powerset,
        residueSignedUnionFiberSum n (residuePrimeSet z) u := by
  classical
  let P : Finset ℕ := residuePrimeSet z
  let pairSet : Finset (Finset ℕ × Finset ℕ) := P.powerset ×ˢ P.powerset
  let pairTerm : Finset ℕ × Finset ℕ → ℝ :=
    fun pair => residueSignedPairTerm n pair.1 pair.2
  have hmaps : ∀ pair ∈ pairSet, pair.1 ∪ pair.2 ∈ P.powerset := by
    intro pair hpair
    rcases Finset.mem_product.mp hpair with ⟨h₁, h₂⟩
    have h₁P : pair.1 ⊆ P := Finset.mem_powerset.mp h₁
    have h₂P : pair.2 ⊆ P := Finset.mem_powerset.mp h₂
    exact Finset.mem_powerset.mpr (Finset.union_subset h₁P h₂P)
  have hfiber :
      (∑ u ∈ P.powerset,
        ∑ pair ∈ pairSet.filter
            (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
          pairTerm pair)
        = ∑ pair ∈ pairSet, pairTerm pair := by
    simpa [pairSet, pairTerm] using
      (Finset.sum_fiberwise_of_maps_to
        (s := pairSet) (t := P.powerset)
        (g := fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2)
        hmaps pairTerm)
  unfold residueDoubleDivisorFullLocalDensitySignedSum
    residueSignedUnionFiberSum residueSignedPairTerm
  change
    (∑ d₁ ∈ P.powerset,
      ∑ d₂ ∈ P.powerset,
        ((-1 : ℝ) ^ d₁.card) * ((-1 : ℝ) ^ d₂.card) *
          residuePairCompatibilityWeight n d₁ d₂)
      =
        ∑ u ∈ P.powerset,
          ∑ pair ∈ pairSet.filter
            (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
            ((-1 : ℝ) ^ pair.1.card) * ((-1 : ℝ) ^ pair.2.card) *
              residuePairCompatibilityWeight n pair.1 pair.2
  rw [← Finset.sum_product']
  exact hfiber.symm

/-! ## Smaller residual and bridges -/

/-- Pointwise union-fiber residual.  For every union `u` appearing inside
the residue prime set, its ordered-pair fiber evaluates to the corresponding
single signed Goldbach-density term. -/
def ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation : Prop :=
  ∀ n z : ℕ, ∀ u ∈ (residuePrimeSet z).powerset,
    residueSignedUnionFiberSum n (residuePrimeSet z) u =
      residueGoldbachDensitySignedFiberTerm n u

/-- At-sqrt version of the union-fiber residual. -/
def ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    ∀ u ∈ (residuePrimeSet (Nat.sqrt n)).powerset,
      residueSignedUnionFiberSum n (residuePrimeSet (Nat.sqrt n)) u =
        residueGoldbachDensitySignedFiberTerm n u

/-- The all-level fiber residual implies its at-sqrt specialization. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_all
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt := by
  intro n _hn u hu
  exact hFiber n (Nat.sqrt n) u hu

/-- The pointwise union-fiber residual closes the signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberEvaluation
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedUnionReduction := by
  intro n z
  rw [residueDoubleDivisorFullLocalDensitySignedSum_eq_unionFiberSum]
  unfold residueGoldbachDensitySignedMainSum
  refine Finset.sum_congr rfl ?_
  intro u hu
  simpa [residueGoldbachDensitySignedFiberTerm] using hFiber n z u hu

/-- The at-sqrt pointwise union-fiber residual closes the at-sqrt signed
union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_fiberEvaluation
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt) :
    ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt := by
  intro n hn
  rw [residueDoubleDivisorFullLocalDensitySignedSum_eq_unionFiberSum]
  unfold residueGoldbachDensitySignedMainSum
  refine Finset.sum_congr rfl ?_
  intro u hu
  simpa [residueGoldbachDensitySignedFiberTerm] using hFiber n hn u hu

/-- The all-level union-fiber residual closes the at-sqrt signed union
reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_fiberEvaluation_all
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_fiberEvaluation
    (residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_all
      hFiber)

/-- The pointwise union-fiber residual closes the signed prime-factorization
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberEvaluation
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_unionReduction
    (residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberEvaluation
      hFiber)

/-- The at-sqrt pointwise union-fiber residual closes the at-sqrt signed
prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberEvaluation
    (hFiber : ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_unionReduction
    (residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_fiberEvaluation
      hFiber)

end PathCResidueFullLocalDensityUnionFiber
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityUnionFiber.residueDoubleDivisorFullLocalDensitySignedSum_eq_unionFiberSum
#print axioms
  Gdbh.PathCResidueFullLocalDensityUnionFiber.residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberEvaluation
#print axioms
  Gdbh.PathCResidueFullLocalDensityUnionFiber.residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberEvaluation
