/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityUnionFiber

/-!
# Path C -- local products for signed union fibers

Round 14 reduced the signed union target to a pointwise fiber evaluation.
For a fixed union `u`, every prime in `u` has three possible states:
first-only, second-only, or both.  This file closes the local arithmetic
attached to those three states and rewrites the target fiber term as a product
of the corresponding one-prime factors.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityFiberProduct

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueFullLocalDensityUnionFiber
  (ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation
   ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt
   residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_all
   residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberEvaluation
   residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_fiberEvaluation
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberEvaluation
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberEvaluation
   residueGoldbachDensitySignedFiberTerm
   residueSignedUnionFiberSum)
open Gdbh.PathCLocalDensityEulerFactor (goldbachDensity)

/-! ## One-prime fiber factor -/

/-- The local factor for one prime inside a fixed union fiber: first-only,
second-only, and both-if-compatible. -/
noncomputable def residueSignedUnionPrimeFiberFactor (n p : ℕ) : ℝ :=
  -(1 / (p : ℝ)) - (1 / (p : ℝ)) +
    if p ∣ n then 1 / (p : ℝ) else 0

/-- The three-state local fiber factor is the negative Goldbach density
divided by the prime. -/
theorem residueSignedUnionPrimeFiberFactor_eq_neg_density_div
    (n p : ℕ) :
    residueSignedUnionPrimeFiberFactor n p =
      -(goldbachDensity n p / (p : ℝ)) := by
  by_cases hp : p ∣ n
  · rw [residueSignedUnionPrimeFiberFactor,
      Gdbh.PathCLocalDensityEulerFactor.goldbachDensity_of_dvd hp]
    simp [hp]
  · rw [residueSignedUnionPrimeFiberFactor,
      Gdbh.PathCLocalDensityEulerFactor.goldbachDensity_of_not_dvd hp]
    simp [hp]
    ring

private lemma cast_prod_eq_prod_cast (u : Finset ℕ) :
    ((u.prod id : ℕ) : ℝ) = ∏ p ∈ u, (p : ℝ) := by
  classical
  have hprod_eq : (u.prod id : ℕ) = ∏ p ∈ u, (id p : ℕ) := rfl
  rw [hprod_eq, Nat.cast_prod]
  simp

/-- The single signed fiber term is the product of the one-prime fiber
factors over its union set. -/
theorem residueGoldbachDensitySignedFiberTerm_eq_primeFiberProduct
    (n : ℕ) (u : Finset ℕ) :
    residueGoldbachDensitySignedFiberTerm n u =
      ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p := by
  classical
  unfold residueGoldbachDensitySignedFiberTerm
  have hneg :
      (∏ p ∈ u, (-(goldbachDensity n p / (p : ℝ))))
        = (-1 : ℝ) ^ u.card *
          ∏ p ∈ u, (goldbachDensity n p / (p : ℝ)) := by
    simpa using
      (Finset.prod_neg (s := u)
        (f := fun p : ℕ => goldbachDensity n p / (p : ℝ)))
  have hsplit :
      (∏ p ∈ u, (goldbachDensity n p / (p : ℝ)))
        = (∏ p ∈ u, goldbachDensity n p) / (∏ p ∈ u, (p : ℝ)) :=
    Finset.prod_div_distrib
      (s := u) (f := fun p => goldbachDensity n p)
      (g := fun p => (p : ℝ))
  have hcast : (∏ p ∈ u, (p : ℝ)) = ((u.prod id : ℕ) : ℝ) :=
    (cast_prod_eq_prod_cast u).symm
  calc
    ((-1 : ℝ) ^ u.card) *
        (∏ p ∈ u, goldbachDensity n p) / ((u.prod id : ℕ) : ℝ)
        = (-1 : ℝ) ^ u.card *
            ((∏ p ∈ u, goldbachDensity n p) /
              ((u.prod id : ℕ) : ℝ)) := by ring
    _ = (-1 : ℝ) ^ u.card *
          (∏ p ∈ u, (goldbachDensity n p / (p : ℝ))) := by
      rw [hsplit, hcast]
    _ = ∏ p ∈ u, (-(goldbachDensity n p / (p : ℝ))) := hneg.symm
    _ = ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p := by
      refine Finset.prod_congr rfl ?_
      intro p _hp
      exact (residueSignedUnionPrimeFiberFactor_eq_neg_density_div n p).symm

/-! ## Product-form fiber residual -/

/-- Product-form version of the pointwise union-fiber residual. -/
def ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation : Prop :=
  ∀ n z : ℕ, ∀ u ∈ (residuePrimeSet z).powerset,
    residueSignedUnionFiberSum n (residuePrimeSet z) u =
      ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p

/-- At-sqrt product-form version of the pointwise union-fiber residual. -/
def ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    ∀ u ∈ (residuePrimeSet (Nat.sqrt n)).powerset,
      residueSignedUnionFiberSum n (residuePrimeSet (Nat.sqrt n)) u =
        ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p

/-- The all-level product-form fiber residual implies its at-sqrt
specialization. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_all
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt := by
  intro n _hn u hu
  exact hProd n (Nat.sqrt n) u hu

/-- The product-form fiber residual closes the Round 14 fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation := by
  intro n z u hu
  rw [residueGoldbachDensitySignedFiberTerm_eq_primeFiberProduct]
  exact hProd n z u hu

/-- The at-sqrt product-form fiber residual closes the at-sqrt Round 14
fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_product
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt := by
  intro n hn u hu
  rw [residueGoldbachDensitySignedFiberTerm_eq_primeFiberProduct]
  exact hProd n hn u hu

/-- The all-level product-form fiber residual closes the at-sqrt Round 14
fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_product_all
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product hProd)

/-- The product-form fiber residual closes the signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberProduct
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedUnionReduction :=
  residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberEvaluation
    (residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
      hProd)

/-- The product-form fiber residual closes the signed prime-factorization
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberProduct
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberEvaluation
    (residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
      hProd)

/-- The at-sqrt product-form fiber residual closes the at-sqrt signed
prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberProduct
    (hProd : ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberEvaluation
    (residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_product
      hProd)

end PathCResidueFullLocalDensityFiberProduct
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityFiberProduct.residueSignedUnionPrimeFiberFactor_eq_neg_density_div
#print axioms
  Gdbh.PathCResidueFullLocalDensityFiberProduct.residueGoldbachDensitySignedFiberTerm_eq_primeFiberProduct
#print axioms
  Gdbh.PathCResidueFullLocalDensityFiberProduct.residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
