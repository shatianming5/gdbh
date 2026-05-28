/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityEulerProduct

/-!
# Path C -- local prime factors for the full double density

`PathC_ResidueFullLocalDensityEulerProduct` reduces the active Euler side to
a product-form finite algebra identity.  This file splits that target once
more: the remaining global work is only to factor the full double powerset
sum into independent prime-local four-state factors.

For one prime, the four states are:

* absent from both divisor sets: `1`;
* present only in the first set: `-1 / p`;
* present only in the second set: `-1 / p`;
* present in both sets: `1 / p` exactly when the congruences are compatible,
  i.e. when `p ∣ n`, and `0` otherwise.

The local arithmetic closes here.  The remaining worker target is the global
finite product factorization of the double powerset sum into these local
factors.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityPrimeFactor

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueFullLocalDensityReduction
  (ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity
   ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt
   residueDoubleDivisorFullLocalDensitySum)
open Gdbh.PathCResidueFullLocalDensityEulerProduct
  (ResidueDoubleDivisorFullLocalDensityEulerProduct
   ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt
   residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_all
   residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_eulerProduct
   residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_eulerProduct)
open Gdbh.PathCLocalDensityEulerFactor (goldbachDensity)

/-! ## One-prime local factor -/

/-- The four-state local factor contributed by one prime in the full double
local-density expansion. -/
noncomputable def residueDoublePrimeLocalFactor (n p : ℕ) : ℝ :=
  (1 : ℝ) - (1 / (p : ℝ)) - (1 / (p : ℝ)) +
    if p ∣ n then 1 / (p : ℝ) else 0

/-- The one-prime four-state factor is exactly the Goldbach local density
factor. -/
theorem residueDoublePrimeLocalFactor_eq_goldbachDensityFactor
    (n p : ℕ) :
    residueDoublePrimeLocalFactor n p =
      (1 : ℝ) - goldbachDensity n p / (p : ℝ) := by
  by_cases hp : p ∣ n
  · simp [residueDoublePrimeLocalFactor, goldbachDensity, hp]
  · simp [residueDoublePrimeLocalFactor, goldbachDensity, hp]
    ring

/-! ## Global factorization residual -/

/-- Global finite-factorization residual for the full double local-density
sum.  This is strictly smaller than the product-form target: the local
four-state arithmetic has already been closed, so this asks only for the
double powerset sum to factor prime-by-prime. -/
def ResidueDoubleDivisorFullLocalDensityPrimeFactorization : Prop :=
  ∀ n z : ℕ,
    residueDoubleDivisorFullLocalDensitySum n z
      = ∏ p ∈ residuePrimeSet z, residueDoublePrimeLocalFactor n p

/-- At-sqrt version of the global factorization residual. -/
def ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorFullLocalDensitySum n (Nat.sqrt n)
      = ∏ p ∈ residuePrimeSet (Nat.sqrt n),
          residueDoublePrimeLocalFactor n p

/-- The all-level prime-factorization residual implies its at-sqrt
specialization. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_all
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt := by
  intro n _hn
  exact hFact n (Nat.sqrt n)

/-- Prime-factorization closes the product-form Euler residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerProduct_of_primeFactorization
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityEulerProduct := by
  intro n z
  rw [hFact n z]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact residueDoublePrimeLocalFactor_eq_goldbachDensityFactor n p

/-- At-sqrt prime-factorization closes the at-sqrt product-form Euler
residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_primeFactorization
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt) :
    ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt := by
  intro n hn
  rw [hFact n hn]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact residueDoublePrimeLocalFactor_eq_goldbachDensityFactor n p

/-- All-level prime-factorization closes the at-sqrt product-form Euler
residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_primeFactorization_all
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt :=
  residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensityEulerProduct_of_primeFactorization
      hFact)

/-- All-level prime-factorization closes the full local-density match. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_primeFactorization
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity :=
  residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_eulerProduct
    (residueDoubleDivisorFullLocalDensityEulerProduct_of_primeFactorization
      hFact)

/-- At-sqrt prime-factorization closes the at-sqrt full local-density match. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_primeFactorization
    (hFact : ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt :=
  residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_eulerProduct
    (residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_primeFactorization
      hFact)

end PathCResidueFullLocalDensityPrimeFactor
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoublePrimeLocalFactor_eq_goldbachDensityFactor
#print axioms
  Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityEulerProduct_of_primeFactorization
#print axioms
  Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_primeFactorization
