/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityReduction
import Gdbh.PathC_LocalDensityEulerFactor

/-!
# Path C -- full local-density Euler-product handoff

`PathC_ResidueFullLocalDensityReduction` leaves a pure finite algebraic
identity: the full double local-density expansion should match the existing
single Goldbach-density powerset expansion.

This file exposes the next smaller worker target.  It asks only for the full
double expansion to equal the product of local Goldbach factors.  The bridge
from that product to the existing powerset sum is already closed by
`PathC_LocalDensityEulerFactor.moebiusEulerProduct_goldbach`.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityEulerProduct

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueFullLocalDensityReduction
  (ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity
   ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt
   residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_all
   residueDoubleDivisorFullLocalDensitySum)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueGoldbachDensityMainSum)
open Gdbh.PathCLocalDensityEulerFactor
  (goldbachDensity goldbachLocalFactor_eq_prod_density goldbachPrimeSet
   moebiusEulerProduct_goldbach)

/-- Product-form worker target for the full double local-density expansion. -/
def ResidueDoubleDivisorFullLocalDensityEulerProduct : Prop :=
  ∀ n z : ℕ,
    residueDoubleDivisorFullLocalDensitySum n z
      = ∏ p ∈ residuePrimeSet z, ((1 : ℝ) - goldbachDensity n p / (p : ℝ))

/-- At-sqrt product-form worker target. -/
def ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorFullLocalDensitySum n (Nat.sqrt n)
      = ∏ p ∈ residuePrimeSet (Nat.sqrt n),
          ((1 : ℝ) - goldbachDensity n p / (p : ℝ))

/-- The all-level product-form target implies its at-sqrt specialization. -/
theorem residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_all
    (hProd : ResidueDoubleDivisorFullLocalDensityEulerProduct) :
    ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt := by
  intro n _hn
  exact hProd n (Nat.sqrt n)

/-- The Goldbach-density powerset sum is the same as the local Euler product
over the residue prime set. -/
theorem residueGoldbachDensityMainSum_eq_localEulerProduct
    (n z : ℕ) :
    residueGoldbachDensityMainSum n z =
      ∏ p ∈ residuePrimeSet z, ((1 : ℝ) - goldbachDensity n p / (p : ℝ)) := by
  classical
  rw [residueGoldbachDensityMainSum]
  rw [← moebiusEulerProduct_goldbach n z]
  rw [goldbachLocalFactor_eq_prod_density n z]
  simp [residuePrimeSet, goldbachPrimeSet]

/-- The product-form worker target closes the full-depth local-density
algebra residual. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_eulerProduct
    (hProd : ResidueDoubleDivisorFullLocalDensityEulerProduct) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity := by
  intro n z
  rw [hProd n z, residueGoldbachDensityMainSum_eq_localEulerProduct]

/-- The at-sqrt product-form worker target closes the at-sqrt full-depth
local-density algebra residual. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_eulerProduct
    (hProd : ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt := by
  intro n hn
  rw [hProd n hn, residueGoldbachDensityMainSum_eq_localEulerProduct]

/-- The all-level product-form target also closes the at-sqrt residual. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_eulerProduct_all
    (hProd : ResidueDoubleDivisorFullLocalDensityEulerProduct) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt :=
  residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_eulerProduct
      hProd)

end PathCResidueFullLocalDensityEulerProduct
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityEulerProduct.residueGoldbachDensityMainSum_eq_localEulerProduct
#print axioms
  Gdbh.PathCResidueFullLocalDensityEulerProduct.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_eulerProduct
#print axioms
  Gdbh.PathCResidueFullLocalDensityEulerProduct.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_eulerProduct
