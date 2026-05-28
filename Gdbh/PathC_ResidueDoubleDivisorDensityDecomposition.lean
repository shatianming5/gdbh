/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex
-/
import Gdbh.PathC_ResidueDoubleSumDecomposition
import Gdbh.PathC_LocalDensityEulerFactor

/-!
# Path C -- residue double-divisor density decomposition

`PathC_ResidueDoubleSumDecomposition` reduces the strict residue kernel to
`ResidueDoubleDivisorCanonicalAtSqrtBound`, an explicit double-divisor
counting estimate.

This file peels off the next honest layer without taking the known bad
CRT-error route.  The remaining count is compared to a local-density sum,
and the local-density algebra is separated from the exact counting problem.

The new residuals are:

* `ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound`: replace each
  finite interval count by its exact local-density main term, with the
  existing canonical tail left as the only reservoir.
* `ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt`: identify
  that double local-density sum with the already-closed Goldbach density
  powerset sum.

The existing Euler-product theorem then rewrites the Goldbach density sum
to `goldbachResidueMainFactor`.
-/

namespace Gdbh
namespace PathCResidueDoubleDivisorDensityDecomposition

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleSumDecomposition
  (ResidueDoubleDivisorCanonicalAtSqrtBound residueDoubleDivisorCountingSumAtSqrt)
open Gdbh.PathCGoldbachResidues
  (goldbachResidueMainFactor goldbachResidueMainFactor_eq_goldbachLocalFactor)
open Gdbh.PathCLocalDensityEulerFactor
  (goldbachDensity goldbachPrimeSet moebiusEulerProduct_goldbach)

/-! ## Closed single-sum local-density layer -/

/-- The existing Goldbach local-density powerset sum, exposed under the
residue double-divisor namespace for the current worker target. -/
noncomputable def residueGoldbachDensityMainSum (n z : ℕ) : ℝ :=
  ∑ d ∈ (goldbachPrimeSet z).powerset,
    (ArithmeticFunction.moebius (d.prod id) : ℝ) *
      (∏ p ∈ d, goldbachDensity n p) / ((d.prod id : ℕ) : ℝ)

/-- The single-sum local-density expansion is exactly the residue main
factor used by the strict canonical kernel. -/
theorem residueGoldbachDensityMainSum_eq_residueMainFactor (n z : ℕ) :
    residueGoldbachDensityMainSum n z = goldbachResidueMainFactor n z := by
  rw [goldbachResidueMainFactor_eq_goldbachLocalFactor]
  exact (moebiusEulerProduct_goldbach n z).symm

/-! ## Double local-density layer -/

/-- Local compatibility density for one ordered pair of squarefree divisor
sets.  A prime in the overlap imposes compatible congruences only when it
divides `n`; otherwise that pair contributes no local main term. -/
noncomputable def residuePairCompatibilityWeight
    (n : ℕ) (d₁ d₂ : Finset ℕ) : ℝ :=
  if ∀ p ∈ d₁ ∩ d₂, p ∣ n then
    (1 : ℝ) / (((d₁ ∪ d₂).prod id : ℕ) : ℝ)
  else
    0

/-- The double local-density main sum naturally attached to the explicit
double-divisor counting sum. -/
noncomputable def residueDoubleDivisorLocalDensitySum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        residuePairCompatibilityWeight n d₁ d₂

/-- The final-threshold, canonical-depth double local-density main sum. -/
noncomputable def residueDoubleDivisorLocalDensitySumAtSqrt (n : ℕ) : ℝ :=
  residueDoubleDivisorLocalDensitySum n (Nat.sqrt n) (canonicalK n)

/-! ## Smaller residuals -/

/-- Exact-count-to-local-density residual.

This is the CRT/counting task stripped of Euler-product algebra.  It avoids
the false route of summing absolute plus-or-minus-one CRT errors at depth `2n`; the
comparison is directly to the compatible local-density main term. -/
def ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCountingSumAtSqrt n
      ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Double-density algebra residual: identify the double local-density sum
with the already-closed Goldbach density powerset sum. -/
def ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorLocalDensitySumAtSqrt n
      = residueGoldbachDensityMainSum n (Nat.sqrt n)

/-- Local-density Euler residual in the exact RHS shape used by the parent
double-divisor target. -/
def ResidueDoubleDivisorLocalDensityEulerAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorLocalDensitySumAtSqrt n
      = goldbachResidueMainFactor n (Nat.sqrt n)

/-- Count-to-Goldbach-density residual.  This is an alternative handoff for
a worker that bypasses the double local-density notation and proves the
comparison directly against the closed powerset expansion. -/
def ResidueDoubleDivisorCountToGoldbachDensityMainAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCountingSumAtSqrt n
      ≤ (n : ℝ) * residueGoldbachDensityMainSum n (Nat.sqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-! ## Bridges back to the parent residual -/

/-- Matching the double local-density sum to the Goldbach density expansion
closes the local-density Euler residual, since the latter expansion is
already identified with `goldbachResidueMainFactor`. -/
theorem residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch
    (hMatch : ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorLocalDensityEulerAtSqrt := by
  intro n hn
  rw [hMatch n hn, residueGoldbachDensityMainSum_eq_residueMainFactor]

/-- The exact count-to-density residual plus the local-density Euler residual
imply the previous explicit double-divisor target. -/
theorem residueDoubleDivisorCanonicalAtSqrtBound_of_localDensity
    (hCount : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound)
    (hEuler : ResidueDoubleDivisorLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCanonicalAtSqrtBound := by
  intro n hn
  have h := hCount n hn
  rw [hEuler n hn] at h
  exact h

/-- Equivalent two-piece bridge using the more primitive match against the
Goldbach density powerset expansion. -/
theorem residueDoubleDivisorCanonicalAtSqrtBound_of_exactCountAndGoldbachDensityMatch
    (hCount : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound)
    (hMatch : ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorCanonicalAtSqrtBound :=
  residueDoubleDivisorCanonicalAtSqrtBound_of_localDensity hCount
    (residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch hMatch)

/-- Direct bridge for a worker proving the count estimate against the
already-closed single-sum Goldbach density expansion. -/
theorem residueDoubleDivisorCanonicalAtSqrtBound_of_goldbachDensityMain
    (hCount : ResidueDoubleDivisorCountToGoldbachDensityMainAtSqrtBound) :
    ResidueDoubleDivisorCanonicalAtSqrtBound := by
  intro n hn
  have h := hCount n hn
  rw [residueGoldbachDensityMainSum_eq_residueMainFactor] at h
  exact h

end PathCResidueDoubleDivisorDensityDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueDoubleDivisorDensityDecomposition.residueGoldbachDensityMainSum_eq_residueMainFactor
#print axioms
  Gdbh.PathCResidueDoubleDivisorDensityDecomposition.residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch
#print axioms
  Gdbh.PathCResidueDoubleDivisorDensityDecomposition.residueDoubleDivisorCanonicalAtSqrtBound_of_localDensity
#print axioms
  Gdbh.PathCResidueDoubleDivisorDensityDecomposition.residueDoubleDivisorCanonicalAtSqrtBound_of_exactCountAndGoldbachDensityMatch
#print axioms
  Gdbh.PathCResidueDoubleDivisorDensityDecomposition.residueDoubleDivisorCanonicalAtSqrtBound_of_goldbachDensityMain
