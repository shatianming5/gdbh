/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityPrimeFactor
import Gdbh.PathC_MoebiusInversionRoute

/-!
# Path C -- signed full local-density handoff

The Round 12 residual asks for a global finite factorization of the full
double local-density sum.  This file peels off the Möbius-product layer:
because every divisor set is a subset of the odd-prime residue set, its
Möbius value is just the explicit sign `(-1)^card`.

The remaining residual is therefore a pure signed double-powerset
factorization, with no arithmetic-function evaluation left.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensitySigned

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition
  (residuePrimeSet residuePrimeSet_prime)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residuePairCompatibilityWeight)
open Gdbh.PathCResidueFullLocalDensityReduction
  (residueDoubleDivisorFullLocalDensitySum)
open Gdbh.PathCResidueFullLocalDensityPrimeFactor
  (ResidueDoubleDivisorFullLocalDensityPrimeFactorization
   ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt
   residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_all
   residueDoublePrimeLocalFactor
   residueDoublePrimeLocalFactor_eq_goldbachDensityFactor)
open Gdbh.PathCLocalDensityEulerFactor
  (goldbachDensity signedEulerProduct_general)

/-! ## Signed full double sum -/

/-- The full double local-density sum after evaluating the two Möbius factors
on squarefree products of distinct residue primes. -/
noncomputable def residueDoubleDivisorFullLocalDensitySignedSum
    (n z : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset,
    ∑ d₂ ∈ (residuePrimeSet z).powerset,
      ((-1 : ℝ) ^ d₁.card) * ((-1 : ℝ) ^ d₂.card) *
        residuePairCompatibilityWeight n d₁ d₂

/-- The original full double local-density sum is exactly the signed version.

This closes the arithmetic-function evaluation layer for the active Euler
factorization branch. -/
theorem residueDoubleDivisorFullLocalDensitySum_eq_signedSum
    (n z : ℕ) :
    residueDoubleDivisorFullLocalDensitySum n z =
      residueDoubleDivisorFullLocalDensitySignedSum n z := by
  classical
  unfold residueDoubleDivisorFullLocalDensitySum
    residueDoubleDivisorFullLocalDensitySignedSum
  refine Finset.sum_congr rfl ?_
  intro d₁ hd₁
  have hd₁_sub : d₁ ⊆ residuePrimeSet z := Finset.mem_powerset.mp hd₁
  have hd₁_primes : ∀ p ∈ d₁, Nat.Prime p :=
    fun p hp => residuePrimeSet_prime (hd₁_sub hp)
  have hμ₁ :
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) =
        (-1 : ℝ) ^ d₁.card := by
    simpa using
      Gdbh.PathCMoebiusInversionRoute.moebius_prod_distinct_primes
        hd₁_primes
  refine Finset.sum_congr rfl ?_
  intro d₂ hd₂
  have hd₂_sub : d₂ ⊆ residuePrimeSet z := Finset.mem_powerset.mp hd₂
  have hd₂_primes : ∀ p ∈ d₂, Nat.Prime p :=
    fun p hp => residuePrimeSet_prime (hd₂_sub hp)
  have hμ₂ :
      (ArithmeticFunction.moebius (d₂.prod id) : ℝ) =
        (-1 : ℝ) ^ d₂.card := by
    simpa using
      Gdbh.PathCMoebiusInversionRoute.moebius_prod_distinct_primes
        hd₂_primes
  rw [hμ₁, hμ₂]

/-! ## Smaller factorization residual -/

/-- Global finite-factorization residual after the Möbius layer has been
closed.  The remaining task is a pure signed double-powerset product
identity. -/
def ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization : Prop :=
  ∀ n z : ℕ,
    residueDoubleDivisorFullLocalDensitySignedSum n z
      = ∏ p ∈ residuePrimeSet z, residueDoublePrimeLocalFactor n p

/-- At-sqrt version of the signed global factorization residual. -/
def ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorFullLocalDensitySignedSum n (Nat.sqrt n)
      = ∏ p ∈ residuePrimeSet (Nat.sqrt n),
          residueDoublePrimeLocalFactor n p

/-- The all-level signed residual implies its at-sqrt specialization. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_all
    (hSigned : ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt := by
  intro n _hn
  exact hSigned n (Nat.sqrt n)

/-- The signed factorization residual closes the Round 12 prime-factor
residual. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorization_of_signed
    (hSigned : ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityPrimeFactorization := by
  intro n z
  rw [residueDoubleDivisorFullLocalDensitySum_eq_signedSum n z]
  exact hSigned n z

/-- The at-sqrt signed factorization residual closes the at-sqrt Round 12
prime-factor residual. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_signed
    (hSigned : ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt) :
    ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt := by
  intro n hn
  rw [residueDoubleDivisorFullLocalDensitySum_eq_signedSum n (Nat.sqrt n)]
  exact hSigned n hn

/-- The all-level signed residual also closes the at-sqrt Round 12
prime-factor residual. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_signed_all
    (hSigned : ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization) :
    ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensityPrimeFactorization_of_signed hSigned)

/-! ## Single signed-sum handoff -/

/-- The single signed Goldbach-density sum over the same residue prime set.

The remaining double-to-single task is to group the signed double sum by the
union of the two divisor sets and add the four local states at each prime. -/
noncomputable def residueGoldbachDensitySignedMainSum (n z : ℕ) : ℝ :=
  ∑ d ∈ (residuePrimeSet z).powerset,
    ((-1 : ℝ) ^ d.card) *
      (∏ p ∈ d, goldbachDensity n p) / ((d.prod id : ℕ) : ℝ)

/-- The single signed Goldbach-density sum is exactly the product of the
Round 12 local prime factors. -/
theorem residueGoldbachDensitySignedMainSum_eq_primeFactorProduct
    (n z : ℕ) :
    residueGoldbachDensitySignedMainSum n z =
      ∏ p ∈ residuePrimeSet z, residueDoublePrimeLocalFactor n p := by
  classical
  unfold residueGoldbachDensitySignedMainSum
  rw [← signedEulerProduct_general (residuePrimeSet z) (goldbachDensity n)]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact (residueDoublePrimeLocalFactor_eq_goldbachDensityFactor n p).symm

/-- Remaining signed union-reduction residual: the double signed sum equals
the single signed Goldbach-density sum. -/
def ResidueDoubleDivisorFullLocalDensitySignedUnionReduction : Prop :=
  ∀ n z : ℕ,
    residueDoubleDivisorFullLocalDensitySignedSum n z =
      residueGoldbachDensitySignedMainSum n z

/-- At-sqrt version of the signed union-reduction residual. -/
def ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorFullLocalDensitySignedSum n (Nat.sqrt n) =
      residueGoldbachDensitySignedMainSum n (Nat.sqrt n)

/-- The all-level signed union-reduction residual implies its at-sqrt
specialization. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt_of_all
    (hUnion : ResidueDoubleDivisorFullLocalDensitySignedUnionReduction) :
    ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt := by
  intro n _hn
  exact hUnion n (Nat.sqrt n)

/-- The signed union-reduction residual closes the signed prime-factorization
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_unionReduction
    (hUnion : ResidueDoubleDivisorFullLocalDensitySignedUnionReduction) :
    ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization := by
  intro n z
  rw [hUnion n z, residueGoldbachDensitySignedMainSum_eq_primeFactorProduct]

/-- The at-sqrt signed union-reduction residual closes the at-sqrt signed
prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_unionReduction
    (hUnion : ResidueDoubleDivisorFullLocalDensitySignedUnionReductionAtSqrt) :
    ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt := by
  intro n hn
  rw [hUnion n hn, residueGoldbachDensitySignedMainSum_eq_primeFactorProduct]

/-- The all-level signed union-reduction residual closes the at-sqrt signed
prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_unionReduction_all
    (hUnion : ResidueDoubleDivisorFullLocalDensitySignedUnionReduction) :
    ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_unionReduction
      hUnion)

end PathCResidueFullLocalDensitySigned
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensitySum_eq_signedSum
#print axioms
  Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensityPrimeFactorization_of_signed
#print axioms
  Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_signed
#print axioms
  Gdbh.PathCResidueFullLocalDensitySigned.residueGoldbachDensitySignedMainSum_eq_primeFactorProduct
#print axioms
  Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_unionReduction
