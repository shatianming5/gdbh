/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityFiberProduct

/-!
# Path C -- state-product handoff for signed union fibers

Round 15 reduced the active pointwise fiber target to a product of local
three-state factors.  This file splits that target into two smaller finite
algebra residuals:

* factor one ordered pair term into prime-local state factors;
* sum those factored pair terms over the fixed-union fiber and expand to the
  product of the one-prime state sums.

Both residuals are purely finite combinatorics; no analytic estimates or CRT
endpoint terms are introduced.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityStateProduct

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueFullLocalDensityUnionFiber
  (residueSignedPairTerm residueSignedUnionFiberSum)
open Gdbh.PathCResidueFullLocalDensityFiberProduct
  (ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation
   ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt
   residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_all
   residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
   residueDoubleDivisorFullLocalDensitySignedFiberEvaluationAtSqrt_of_product
   residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberProduct
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberProduct
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_fiberProduct
   residueSignedUnionPrimeFiberFactor)

/-! ## Pair-local state factors -/

/-- The state factor contributed by a prime for one ordered pair `(d₁, d₂)`.
It records the first-only, second-only, both-compatible, and absent states. -/
noncomputable def residueSignedPairPrimeStateFactor
    (n p : ℕ) (d₁ d₂ : Finset ℕ) : ℝ :=
  if p ∈ d₁ ∩ d₂ then
    if p ∣ n then 1 / (p : ℝ) else 0
  else if p ∈ d₁ then
    -(1 / (p : ℝ))
  else if p ∈ d₂ then
    -(1 / (p : ℝ))
  else
    1

/-- First smaller residual: a signed pair term factors into prime-local state
factors over the union of its two divisor sets. -/
def ResidueSignedPairTermPrimeStateFactorization : Prop :=
  ∀ n : ℕ, ∀ d₁ d₂ : Finset ℕ,
    residueSignedPairTerm n d₁ d₂ =
      ∏ p ∈ d₁ ∪ d₂, residueSignedPairPrimeStateFactor n p d₁ d₂

/-- Second smaller residual: after pairwise factorization, the fixed-union
fiber sum expands to the product of one-prime three-state sums. -/
def ResidueSignedUnionFiberStateProductExpansion : Prop :=
  ∀ n z : ℕ, ∀ u ∈ (residuePrimeSet z).powerset,
    (∑ pair ∈ ((residuePrimeSet z).powerset ×ˢ
        (residuePrimeSet z).powerset).filter
          (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
        ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2)
      = ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p

/-- At-sqrt version of the state-product expansion residual. -/
def ResidueSignedUnionFiberStateProductExpansionAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    ∀ u ∈ (residuePrimeSet (Nat.sqrt n)).powerset,
      (∑ pair ∈ ((residuePrimeSet (Nat.sqrt n)).powerset ×ˢ
          (residuePrimeSet (Nat.sqrt n)).powerset).filter
            (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
          ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2)
        = ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p

/-- The all-level state-product expansion residual implies its at-sqrt
specialization. -/
theorem residueSignedUnionFiberStateProductExpansionAtSqrt_of_all
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    ResidueSignedUnionFiberStateProductExpansionAtSqrt := by
  intro n _hn u hu
  exact hState n (Nat.sqrt n) u hu

/-! ## Bridges back to Round 15 -/

/-- Pairwise prime-state factorization plus fixed-union state expansion closes
the Round 15 product-form fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation := by
  intro n z u hu
  let P : Finset ℕ := residuePrimeSet z
  have hsum :
      residueSignedUnionFiberSum n P u =
        ∑ pair ∈ (P.powerset ×ˢ P.powerset).filter
            (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
          ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2 := by
    unfold residueSignedUnionFiberSum
    refine Finset.sum_congr rfl ?_
    intro pair hp
    have hUnion : pair.1 ∪ pair.2 = u := (Finset.mem_filter.mp hp).2
    rw [hPair n pair.1 pair.2, hUnion]
  rw [hsum]
  exact hState n z u hu

/-- At-sqrt pairwise prime-state factorization plus at-sqrt fixed-union state
expansion closes the at-sqrt product-form fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_pairState
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansionAtSqrt) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt := by
  intro n hn u hu
  let P : Finset ℕ := residuePrimeSet (Nat.sqrt n)
  have hsum :
      residueSignedUnionFiberSum n P u =
        ∑ pair ∈ (P.powerset ×ˢ P.powerset).filter
            (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
          ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2 := by
    unfold residueSignedUnionFiberSum
    refine Finset.sum_congr rfl ?_
    intro pair hp
    have hUnion : pair.1 ∪ pair.2 = u := (Finset.mem_filter.mp hp).2
    rw [hPair n pair.1 pair.2, hUnion]
  rw [hsum]
  exact hState n hn u hu

/-- All-level pairwise factorization and state expansion close the at-sqrt
product-form fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_pairState_all
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_all
    (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
      hPair hState)

/-- Pair-state residuals close the Round 14 fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_pairState
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensityUnionFiber.ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_product
    (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
      hPair hState)

/-- Pair-state residuals close the signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_pairState
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedUnionReduction :=
  residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_fiberProduct
    (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
      hPair hState)

/-- Pair-state residuals close the signed prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_pairState
    (hPair : ResidueSignedPairTermPrimeStateFactorization)
    (hState : ResidueSignedUnionFiberStateProductExpansion) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_fiberProduct
    (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
      hPair hState)

end PathCResidueFullLocalDensityStateProduct
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityStateProduct.residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_pairState
#print axioms
  Gdbh.PathCResidueFullLocalDensityStateProduct.residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_pairState
#print axioms
  Gdbh.PathCResidueFullLocalDensityStateProduct.residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_pairState
