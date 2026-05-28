/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueBonferroniKernelDecomposition
import Gdbh.PathC_ResidueCanonicalRefinedBridge

/-!
# Path C -- residue Bonferroni decomposition with a main coefficient

The earlier residue Bonferroni decomposition targeted the strict coefficient
`1` canonical kernel.  That shape is useful as a mechanical prototype, but it
is too narrow for the corrected route: small explicit cases already forced the
project to keep an honest main-term coefficient.

This file gives the coefficient-bearing version of the same closed
decomposition.  It peels off the residue indicator and Bonferroni layers, then
leaves only a smaller truncated double-divisor-sum estimate with an existential
main coefficient.  The result feeds the Round 43 refined finite-sieve target.
-/

set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueBonferroniConstantDecomposition

open scoped BigOperators

open Gdbh.PathCGoldbachResidues
  (GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound)
open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt residueBonferroniTailAtSqrtErrorBound_holds)
open Gdbh.PathCResidueBonferroniKernelDecomposition
  (residueDivisibilityIndicatorSum pairedTruncatedDivisorSum
   residuePairedBonferroniMajorant
   goldbachResidueSiftedCount_eq_divisibilityIndicatorSum
   residueDivisibilityIndicatorSum_le_pairedTruncatedDivisorSum)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant
   residueSiftedUpperBoundAtSqrtWithError_of_canonicalWithConstant)
open Gdbh.PathCResidueCanonicalRefinedBridge
  (finiteSieveInput_of_refinedAtSqrtWithErrorConstant
   pathC_kGoldbach_of_refinedAtSqrtWithErrorConstant_and_countingInput)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Coefficient-bearing Bonferroni worker Props -/

/-- Fixed-coefficient truncated divisor-sum residual at the canonical
at-sqrt depth. -/
noncomputable def ResidueBonferroniTruncatedSumFixedConstantAtSqrt
    (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      pairedTruncatedDivisorSum n (Nat.sqrt n) (canonicalK n)
        ≤ C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the truncated divisor-sum residual. -/
noncomputable def ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant :
    Prop :=
  ∃ C1 : ℝ, ResidueBonferroniTruncatedSumFixedConstantAtSqrt C1

/-- Fixed-coefficient double-sum residual after expanding the truncated
divisor-sum notation. -/
noncomputable def ResidueDoubleSumFixedConstantAtSqrt (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      (∑ m ∈ Finset.Icc 1 (n - 1),
          residuePairedBonferroniMajorant n (Nat.sqrt n) m)
        ≤ C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the explicit double-sum residual. -/
noncomputable def ResidueDoubleSumCanonicalAtSqrtBoundWithConstant : Prop :=
  ∃ C1 : ℝ, ResidueDoubleSumFixedConstantAtSqrt C1

/-! ## Closed notation and Bonferroni bridges -/

/-- The explicit double-sum residual is the coefficient-bearing truncated
sum residual. -/
theorem residueBonferroniTruncatedSumFixedConstantAtSqrt_of_doubleSumFixedConstant
    {C1 : ℝ} (h : ResidueDoubleSumFixedConstantAtSqrt C1) :
    ResidueBonferroniTruncatedSumFixedConstantAtSqrt C1 := by
  rcases h with ⟨hC1_pos, hbd⟩
  refine ⟨hC1_pos, ?_⟩
  intro n hn
  simpa [pairedTruncatedDivisorSum, residuePairedBonferroniMajorant] using
    hbd n hn

/-- The existential double-sum residual gives the existential truncated-sum
residual. -/
theorem residueBonferroniTruncatedSumWithConstant_of_doubleSumWithConstant
    (h : ResidueDoubleSumCanonicalAtSqrtBoundWithConstant) :
    ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant := by
  rcases h with ⟨C1, hC1⟩
  exact ⟨C1,
    residueBonferroniTruncatedSumFixedConstantAtSqrt_of_doubleSumFixedConstant
      hC1⟩

/-- The coefficient-bearing truncated-sum residual closes the corrected
canonical residue target. -/
theorem residueCanonicalWithConstant_of_truncatedSumWithConstant
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant := by
  rcases h with ⟨C1, hC1_pos, hbd⟩
  refine ⟨C1, hC1_pos, ?_⟩
  intro n hn
  have hk : Even (canonicalK n) := by
    unfold canonicalK
    exact even_two_mul n
  calc
    (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        = residueDivisibilityIndicatorSum n (Nat.sqrt n) :=
          goldbachResidueSiftedCount_eq_divisibilityIndicatorSum
            n (Nat.sqrt n)
    _ ≤ pairedTruncatedDivisorSum n (Nat.sqrt n) (canonicalK n) :=
          residueDivisibilityIndicatorSum_le_pairedTruncatedDivisorSum
            n (Nat.sqrt n) (canonicalK n) hk
    _ ≤ C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n) :=
          hbd n hn

/-- The coefficient-bearing double-sum residual closes the corrected
canonical residue target. -/
theorem residueCanonicalWithConstant_of_doubleSumWithConstant
    (h : ResidueDoubleSumCanonicalAtSqrtBoundWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_truncatedSumWithConstant
    (residueBonferroniTruncatedSumWithConstant_of_doubleSumWithConstant h)

/-! ## Bridges to the Round 43 refined finite-sieve target -/

/-- The coefficient-bearing truncated-sum residual supplies the Round 43
refined finite-sieve target. -/
theorem refinedAtSqrtWithErrorConstant_of_truncatedSumWithConstant
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant :=
  goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
    (residueSiftedUpperBoundAtSqrtWithError_of_canonicalWithConstant
      (residueCanonicalWithConstant_of_truncatedSumWithConstant h))
    residueBonferroniTailAtSqrtErrorBound_holds

/-- The coefficient-bearing double-sum residual supplies the Round 43 refined
finite-sieve target. -/
theorem refinedAtSqrtWithErrorConstant_of_doubleSumWithConstant
    (h : ResidueDoubleSumCanonicalAtSqrtBoundWithConstant) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant :=
  refinedAtSqrtWithErrorConstant_of_truncatedSumWithConstant
    (residueBonferroniTruncatedSumWithConstant_of_doubleSumWithConstant h)

/-- The coefficient-bearing truncated-sum residual supplies the supported
finite-sieve input. -/
theorem finiteSieveInput_of_residueTruncatedSumWithConstant
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_refinedAtSqrtWithErrorConstant
    (refinedAtSqrtWithErrorConstant_of_truncatedSumWithConstant h)

/-- The coefficient-bearing double-sum residual supplies the supported
finite-sieve input. -/
theorem finiteSieveInput_of_residueDoubleSumWithConstant
    (h : ResidueDoubleSumCanonicalAtSqrtBoundWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueTruncatedSumWithConstant
    (residueBonferroniTruncatedSumWithConstant_of_doubleSumWithConstant h)

/-- Final Path C adapter from the coefficient-bearing truncated-sum residual
and any supported counting input. -/
theorem pathC_kGoldbach_of_residueTruncatedSumWithConstant_and_countingInput
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_refinedAtSqrtWithErrorConstant_and_countingInput
    (refinedAtSqrtWithErrorConstant_of_truncatedSumWithConstant h)
    hCounting

/-- Final Path C adapter from the coefficient-bearing double-sum residual and
any supported counting input. -/
theorem pathC_kGoldbach_of_residueDoubleSumWithConstant_and_countingInput
    (h : ResidueDoubleSumCanonicalAtSqrtBoundWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueTruncatedSumWithConstant_and_countingInput
    (residueBonferroniTruncatedSumWithConstant_of_doubleSumWithConstant h)
    hCounting

end PathCResidueBonferroniConstantDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueBonferroniConstantDecomposition.residueBonferroniTruncatedSumFixedConstantAtSqrt_of_doubleSumFixedConstant
#print axioms
  Gdbh.PathCResidueBonferroniConstantDecomposition.residueCanonicalWithConstant_of_truncatedSumWithConstant
#print axioms
  Gdbh.PathCResidueBonferroniConstantDecomposition.refinedAtSqrtWithErrorConstant_of_truncatedSumWithConstant
#print axioms
  Gdbh.PathCResidueBonferroniConstantDecomposition.finiteSieveInput_of_residueDoubleSumWithConstant
#print axioms
  Gdbh.PathCResidueBonferroniConstantDecomposition.pathC_kGoldbach_of_residueDoubleSumWithConstant_and_countingInput
