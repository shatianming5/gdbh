/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueBonferroniConstantDecomposition
import Gdbh.PathC_ResidueDoubleDivisorCoprimeSplit

/-!
# Path C -- coefficient-bearing residue double-divisor decomposition

Round 44 reduced the active finite-sieve worker to a coefficient-bearing
double sum of Bonferroni majorants.  This file peels off the next two closed
layers while preserving that coefficient:

* the rearrangement from the `m`-sum of Bonferroni majorants to the explicit
  double-divisor counting sum;
* the partition of that explicit double-divisor count into coprime and
  shared-prime-overlap divisor-product parts.

The new residual keeps the corrected coefficient-bearing shape instead of
using the older strict coefficient-`1` double-divisor target as the active
worker.
-/

set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueDoubleDivisorConstantDecomposition

open scoped BigOperators

open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniConstantDecomposition
  (ResidueDoubleSumFixedConstantAtSqrt
   ResidueDoubleSumCanonicalAtSqrtBoundWithConstant
   finiteSieveInput_of_residueDoubleSumWithConstant
   pathC_kGoldbach_of_residueDoubleSumWithConstant_and_countingInput)
open Gdbh.PathCResidueDoubleSumDecomposition
  (residueDoubleDivisorCountingSumAtSqrt
   residueMajorantSumAtSqrt_eq_doubleDivisorCountingSumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorCoprimeSplit
  (residueDoubleDivisorCoprimeCountingSumAtSqrt
   residueDoubleDivisorNonCoprimeCountingSumAtSqrt
   residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Coefficient-bearing explicit double-divisor residuals -/

/-- Fixed-coefficient explicit double-divisor counting residual at the final
at-sqrt threshold. -/
noncomputable def ResidueDoubleDivisorFixedConstantAtSqrtBound
    (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorCountingSumAtSqrt n
        ≤ C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the explicit double-divisor counting
residual. -/
noncomputable def ResidueDoubleDivisorCanonicalAtSqrtBoundWithConstant :
    Prop :=
  ∃ C1 : ℝ, ResidueDoubleDivisorFixedConstantAtSqrtBound C1

/-- Fixed-coefficient coprime/shared-prime split residual for the explicit
double-divisor count. -/
noncomputable def ResidueDoubleDivisorCoprimeSplitFixedConstantAtSqrtBound
    (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorCoprimeCountingSumAtSqrt n
        + residueDoubleDivisorNonCoprimeCountingSumAtSqrt n
        ≤ C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the coprime/shared-prime split residual. -/
noncomputable def
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant :
    Prop :=
  ∃ C1 : ℝ, ResidueDoubleDivisorCoprimeSplitFixedConstantAtSqrtBound C1

/-! ## Closed rearrangement and split bridges -/

/-- The coefficient-bearing explicit double-divisor residual implies the
coefficient-bearing double-sum residual from Round 44. -/
theorem residueDoubleSumFixedConstantAtSqrt_of_doubleDivisorFixedConstant
    {C1 : ℝ} (h : ResidueDoubleDivisorFixedConstantAtSqrtBound C1) :
    ResidueDoubleSumFixedConstantAtSqrt C1 := by
  rcases h with ⟨hC1_pos, hbd⟩
  refine ⟨hC1_pos, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ 16).trans hn
  rw [residueMajorantSumAtSqrt_eq_doubleDivisorCountingSumAtSqrt hn2]
  exact hbd n hn

/-- The existential explicit double-divisor residual implies the Round 44
double-sum residual. -/
theorem residueDoubleSumWithConstant_of_doubleDivisorWithConstant
    (h : ResidueDoubleDivisorCanonicalAtSqrtBoundWithConstant) :
    ResidueDoubleSumCanonicalAtSqrtBoundWithConstant := by
  rcases h with ⟨C1, hC1⟩
  exact ⟨C1,
    residueDoubleSumFixedConstantAtSqrt_of_doubleDivisorFixedConstant hC1⟩

/-- The coefficient-bearing coprime/shared-prime split residual implies the
coefficient-bearing explicit double-divisor residual. -/
theorem residueDoubleDivisorFixedConstantAtSqrtBound_of_coprimeSplitFixedConstant
    {C1 : ℝ}
    (h : ResidueDoubleDivisorCoprimeSplitFixedConstantAtSqrtBound C1) :
    ResidueDoubleDivisorFixedConstantAtSqrtBound C1 := by
  rcases h with ⟨hC1_pos, hbd⟩
  refine ⟨hC1_pos, ?_⟩
  intro n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime]
  exact hbd n hn

/-- The existential coprime/shared-prime split residual implies the
existential explicit double-divisor residual. -/
theorem residueDoubleDivisorWithConstant_of_coprimeSplitWithConstant
    (h : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant) :
    ResidueDoubleDivisorCanonicalAtSqrtBoundWithConstant := by
  rcases h with ⟨C1, hC1⟩
  exact ⟨C1,
    residueDoubleDivisorFixedConstantAtSqrtBound_of_coprimeSplitFixedConstant
      hC1⟩

/-- The coefficient-bearing coprime/shared-prime split residual implies the
Round 44 double-sum residual. -/
theorem residueDoubleSumWithConstant_of_coprimeSplitWithConstant
    (h : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant) :
    ResidueDoubleSumCanonicalAtSqrtBoundWithConstant :=
  residueDoubleSumWithConstant_of_doubleDivisorWithConstant
    (residueDoubleDivisorWithConstant_of_coprimeSplitWithConstant h)

/-! ## Integration adapters -/

/-- The coefficient-bearing explicit double-divisor residual supplies the
supported finite-sieve input. -/
theorem finiteSieveInput_of_residueDoubleDivisorWithConstant
    (h : ResidueDoubleDivisorCanonicalAtSqrtBoundWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueDoubleSumWithConstant
    (residueDoubleSumWithConstant_of_doubleDivisorWithConstant h)

/-- The coefficient-bearing coprime/shared-prime split residual supplies the
supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCoprimeSplitWithConstant
    (h : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueDoubleDivisorWithConstant
    (residueDoubleDivisorWithConstant_of_coprimeSplitWithConstant h)

/-- Final Path C adapter from the coefficient-bearing explicit double-divisor
residual and any supported counting input. -/
theorem pathC_kGoldbach_of_residueDoubleDivisorWithConstant_and_countingInput
    (h : ResidueDoubleDivisorCanonicalAtSqrtBoundWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueDoubleSumWithConstant_and_countingInput
    (residueDoubleSumWithConstant_of_doubleDivisorWithConstant h)
    hCounting

/-- Final Path C adapter from the coefficient-bearing coprime/shared-prime
split residual and any supported counting input. -/
theorem pathC_kGoldbach_of_residueCoprimeSplitWithConstant_and_countingInput
    (h : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueDoubleSumWithConstant_and_countingInput
    (residueDoubleSumWithConstant_of_coprimeSplitWithConstant h)
    hCounting

end PathCResidueDoubleDivisorConstantDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueDoubleDivisorConstantDecomposition.residueDoubleSumFixedConstantAtSqrt_of_doubleDivisorFixedConstant
#print axioms
  Gdbh.PathCResidueDoubleDivisorConstantDecomposition.residueDoubleDivisorFixedConstantAtSqrtBound_of_coprimeSplitFixedConstant
#print axioms
  Gdbh.PathCResidueDoubleDivisorConstantDecomposition.residueDoubleSumWithConstant_of_coprimeSplitWithConstant
#print axioms
  Gdbh.PathCResidueDoubleDivisorConstantDecomposition.finiteSieveInput_of_residueCoprimeSplitWithConstant
#print axioms
  Gdbh.PathCResidueDoubleDivisorConstantDecomposition.pathC_kGoldbach_of_residueCoprimeSplitWithConstant_and_countingInput
