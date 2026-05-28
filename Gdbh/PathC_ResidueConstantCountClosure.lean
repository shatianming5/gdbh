/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCoprimeSplitDensityConstantBridge
import Gdbh.PathC_ResidueFullLocalDensityClosure
import Gdbh.PathC_ResidueQuotientMainClosure

/-!
# Path C -- coefficient-bearing count-only closure

Round 46 exposed a coefficient-bearing split count-to-local-density residual,
but still threaded the split local-density Euler identity as an explicit
input.  That Euler algebra is already closed by
`PathC_ResidueFullLocalDensityClosure`.

This file removes the closed Euler input from the coefficient-bearing branch.
The active finite-sieve side is reduced to the named count residual
`ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant`.

It also records the existing signed-remainder residual as a strong sufficient
condition for that coefficient-bearing count target, without making it the
primary route.
-/

namespace Gdbh
namespace PathCResidueConstantCountClosure

open Gdbh.PathCResidueCoprimeSplitDensityConstantBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant
   ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant
   finiteSieveInput_of_splitLocalDensityWithConstant
   pathC_kGoldbach_of_splitLocalDensityWithConstant_and_countingInput
   residueCoprimeSplitExactCountToLocalDensityWithConstant_of_strict
   residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorRemainderAtSqrtBound)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Count-only coefficient-bearing adapters -/

/-- Coefficient-bearing split count residual alone supplies finite-sieve input,
because the split local-density Euler algebra is already closed. -/
theorem finiteSieveInput_of_splitCountWithConstant
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_splitLocalDensityWithConstant hCount
    Gdbh.PathCResidueFullLocalDensityClosure.residueCoprimeSplitLocalDensityEulerAtSqrt

/-- Final Path C adapter from coefficient-bearing split count and counting
input. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitLocalDensityWithConstant_and_countingInput
    hCount
    Gdbh.PathCResidueFullLocalDensityClosure.residueCoprimeSplitLocalDensityEulerAtSqrt
    hCounting

/-- Coefficient-bearing unsplit count residual alone supplies finite-sieve
input. -/
theorem finiteSieveInput_of_unsplitCountWithConstant
    (hCount :
      ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_splitCountWithConstant
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
      hCount)

/-- Final Path C adapter from coefficient-bearing unsplit count and counting
input. -/
theorem pathC_kGoldbach_of_unsplitCountWithConstant_and_countingInput
    (hCount :
      ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
      hCount)
    hCounting

/-! ## Strong sufficient route through the signed-remainder residual -/

/-- The already isolated signed-remainder residual is a strong sufficient
condition for the coefficient-bearing split count residual. -/
theorem residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainder
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant :=
  residueCoprimeSplitExactCountToLocalDensityWithConstant_of_strict
    (Gdbh.PathCResidueQuotientMainClosure.residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_remainder
      hRem)

/-- Signed-remainder residual alone supplies finite-sieve input on the
coefficient-bearing route. -/
theorem finiteSieveInput_of_remainderWithConstant
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_splitCountWithConstant
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainder
      hRem)

/-- Final Path C adapter from the signed-remainder residual and counting input,
through the coefficient-bearing route. -/
theorem pathC_kGoldbach_of_residueRemainderWithConstant_and_countingInput
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainder
      hRem)
    hCounting

end PathCResidueConstantCountClosure
end Gdbh

#print axioms
  Gdbh.PathCResidueConstantCountClosure.finiteSieveInput_of_splitCountWithConstant
#print axioms
  Gdbh.PathCResidueConstantCountClosure.pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
#print axioms
  Gdbh.PathCResidueConstantCountClosure.finiteSieveInput_of_remainderWithConstant
#print axioms
  Gdbh.PathCResidueConstantCountClosure.pathC_kGoldbach_of_residueRemainderWithConstant_and_countingInput
