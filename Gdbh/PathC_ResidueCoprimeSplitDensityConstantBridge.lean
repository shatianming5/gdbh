/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueDoubleDivisorConstantDecomposition
import Gdbh.PathC_ResidueCoprimeSplitDensityBridge

/-!
# Path C -- coefficient-bearing split local-density bridge

Round 45 made the active CRT-facing residual coefficient-bearing.  This file
aligns the split local-density layer with that corrected shape.

The new worker target allows a fixed main coefficient in the exact
count-to-local-density comparison, while keeping the local-density Euler
identity exact.  This avoids treating the older coefficient-`1`
count-to-density residual as the primary route.
-/

set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCoprimeSplitDensityConstantBridge

open Gdbh.PathCResidueDoubleDivisorConstantDecomposition
  (ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant
   finiteSieveInput_of_residueCoprimeSplitWithConstant
   pathC_kGoldbach_of_residueCoprimeSplitWithConstant_and_countingInput)
open Gdbh.PathCResidueDoubleSumDecomposition
  (residueDoubleDivisorCountingSumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorCoprimeSplit
  (residueDoubleDivisorCoprimeCountingSumAtSqrt
   residueDoubleDivisorNonCoprimeCountingSumAtSqrt
   residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound
   ResidueDoubleDivisorLocalDensityEulerAtSqrt
   ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt
   residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueCoprimeSplitDensityBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound
   ResidueCoprimeSplitLocalDensityEulerAtSqrt
   residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit
   residueCoprimeSplitLocalDensityEulerAtSqrt_of_goldbachDensityMatch
   residueDoubleDivisorCoprimeLocalDensitySumAtSqrt
   residueDoubleDivisorLocalDensitySumAtSqrt_eq_coprime_add_nonCoprime
   residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical (residueBonferroniTailAtSqrt)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Coefficient-bearing count-to-density worker Props -/

/-- Fixed-coefficient split exact-count-to-local-density residual. -/
noncomputable def ResidueCoprimeSplitExactCountToLocalDensityFixedConstantAtSqrtBound
    (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorCoprimeCountingSumAtSqrt n
        + residueDoubleDivisorNonCoprimeCountingSumAtSqrt n
        ≤ C1 * (n : ℝ) *
            (residueDoubleDivisorCoprimeLocalDensitySumAtSqrt n
              + residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the split count-to-density residual. -/
noncomputable def
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant :
    Prop :=
  ∃ C1 : ℝ,
    ResidueCoprimeSplitExactCountToLocalDensityFixedConstantAtSqrtBound C1

/-- Fixed-coefficient unsplit exact-count-to-local-density residual. -/
noncomputable def
    ResidueDoubleDivisorExactCountToLocalDensityFixedConstantAtSqrtBound
    (C1 : ℝ) : Prop :=
  0 < C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorCountingSumAtSqrt n
        ≤ C1 * (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the unsplit count-to-density residual. -/
noncomputable def
    ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant :
    Prop :=
  ∃ C1 : ℝ,
    ResidueDoubleDivisorExactCountToLocalDensityFixedConstantAtSqrtBound C1

/-! ## Compatibility with older strict residuals -/

/-- The older split count-to-density residual is the `C1 = 1` case of the
coefficient-bearing split residual. -/
theorem residueCoprimeSplitExactCountToLocalDensityWithConstant_of_strict
    (h : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant := by
  refine ⟨1, by norm_num, ?_⟩
  intro n hn
  simpa [one_mul] using h n hn

/-- The older unsplit count-to-density residual is the `C1 = 1` case of the
coefficient-bearing unsplit residual. -/
theorem residueDoubleDivisorExactCountToLocalDensityWithConstant_of_strict
    (h : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound) :
    ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant := by
  refine ⟨1, by norm_num, ?_⟩
  intro n hn
  simpa [one_mul] using h n hn

/-! ## Split/unsplit partition bridge -/

/-- The coefficient-bearing unsplit count-to-density residual implies the
coefficient-bearing split count-to-density residual through the closed count
and local-density partition identities. -/
theorem residueCoprimeSplitExactCountToLocalDensityFixedConstant_of_unsplit
    {C1 : ℝ}
    (h : ResidueDoubleDivisorExactCountToLocalDensityFixedConstantAtSqrtBound
      C1) :
    ResidueCoprimeSplitExactCountToLocalDensityFixedConstantAtSqrtBound
      C1 := by
  rcases h with ⟨hC1_pos, hbd⟩
  refine ⟨hC1_pos, ?_⟩
  intro n hn
  have h := hbd n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime] at h
  rw [residueDoubleDivisorLocalDensitySumAtSqrt_eq_coprime_add_nonCoprime]
    at h
  exact h

/-- The existential unsplit count-to-density residual implies the existential
split count-to-density residual. -/
theorem residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
    (h : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant := by
  rcases h with ⟨C1, hC1⟩
  exact ⟨C1,
    residueCoprimeSplitExactCountToLocalDensityFixedConstant_of_unsplit hC1⟩

/-! ## Bridges to the active coefficient-bearing coprime split residual -/

/-- Coefficient-bearing split count-to-density plus exact split Euler algebra
imply the Round 45 coprime/shared-prime split residual. -/
theorem residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant := by
  rcases hCount with ⟨C1, hC1_pos, hCountBd⟩
  refine ⟨C1, hC1_pos, ?_⟩
  intro n hn
  have h := hCountBd n hn
  rw [hEuler n hn] at h
  exact h

/-- The coefficient-bearing unsplit count residual plus unsplit local-density
Euler identity imply the Round 45 coprime/shared-prime split residual. -/
theorem residueCoprimeSplitWithConstant_of_unsplitLocalDensityWithConstant
    (hCount :
      ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hEuler : ResidueDoubleDivisorLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant :=
  residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
      hCount)
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit hEuler)

/-- The coefficient-bearing unsplit count residual plus the primitive
Goldbach-density match imply the Round 45 coprime/shared-prime split residual. -/
theorem residueCoprimeSplitWithConstant_of_unsplitCount_and_goldbachDensityMatch
    (hCount :
      ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hMatch : ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBoundWithConstant :=
  residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
      hCount)
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_goldbachDensityMatch
      hMatch)

/-- Coefficient-bearing split local-density residuals supply the supported
finite-sieve input. -/
theorem finiteSieveInput_of_splitLocalDensityWithConstant
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCoprimeSplitWithConstant
    (residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
      hCount hEuler)

/-- Final Path C adapter from the coefficient-bearing split local-density
residuals and any supported counting input. -/
theorem pathC_kGoldbach_of_splitLocalDensityWithConstant_and_countingInput
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCoprimeSplitWithConstant_and_countingInput
    (residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
      hCount hEuler)
    hCounting

end PathCResidueCoprimeSplitDensityConstantBridge
end Gdbh

#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityConstantBridge.residueCoprimeSplitExactCountToLocalDensityWithConstant_of_strict
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityConstantBridge.residueCoprimeSplitExactCountToLocalDensityFixedConstant_of_unsplit
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityConstantBridge.residueCoprimeSplitWithConstant_of_splitLocalDensityWithConstant
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityConstantBridge.finiteSieveInput_of_splitLocalDensityWithConstant
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityConstantBridge.pathC_kGoldbach_of_splitLocalDensityWithConstant_and_countingInput
