/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCountQuotientRemainder
import Gdbh.PathC_ResidueRemainderFalseCatch
import Mathlib.Tactic.Linarith

/-!
# Path C -- quotient/remainder route false catch

Round 49 renamed the signed double-divisor remainder bound as
`ResidueDoubleDivisorRemainderTailSubtargetAtSqrt`.  This file records the
honesty correction: the renamed target is definitionally the Round 22
remainder target, already refuted at `n = 20` in
`PathC_ResidueRemainderFalseCatch`.

The active residue-side worker target should therefore stay at the
coefficient-bearing count residual, not the strict signed-remainder tail
bound.
-/

namespace Gdbh
namespace PathCResidueCountQuotientRemainderFalseCatch

open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCountQuotientRemainder
  (ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
open Gdbh.PathCResidueCoprimeSplitDensityConstantBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
open Gdbh.PathCResidueConstantCountClosure
  (pathC_kGoldbach_of_splitCountWithConstant_and_countingInput)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderFalseCatch
  (residueBonferroniTailAtSqrt_twenty_lt_third
   residueDoubleDivisorRemainderSumAtSqrt_twenty)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The explicit `n = 20` obstruction to the renamed Round 49 remainder
subtarget. -/
theorem not_remainderTailInequalityAtTwenty :
    ¬ residueDoubleDivisorRemainderSumAtSqrt 20
        ≤ residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) := by
  intro h
  rw [residueDoubleDivisorRemainderSumAtSqrt_twenty] at h
  have htail := residueBonferroniTailAtSqrt_twenty_lt_third
  linarith

/-- The Round 49 remainder-tail subtarget is exactly the already refuted
Round 22 signed-remainder target. -/
theorem not_residueDoubleDivisorRemainderTailSubtargetAtSqrt :
    ¬ ResidueDoubleDivisorRemainderTailSubtargetAtSqrt := by
  simpa [ResidueDoubleDivisorRemainderTailSubtargetAtSqrt] using
    Gdbh.PathCResidueRemainderFalseCatch.not_residueDoubleDivisorRemainderAtSqrtBound

/-- Stable status name for the controller: the strict quotient/remainder
branch is diagnostic only, because its worker target is false. -/
def ResidueCountQuotientRemainderRouteRefuted : Prop :=
  ¬ ResidueDoubleDivisorRemainderTailSubtargetAtSqrt

/-- The diagnostic status is closed by the existing `n = 20` false catch. -/
theorem residueCountQuotientRemainderRouteRefuted_holds :
    ResidueCountQuotientRemainderRouteRefuted :=
  not_residueDoubleDivisorRemainderTailSubtargetAtSqrt

/-- Active residue-side worker target after refuting the strict
quotient/remainder branch. -/
def ResidueCountPrimaryTargetAfterRemainderFalseCatch : Prop :=
  ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant

/-- The post-false-catch target is definitionally the coefficient-bearing
split count residual from Round 46/47. -/
theorem residueCountPrimaryTargetAfterRemainderFalseCatch_iff :
    ResidueCountPrimaryTargetAfterRemainderFalseCatch ↔
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant :=
  Iff.rfl

/-- Final Path C adapter from the post-false-catch primary residue target and
any supported counting input. -/
theorem pathC_kGoldbach_of_primaryTargetAfterRemainderFalseCatch_and_countingInput
    (hCount : ResidueCountPrimaryTargetAfterRemainderFalseCatch)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput hCount hCounting

end PathCResidueCountQuotientRemainderFalseCatch
end Gdbh

#print axioms
  Gdbh.PathCResidueCountQuotientRemainderFalseCatch.not_remainderTailInequalityAtTwenty
#print axioms
  Gdbh.PathCResidueCountQuotientRemainderFalseCatch.not_residueDoubleDivisorRemainderTailSubtargetAtSqrt
#print axioms
  Gdbh.PathCResidueCountQuotientRemainderFalseCatch.residueCountQuotientRemainderRouteRefuted_holds
#print axioms
  Gdbh.PathCResidueCountQuotientRemainderFalseCatch.residueCountPrimaryTargetAfterRemainderFalseCatch_iff
#print axioms
  Gdbh.PathCResidueCountQuotientRemainderFalseCatch.pathC_kGoldbach_of_primaryTargetAfterRemainderFalseCatch_and_countingInput
