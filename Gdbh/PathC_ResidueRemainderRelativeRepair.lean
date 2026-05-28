/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderAbsoluteRepair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder repair

Round 52 exposed the absolute-value remainder target needed for the repaired
residue route.  This file records a stricter but cleaner analytic worker
shape: control the absolute remainder by a constant multiple of the closed
local-density main term alone.  The nonnegative Bonferroni tail from Round 52
then embeds this relative estimate into the absolute absorbed-remainder target.

This does not revive the false coefficient-one tail-only route.  The finite
coefficient slack is explicit, and the target feeds back through the already
verified absolute-remainder adapter.
-/

namespace Gdbh
namespace PathCResidueRemainderRelativeRepair

open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (ResidueDoubleDivisorRemainderAbsoluteAtSqrtWithConstant
   ResidueDoubleDivisorRemainderAbsoluteFixedConstantAtSqrt
   pathC_kGoldbach_of_remainderAbsolute_and_countingInput
   residueBonferroniTailAtSqrt_nonneg)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Fixed-coefficient relative remainder control.  The error is measured
against the local-density main term, not against the Bonferroni tail. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeFixedConstantAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the relative remainder worker target. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant : Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeFixedConstantAtSqrt A

/-- Relative main-term control implies the Round 52 absolute absorbed-remainder
target by spending one unit of coefficient slack and keeping the nonnegative
Bonferroni tail. -/
theorem residueRemainderAbsoluteFixed_of_relative
    {A : ℝ}
    (hRel :
      ResidueDoubleDivisorRemainderRelativeFixedConstantAtSqrt A) :
    ResidueDoubleDivisorRemainderAbsoluteFixedConstantAtSqrt (A + 1) := by
  rcases hRel with ⟨hA_nonneg, hRelBd⟩
  refine ⟨by linarith, ?_⟩
  intro n hn
  have hRel' := hRelBd n hn
  have htail : 0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) :=
    residueBonferroniTailAtSqrt_nonneg n (Nat.sqrt n)
  calc
    |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
          hRel'
    _ ≤ (A + 1 - 1) *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
        have hEq :
            (A + 1 - 1) *
                ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
              =
            A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
          ring
        rw [hEq]
        exact le_add_of_nonneg_right htail

/-- The existential relative target supplies the Round 52 absolute target. -/
theorem residueRemainderAbsoluteWithConstant_of_relative
    (hRel :
      ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant) :
    ResidueDoubleDivisorRemainderAbsoluteAtSqrtWithConstant := by
  rcases hRel with ⟨A, hA⟩
  exact ⟨A + 1, residueRemainderAbsoluteFixed_of_relative hA⟩

/-- Final Path C adapter from the relative remainder target and any supported
counting input. -/
theorem pathC_kGoldbach_of_remainderRelative_and_countingInput
    (hRel :
      ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAbsolute_and_countingInput
    (residueRemainderAbsoluteWithConstant_of_relative hRel)
    hCounting

end PathCResidueRemainderRelativeRepair
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderRelativeRepair.residueRemainderAbsoluteFixed_of_relative
#print axioms
  Gdbh.PathCResidueRemainderRelativeRepair.residueRemainderAbsoluteWithConstant_of_relative
#print axioms
  Gdbh.PathCResidueRemainderRelativeRepair.pathC_kGoldbach_of_remainderRelative_and_countingInput
