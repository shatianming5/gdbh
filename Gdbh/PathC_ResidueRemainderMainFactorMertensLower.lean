/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueMainFactorMertensLower
import Gdbh.PathC_ResidueRemainderAnalyticTailReduction

/-!
# Path C -- residue remainder main-factor Mertens lower reuse

Round 72 split the relative-remainder large tail into two log-squared analytic
inputs: a signed-remainder upper bound and the residue main-factor lower bound.
The main-factor lower half was already closed in the canonical route from the
paired-Brun Mertens lower theorem.

This file reuses that closed lower half for the remainder route, leaving only
the signed-remainder upper estimate as the active large-tail worker.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderMainFactorMertensLower

open Gdbh.PathCResidueCanonicalAnalyticTailReduction
  (ResidueMainFactorLogSquaredLowerAfter)
open Gdbh.PathCResidueMainFactorMertensLower
  (ResidueMainFactorLogSquaredLowerEventually
   residueMainFactorLogSquaredLowerAfter_mono
   residueMainFactorLogSquaredLowerEventually_holds)
open Gdbh.PathCResidueRemainderAnalyticTailReduction
  (ResidueRemainderLogSquaredUpperAfter
   ResidueRemainderLogSquaredTailInputs
   pathC_kGoldbach_of_remainderLogSquared_tail_inputs_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Eventual remainder worker targets -/

/-- Eventual form of the signed-remainder log-squared upper bound. -/
noncomputable def ResidueRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ, ResidueRemainderLogSquaredUpperAfter N A

/-- Eventual form of the bundled remainder log-squared tail input. -/
noncomputable def ResidueRemainderLogSquaredTailEventually : Prop :=
  ∃ N : ℕ, ResidueRemainderLogSquaredTailInputs N

/-! ## Threshold monotonicity and recombination -/

/-- Raising the threshold preserves the signed-remainder upper bound. -/
theorem residueRemainderLogSquaredUpperAfter_mono
    {N M : ℕ} {A : ℝ} (hNM : N ≤ M)
    (h : ResidueRemainderLogSquaredUpperAfter N A) :
    ResidueRemainderLogSquaredUpperAfter M A := by
  rcases h with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact hbd n hn (by omega)

/-- Once the signed-remainder upper bound is eventually available, the closed
Mertens lower bound supplies the full bundled remainder analytic-tail input. -/
theorem residueRemainderLogSquaredTailEventually_of_remainderUpperEventually
    (hUpper : ResidueRemainderLogSquaredUpperEventually) :
    ResidueRemainderLogSquaredTailEventually := by
  rcases hUpper with ⟨NU, A, hU⟩
  rcases residueMainFactorLogSquaredLowerEventually_holds with ⟨NL, B, hL⟩
  refine ⟨max NU NL, A, B, ?_, ?_⟩
  · exact residueRemainderLogSquaredUpperAfter_mono
      (le_max_left NU NL) hU
  · exact residueMainFactorLogSquaredLowerAfter_mono
      (le_max_right NU NL) hL

/-- Final Path C adapter after closing the residue main-factor lower half of
the remainder analytic tail. -/
theorem pathC_kGoldbach_of_remainderLogSquaredUpperEventually_and_countingInput
    (hUpper : ResidueRemainderLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  rcases residueRemainderLogSquaredTailEventually_of_remainderUpperEventually
      hUpper with ⟨N, hInputs⟩
  exact
    pathC_kGoldbach_of_remainderLogSquared_tail_inputs_and_countingInput
      N hInputs hCounting

end PathCResidueRemainderMainFactorMertensLower
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderMainFactorMertensLower.residueRemainderLogSquaredUpperAfter_mono
#print axioms
  Gdbh.PathCResidueRemainderMainFactorMertensLower.residueRemainderLogSquaredTailEventually_of_remainderUpperEventually
#print axioms
  Gdbh.PathCResidueRemainderMainFactorMertensLower.pathC_kGoldbach_of_remainderLogSquaredUpperEventually_and_countingInput
