/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderFalseCatch
import Gdbh.PathC_FinalClosedReductions

/-!
# Path C -- corrected residue canonical route

`PathC_ResidueRemainderFalseCatch` proves that the strict residue canonical
kernel with coefficient `1` is false at `n = 20`.  This file replaces that
dead worker target with the coefficient-bearing shape already supported by
the final Path C finite-sieve interface.

The new target is still concrete: it keeps the explicit canonical Bonferroni
tail, but it exposes the main-term constant `C₁` as part of the finite-sieve
work.  That is the shape consumed by
`BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError`.
-/

namespace Gdbh
namespace PathCResidueCanonicalCorrectedRoute

open Gdbh.PathCGoldbachResidues
  (BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
   GoldbachResidueErrorBoundedByRefinedAtSqrt
   goldbachResidueMainFactor goldbachResidueSiftedCount)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt residueBonferroniTailAtSqrtErrorBound_holds)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput
   pathC_kGoldbach_of_finiteSieveInput_and_countingInput)
open Gdbh.PathCFinalClosedReductions
  (PathC_CorrectedSingularTeamContent
   pathC_kGoldbach_of_corrected_singular_team_content)

/-! ## Corrected worker target -/

/-- Fixed-constant version of the corrected canonical-tail residue target.

This is the strictly smaller fixed-`C₁` sub-Prop used by the controller before
the existential worker target. -/
def ResidueCanonicalFixedConstantAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n →
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Corrected replacement for the false strict canonical kernel.

Unlike `BrunGoldbachResidueSiftedAtSqrtCanonicalKernel`, this target does not
force the main-term coefficient to be `1`.  The `n = 20` obstruction is
defused by allowing an honest finite-sieve constant. -/
def BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFixedConstantAtSqrt C₁

/-- The fixed-constant sub-Prop closes the existential corrected target. -/
theorem residueCanonicalWithConstant_of_fixed
    {C₁ : ℝ} (h : ResidueCanonicalFixedConstantAtSqrt C₁) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  ⟨C₁, h⟩

/-! ## Bridges back to the supported Path C interface -/

/-- The corrected canonical-tail target is exactly an at-sqrt abstract-error
finite-sieve upper bound with `B = residueBonferroniTailAtSqrt`. -/
theorem residueSiftedUpperBoundAtSqrtWithError_of_canonicalWithConstant
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant) :
    BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
      residueBonferroniTailAtSqrt := by
  rcases hCan with ⟨C₁, hC₁_pos, hCanBd⟩
  refine ⟨C₁, 16, hC₁_pos, ?_⟩
  intro n hn _hn2
  exact hCanBd n hn

/-- The corrected canonical-tail target supplies the supported finite-sieve
input, because the explicit canonical tail is already bounded by the refined
reservoir. -/
theorem finiteSieveInput_of_residueCanonicalWithConstant
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant) :
    PathCFiniteSieveInput :=
  PathCFiniteSieveInput.atSqrtFields
    (residueSiftedUpperBoundAtSqrtWithError_of_canonicalWithConstant hCan)
    residueBonferroniTailAtSqrtErrorBound_holds

/-- Team-content packaging for the corrected singular-factor route. -/
noncomputable def correctedSingularTeamContent_of_residueCanonicalWithConstant
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
    (hCounting : PathCCountingInput) :
    PathC_CorrectedSingularTeamContent where
  finiteSieve := finiteSieveInput_of_residueCanonicalWithConstant hCan
  counting := hCounting

/-- Final Path C adapter from the corrected canonical-tail target and any
supported counting input. -/
theorem pathC_kGoldbach_of_residueCanonicalWithConstant_and_countingInput
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    (finiteSieveInput_of_residueCanonicalWithConstant hCan)
    hCounting

/-- The same final adapter routed through the corrected team-content wrapper. -/
theorem pathC_kGoldbach_of_correctedTeamContent_from_residueCanonicalWithConstant
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_corrected_singular_team_content
    (correctedSingularTeamContent_of_residueCanonicalWithConstant hCan hCounting)

/-! ## Sanity check at the previous obstruction -/

/-- Allowing an honest main-term constant defuses the `n = 20` obstruction:
the exact same small case is already compatible with `C₁ = 2`. -/
theorem residueCanonicalFixedConstant_two_holds_at_twenty :
    (goldbachResidueSiftedCount 20 (Nat.sqrt 20) : ℝ)
      ≤ (2 : ℝ) * (20 : ℝ) * goldbachResidueMainFactor 20 (Nat.sqrt 20)
        + residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) := by
  have hsqrt : Nat.sqrt 20 = 4 := by norm_num
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  have htail_nonneg_four :
      0 ≤ residueBonferroniTailAtSqrt 20 4 := by
    simpa [hsqrt] using htail_nonneg
  rw [hsqrt,
    Gdbh.PathCResidueRemainderFalseCatch.goldbachResidueSiftedCount_twenty_four,
    Gdbh.PathCResidueRemainderFalseCatch.goldbachResidueMainFactor_twenty_four]
  nlinarith

end PathCResidueCanonicalCorrectedRoute
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.residueCanonicalWithConstant_of_fixed
#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.residueSiftedUpperBoundAtSqrtWithError_of_canonicalWithConstant
#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.finiteSieveInput_of_residueCanonicalWithConstant
#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.pathC_kGoldbach_of_residueCanonicalWithConstant_and_countingInput
#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.pathC_kGoldbach_of_correctedTeamContent_from_residueCanonicalWithConstant
#print axioms
  Gdbh.PathCResidueCanonicalCorrectedRoute.residueCanonicalFixedConstant_two_holds_at_twenty
