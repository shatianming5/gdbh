/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalParametricCoarseSplit

/-!
# Path C -- residue canonical analytic tail reduction

Round 40 reduced the active finite-sieve worker target to a parameterized
large-range residual `N + 1 ≤ Nat.sqrt n`.  This file gives the next honest
analytic decomposition of that residual.

For any chosen threshold `N`, the residual follows from two strictly smaller
estimates:

* an upper bound for the residue-sifted count of size `n / (log n)^2`;
* a lower bound for the residue main factor of size `1 / (log n)^2`.

The bridge is deliberately algebraic.  It does not assert either analytic
estimate; it exposes them as stable worker Props with direct integration back
to the current Path C route.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueCanonicalAnalyticTailReduction

open Gdbh.PathCGoldbachResidues
  (goldbachResidueMainFactor goldbachResidueSiftedCount)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCResidueCanonicalParametricCoarseSplit
  (ResidueCanonicalFromSqrtAfterAtSqrt
   ResidueCanonicalFromSqrtAfterAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtAfter
   pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput
   residueCanonicalWithConstant_of_parametric_after)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Analytic tail worker Props -/

/-- Large-range residue-sifted count upper bound at `z = Nat.sqrt n`.

This is the sieve-counting half of the analytic tail decomposition. -/
noncomputable def ResidueSiftedCountLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Large-range lower bound for the residue main factor at `z = Nat.sqrt n`.

This is the Euler-product half of the analytic tail decomposition. -/
noncomputable def ResidueMainFactorLogSquaredLowerAfter
    (N : ℕ) (B : ℝ) : Prop :=
  0 < B ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      B / (Real.log (n : ℝ))^2 ≤
        goldbachResidueMainFactor n (Nat.sqrt n)

/-- Bundled analytic tail input for a fixed threshold `N`. -/
noncomputable def ResidueCanonicalLogSquaredTailInputs (N : ℕ) : Prop :=
  ∃ A B : ℝ,
    ResidueSiftedCountLogSquaredUpperAfter N A ∧
      ResidueMainFactorLogSquaredLowerAfter N B

/-! ## Bridge to the parameterized residual -/

/-- The two log-squared analytic estimates imply the parameterized corrected
residue residual after `N`. -/
theorem residueCanonicalFromSqrtAfterAtSqrt_of_logSquared_upper_lower
    {N : ℕ} {A B : ℝ}
    (hUpper : ResidueSiftedCountLogSquaredUpperAfter N A)
    (hLower : ResidueMainFactorLogSquaredLowerAfter N B) :
    ResidueCanonicalFromSqrtAfterAtSqrt N (A / B) := by
  rcases hUpper with ⟨hA_pos, hUpperBd⟩
  rcases hLower with ⟨hB_pos, hLowerBd⟩
  refine ⟨by positivity, ?_⟩
  intro n hn hsqrt
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount := hUpperBd n hn hsqrt
  have hfactor := hLowerBd n hn hsqrt
  have hn_pos_nat : 1 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn_pos_nat)
  have hlog_sq_ne : (Real.log (n : ℝ)) ^ 2 ≠ 0 := by positivity
  have hscale_nonneg : 0 ≤ (A / B * (n : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfactor hscale_nonneg
  have hmain :
      A * (n : ℝ) / (Real.log (n : ℝ))^2 ≤
        (A / B) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
    calc
      A * (n : ℝ) / (Real.log (n : ℝ))^2
          = (A / B * (n : ℝ)) *
              (B / (Real.log (n : ℝ))^2) := by
              field_simp [ne_of_gt hB_pos, hlog_sq_ne]
      _ ≤ (A / B * (n : ℝ)) *
            goldbachResidueMainFactor n (Nat.sqrt n) := hmul
      _ = (A / B) * (n : ℝ) *
            goldbachResidueMainFactor n (Nat.sqrt n) := by ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hmain.trans (le_add_of_nonneg_right htail_nonneg))

/-- Bundled analytic tail inputs close the parameterized residual after `N`. -/
theorem residueCanonicalFromSqrtAfterWithConstant_of_logSquared_inputs
    (N : ℕ) (hInputs : ResidueCanonicalLogSquaredTailInputs N) :
    ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N := by
  rcases hInputs with ⟨A, B, hUpper, hLower⟩
  exact ⟨A / B,
    residueCanonicalFromSqrtAfterAtSqrt_of_logSquared_upper_lower
      hUpper hLower⟩

/-! ## Integration adapters -/

/-- Analytic tail inputs recover the corrected canonical target with a
coefficient. -/
theorem residueCanonicalWithConstant_of_logSquared_tail_inputs
    (N : ℕ) (hInputs : ResidueCanonicalLogSquaredTailInputs N) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_parametric_after N
    (residueCanonicalFromSqrtAfterWithConstant_of_logSquared_inputs
      N hInputs)

/-- Analytic tail inputs supply the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalLogSquared_tail_inputs
    (N : ℕ) (hInputs : ResidueCanonicalLogSquaredTailInputs N) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtAfter N
    (residueCanonicalFromSqrtAfterWithConstant_of_logSquared_inputs
      N hInputs)

/-- Final Path C adapter from the analytic tail decomposition and any
supported counting input. -/
theorem pathC_kGoldbach_of_residueCanonicalLogSquared_tail_inputs_and_countingInput
    (N : ℕ) (hInputs : ResidueCanonicalLogSquaredTailInputs N)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput N
    (residueCanonicalFromSqrtAfterWithConstant_of_logSquared_inputs
      N hInputs)
    hCounting

end PathCResidueCanonicalAnalyticTailReduction
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalAnalyticTailReduction.residueCanonicalFromSqrtAfterAtSqrt_of_logSquared_upper_lower
#print axioms
  Gdbh.PathCResidueCanonicalAnalyticTailReduction.residueCanonicalFromSqrtAfterWithConstant_of_logSquared_inputs
#print axioms
  Gdbh.PathCResidueCanonicalAnalyticTailReduction.residueCanonicalWithConstant_of_logSquared_tail_inputs
#print axioms
  Gdbh.PathCResidueCanonicalAnalyticTailReduction.finiteSieveInput_of_residueCanonicalLogSquared_tail_inputs
#print axioms
  Gdbh.PathCResidueCanonicalAnalyticTailReduction.pathC_kGoldbach_of_residueCanonicalLogSquared_tail_inputs_and_countingInput
