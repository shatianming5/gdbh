/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalAnalyticTailReduction
import Gdbh.PathC_ResidueRemainderParametricCoarseSplit

/-!
# Path C -- residue remainder analytic tail reduction

Round 71 reduced the relative-remainder route to a parameterized large-range
residual after any chosen threshold `N`.  This file gives the next honest
analytic decomposition of that residual.

For a fixed `N`, the residual follows from:

* an absolute upper bound for the signed double-divisor CRT remainder of size
  `n / (log n)^2`;
* the existing residue main-factor lower-bound worker of size
  `1 / (log n)^2`.

The bridge is algebraic and reuses the closed identity between the
double-divisor local-density sum and `goldbachResidueMainFactor`.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderAnalyticTailReduction

open Gdbh.PathCResidueCanonicalAnalyticTailReduction
  (ResidueMainFactorLogSquaredLowerAfter)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderParametricCoarseSplit
  (ResidueDoubleDivisorRemainderRelativeFromSqrtAfterAtSqrtWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtAfter_and_countingInput
   residueRemainderAfterSqrtTenThousandOne_of_parametric_after)
open Gdbh.PathCResidueRemainderSqrtSevenHundredTwentySixToTenThousandPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Analytic tail worker Props -/

/-- Large-range signed-remainder upper bound at `z = Nat.sqrt n`.

This is the CRT-error half of the remainder analytic tail decomposition. -/
noncomputable def ResidueRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Bundled analytic tail input for the relative-remainder residual after a
fixed threshold `N`. -/
noncomputable def ResidueRemainderLogSquaredTailInputs (N : ℕ) : Prop :=
  ∃ A B : ℝ,
    ResidueRemainderLogSquaredUpperAfter N A ∧
      ResidueMainFactorLogSquaredLowerAfter N B

/-! ## Bridge to the parameterized remainder residual -/

/-- The two log-squared analytic estimates imply the parameterized
relative-remainder residual after `N`. -/
theorem residueRemainderFromSqrtAfterAtSqrt_of_logSquared_upper_lower
    {N : ℕ} {A B : ℝ}
    (hUpper : ResidueRemainderLogSquaredUpperAfter N A)
    (hLower : ResidueMainFactorLogSquaredLowerAfter N B) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold N (A / B) := by
  rcases hUpper with ⟨hA_pos, hUpperBd⟩
  rcases hLower with ⟨hB_pos, hLowerBd⟩
  refine ⟨by positivity, ?_⟩
  intro n hn hsqrt
  have hrem := hUpperBd n hn hsqrt
  have hfactor_main := hLowerBd n hn hsqrt
  have hn_pos_nat : 1 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn_pos_nat)
  have hlog_sq_ne : (Real.log (n : ℝ)) ^ 2 ≠ 0 := by positivity
  have hfactor_local :
      B / (Real.log (n : ℝ))^2 ≤
        residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rwa [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
  have hscale_nonneg : 0 ≤ (A / B * (n : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfactor_local hscale_nonneg
  have hmain :
      A * (n : ℝ) / (Real.log (n : ℝ))^2 ≤
        (A / B) *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    calc
      A * (n : ℝ) / (Real.log (n : ℝ))^2
          = (A / B * (n : ℝ)) *
              (B / (Real.log (n : ℝ))^2) := by
              field_simp [ne_of_gt hB_pos, hlog_sq_ne]
      _ ≤ (A / B * (n : ℝ)) *
            residueDoubleDivisorLocalDensitySumAtSqrt n := hmul
      _ = (A / B) *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
          ring
  exact hrem.trans hmain

/-- Bundled analytic tail inputs close the parameterized remainder residual
after `N`. -/
theorem residueRemainderFromSqrtAfterWithConstant_of_logSquared_inputs
    (N : ℕ) (hInputs : ResidueRemainderLogSquaredTailInputs N) :
    ResidueDoubleDivisorRemainderRelativeFromSqrtAfterAtSqrtWithConstant N := by
  rcases hInputs with ⟨A, B, hUpper, hLower⟩
  exact ⟨A / B,
    residueRemainderFromSqrtAfterAtSqrt_of_logSquared_upper_lower
      hUpper hLower⟩

/-! ## Integration adapters -/

/-- Remainder analytic tail inputs recover the active post-`10000`
relative-remainder target. -/
theorem residueRemainderAfterSqrtTenThousandOne_of_logSquared_tail_inputs
    (N : ℕ) (hInputs : ResidueRemainderLogSquaredTailInputs N) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtTenThousandOneWithConstant :=
  residueRemainderAfterSqrtTenThousandOne_of_parametric_after N
    (residueRemainderFromSqrtAfterWithConstant_of_logSquared_inputs
      N hInputs)

/-- Final Path C adapter from the remainder analytic tail decomposition and
any supported counting input. -/
theorem pathC_kGoldbach_of_remainderLogSquared_tail_inputs_and_countingInput
    (N : ℕ) (hInputs : ResidueRemainderLogSquaredTailInputs N)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtAfter_and_countingInput N
    (residueRemainderFromSqrtAfterWithConstant_of_logSquared_inputs
      N hInputs)
    hCounting

end PathCResidueRemainderAnalyticTailReduction
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderAnalyticTailReduction.residueRemainderFromSqrtAfterAtSqrt_of_logSquared_upper_lower
#print axioms
  Gdbh.PathCResidueRemainderAnalyticTailReduction.residueRemainderFromSqrtAfterWithConstant_of_logSquared_inputs
#print axioms
  Gdbh.PathCResidueRemainderAnalyticTailReduction.residueRemainderAfterSqrtTenThousandOne_of_logSquared_tail_inputs
#print axioms
  Gdbh.PathCResidueRemainderAnalyticTailReduction.pathC_kGoldbach_of_remainderLogSquared_tail_inputs_and_countingInput
