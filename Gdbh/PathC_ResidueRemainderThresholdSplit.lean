/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderRelativeRepair
import Mathlib.Tactic.Linarith

/-!
# Path C -- relative remainder threshold split

Round 53 exposed a tail-free relative remainder target.  This file makes the
next split explicit: a finite `Nat.sqrt n ≤ N` prefix and a large-range
`N + 1 ≤ Nat.sqrt n` analytic tail are separate worker Props.  The bridge
uses the maximum of the two constants to recover the Round 53 target.

This avoids the known bad CRT-error envelope route: no absolute sum over all
subset pairs is introduced.  The finite prefix can be attacked by computation,
while the large-range tail keeps the analytic content isolated.
-/

namespace Gdbh
namespace PathCResidueRemainderThresholdSplit

open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderRelativeRepair
  (ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant
   ResidueDoubleDivisorRemainderRelativeFixedConstantAtSqrt
   pathC_kGoldbach_of_remainderRelative_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Finite-prefix relative remainder target below a chosen square-root
threshold. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeFinitePrefixAtSqrt
    (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n ≤ N →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Large-range relative remainder target above a chosen square-root
threshold. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold
    (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Fixed-threshold split form of the Round 53 relative remainder target. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeThresholdSplitAtSqrt
    (N : ℕ) : Prop :=
  ∃ A₀ A₁ : ℝ,
    ResidueDoubleDivisorRemainderRelativeFinitePrefixAtSqrt N A₀ ∧
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold N A₁

/-- Existential-threshold split form of the relative remainder target. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeThresholdSplit : Prop :=
  ∃ N : ℕ,
    ResidueDoubleDivisorRemainderRelativeThresholdSplitAtSqrt N

/-- A finite-prefix bound and a large-range bound combine into the Round 53
fixed-coefficient relative target, with coefficient `max A₀ A₁`. -/
theorem residueRemainderRelativeFixed_of_thresholdSplit
    {N : ℕ} {A₀ A₁ : ℝ}
    (hPrefix :
      ResidueDoubleDivisorRemainderRelativeFinitePrefixAtSqrt N A₀)
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold N A₁) :
    ResidueDoubleDivisorRemainderRelativeFixedConstantAtSqrt
      (max A₀ A₁) := by
  rcases hPrefix with ⟨hA₀, hPrefixBd⟩
  rcases hAfter with ⟨hA₁, hAfterBd⟩
  refine ⟨hA₀.trans (le_max_left A₀ A₁), ?_⟩
  intro n hn
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt : Nat.sqrt n ≤ N
  · have hbd := hPrefixBd n hn hsqrt
    have hscale :
        A₀ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₀ A₁ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left A₀ A₁) hmain_nonneg
    exact hbd.trans hscale
  · have hafter_sqrt : N + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr (lt_of_not_ge hsqrt)
    have hbd := hAfterBd n hn hafter_sqrt
    have hscale :
        A₁ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₀ A₁ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right A₀ A₁) hmain_nonneg
    exact hbd.trans hscale

/-- Fixed-threshold split form supplies the Round 53 existential relative
target. -/
theorem residueRemainderRelativeWithConstant_of_thresholdSplitAtSqrt
    {N : ℕ}
    (hSplit :
      ResidueDoubleDivisorRemainderRelativeThresholdSplitAtSqrt N) :
    ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant := by
  rcases hSplit with ⟨A₀, A₁, hPrefix, hAfter⟩
  exact ⟨max A₀ A₁,
    residueRemainderRelativeFixed_of_thresholdSplit hPrefix hAfter⟩

/-- Existential-threshold split form supplies the Round 53 relative target. -/
theorem residueRemainderRelativeWithConstant_of_thresholdSplit
    (hSplit :
      ResidueDoubleDivisorRemainderRelativeThresholdSplit) :
    ResidueDoubleDivisorRemainderRelativeAtSqrtWithConstant := by
  rcases hSplit with ⟨N, hN⟩
  exact residueRemainderRelativeWithConstant_of_thresholdSplitAtSqrt hN

/-- Final Path C adapter from the threshold-split relative remainder target and
any supported counting input. -/
theorem pathC_kGoldbach_of_remainderThresholdSplit_and_countingInput
    (hSplit :
      ResidueDoubleDivisorRemainderRelativeThresholdSplit)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderRelative_and_countingInput
    (residueRemainderRelativeWithConstant_of_thresholdSplit hSplit)
    hCounting

end PathCResidueRemainderThresholdSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderThresholdSplit.residueRemainderRelativeFixed_of_thresholdSplit
#print axioms
  Gdbh.PathCResidueRemainderThresholdSplit.residueRemainderRelativeWithConstant_of_thresholdSplitAtSqrt
#print axioms
  Gdbh.PathCResidueRemainderThresholdSplit.residueRemainderRelativeWithConstant_of_thresholdSplit
#print axioms
  Gdbh.PathCResidueRemainderThresholdSplit.pathC_kGoldbach_of_remainderThresholdSplit_and_countingInput
