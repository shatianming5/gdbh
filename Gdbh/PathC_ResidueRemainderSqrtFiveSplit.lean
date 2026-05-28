/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtFourPrefix
import Mathlib.Tactic.Linarith

/-!
# Path C -- relative remainder sqrt-five split

Round 55 closed the `Nat.sqrt n = 4` finite prefix, leaving the large-range
worker beginning at `5 ≤ Nat.sqrt n`.  This file performs the next honest
decomposition: isolate the finite `Nat.sqrt n = 5` prefix and leave the
strictly later `6 ≤ Nat.sqrt n` tail.

The file does not claim the `sqrt = 5` CRT table.  It creates stable smaller
worker Props and an axiom-clean bridge back to the current active route.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtFiveSplit

open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderSqrtFourPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtFive_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Fixed-coefficient finite-prefix worker for the `Nat.sqrt n = 5` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtFiveAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 5 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `sqrt = 5` finite-prefix worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtFiveWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtFiveAtSqrt A

/-- Remaining large-range worker after removing the `sqrt = 5` prefix. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 5 A

/-- A `sqrt = 5` prefix bound and a `sqrt ≥ 6` tail bound combine into the
Round 55 active `sqrt ≥ 5` target. -/
theorem residueRemainderAfterSqrtFiveFixed_of_sqrtFive_and_afterSqrtSix
    {A₅ A₆ : ℝ}
    (hFive :
      ResidueDoubleDivisorRemainderRelativeSqrtFiveAtSqrt A₅)
    (hSix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 5 A₆) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 4
      (max A₅ A₆) := by
  rcases hFive with ⟨hA₅, hFiveBd⟩
  rcases hSix with ⟨hA₆, hSixBd⟩
  refine ⟨hA₅.trans (le_max_left A₅ A₆), ?_⟩
  intro n hn hsqrt_ge_five
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt : Nat.sqrt n = 5
  · have hbd := hFiveBd n hn hsqrt
    have hscale :
        A₅ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₅ A₆ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left A₅ A₆) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_six : 5 + 1 ≤ Nat.sqrt n := by
      have hne : 5 ≠ Nat.sqrt n := by
        intro h
        exact hsqrt h.symm
      exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hsqrt_ge_five hne)
    have hbd := hSixBd n hn hsqrt_ge_six
    have hscale :
        A₆ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₅ A₆ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right A₅ A₆) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 55 active
`sqrt ≥ 5` target. -/
theorem residueRemainderAfterSqrtFive_of_sqrtFive_and_afterSqrtSix
    (hFive :
      ResidueDoubleDivisorRemainderRelativeSqrtFiveWithConstant)
    (hSix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant := by
  rcases hFive with ⟨A₅, hA₅⟩
  rcases hSix with ⟨A₆, hA₆⟩
  exact ⟨max A₅ A₆,
    residueRemainderAfterSqrtFiveFixed_of_sqrtFive_and_afterSqrtSix
      hA₅ hA₆⟩

/-- Final Path C adapter after splitting the Round 55 active target into the
`sqrt = 5` prefix and `sqrt ≥ 6` tail. -/
theorem pathC_kGoldbach_of_remainderSqrtFive_and_afterSqrtSix
    (hFive :
      ResidueDoubleDivisorRemainderRelativeSqrtFiveWithConstant)
    (hSix :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtFive_and_countingInput
    (residueRemainderAfterSqrtFive_of_sqrtFive_and_afterSqrtSix
      hFive hSix)
    hCounting

end PathCResidueRemainderSqrtFiveSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveSplit.residueRemainderAfterSqrtFiveFixed_of_sqrtFive_and_afterSqrtSix
#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveSplit.residueRemainderAfterSqrtFive_of_sqrtFive_and_afterSqrtSix
#print axioms
  Gdbh.PathCResidueRemainderSqrtFiveSplit.pathC_kGoldbach_of_remainderSqrtFive_and_afterSqrtSix
