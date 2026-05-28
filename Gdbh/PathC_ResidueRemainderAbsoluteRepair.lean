/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderAbsorbedRepair
import Gdbh.PathC_ResidueFullLocalDensityClosure
import Gdbh.PathC_GoldbachResidues
import Mathlib.Tactic.Positivity

/-!
# Path C -- absolute-value remainder repair

Round 51 replaced the false strict remainder-to-tail route by an absorbed
signed-remainder target.  This file exposes the next standard analytic worker
shape: bound the absolute value of the signed remainder by the same
coefficient-bearing main-term slack.

The absolute-value target is stronger than the signed absorbed target, but it
is the natural form for a CRT/error estimate.  We also record that the
local-density main term and repaired right-hand side are nonnegative, so the
target is not structurally impossible for sign reasons.
-/

namespace Gdbh
namespace PathCResidueRemainderAbsoluteRepair

open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor_nonneg)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueRemainderAbsorbedRepair
  (ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant
   ResidueDoubleDivisorRemainderAbsorbedFixedConstantAtSqrt
   pathC_kGoldbach_of_remainderAbsorbed_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The closed local-density Euler algebra makes the at-sqrt local-density
main term nonnegative. -/
theorem residueDoubleDivisorLocalDensitySumAtSqrt_nonneg
    (n : ℕ) (hn : 16 ≤ n) :
    0 ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
  rw [
    Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
      n hn]
  exact goldbachResidueMainFactor_nonneg n (Nat.sqrt n)

/-- The canonical residue Bonferroni tail is nonnegative. -/
theorem residueBonferroniTailAtSqrt_nonneg (n z : ℕ) :
    0 ≤ residueBonferroniTailAtSqrt n z := by
  unfold residueBonferroniTailAtSqrt
  positivity

/-- The repaired absorbed-remainder right-hand side is nonnegative whenever
`1 ≤ C1`. -/
theorem residueRemainderAbsorbedRhs_nonneg
    {C1 : ℝ} (hC1 : 1 ≤ C1) (n : ℕ) (hn : 16 ≤ n) :
    0 ≤
      (C1 - 1) *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
  have hC1_slack : 0 ≤ C1 - 1 := by linarith
  have hmain :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  have htail : 0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) :=
    residueBonferroniTailAtSqrt_nonneg n (Nat.sqrt n)
  exact add_nonneg (mul_nonneg hC1_slack hmain) htail

/-- Fixed-coefficient absolute-value repair for the signed-remainder route. -/
noncomputable def
    ResidueDoubleDivisorRemainderAbsoluteFixedConstantAtSqrt
    (C1 : ℝ) : Prop :=
  1 ≤ C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ (C1 - 1) *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the absolute-value absorbed repair. -/
noncomputable def
    ResidueDoubleDivisorRemainderAbsoluteAtSqrtWithConstant : Prop :=
  ∃ C1 : ℝ,
    ResidueDoubleDivisorRemainderAbsoluteFixedConstantAtSqrt C1

/-- The absolute-value absorbed repair implies the signed absorbed repair from
Round 51. -/
theorem residueRemainderAbsorbedFixed_of_absolute
    {C1 : ℝ}
    (hAbs :
      ResidueDoubleDivisorRemainderAbsoluteFixedConstantAtSqrt C1) :
    ResidueDoubleDivisorRemainderAbsorbedFixedConstantAtSqrt C1 := by
  rcases hAbs with ⟨hC1, hAbsBd⟩
  refine ⟨hC1, ?_⟩
  intro n hn
  exact (le_abs_self (residueDoubleDivisorRemainderSumAtSqrt n)).trans
    (hAbsBd n hn)

/-- The existential absolute-value repair supplies the Round 51 absorbed
signed-remainder target. -/
theorem residueRemainderAbsorbedWithConstant_of_absolute
    (hAbs :
      ResidueDoubleDivisorRemainderAbsoluteAtSqrtWithConstant) :
    ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant := by
  rcases hAbs with ⟨C1, hC1⟩
  exact ⟨C1, residueRemainderAbsorbedFixed_of_absolute hC1⟩

/-- Final Path C adapter from the absolute-value absorbed remainder repair
and any supported counting input. -/
theorem pathC_kGoldbach_of_remainderAbsolute_and_countingInput
    (hAbs :
      ResidueDoubleDivisorRemainderAbsoluteAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAbsorbed_and_countingInput
    (residueRemainderAbsorbedWithConstant_of_absolute hAbs)
    hCounting

end PathCResidueRemainderAbsoluteRepair
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderAbsoluteRepair.residueDoubleDivisorLocalDensitySumAtSqrt_nonneg
#print axioms
  Gdbh.PathCResidueRemainderAbsoluteRepair.residueBonferroniTailAtSqrt_nonneg
#print axioms
  Gdbh.PathCResidueRemainderAbsoluteRepair.residueRemainderAbsorbedRhs_nonneg
#print axioms
  Gdbh.PathCResidueRemainderAbsoluteRepair.residueRemainderAbsorbedWithConstant_of_absolute
#print axioms
  Gdbh.PathCResidueRemainderAbsoluteRepair.pathC_kGoldbach_of_remainderAbsolute_and_countingInput
