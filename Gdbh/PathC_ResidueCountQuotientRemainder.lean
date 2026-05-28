/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCountCountingAdapters
import Gdbh.PathC_ResidueQuotientMainClosure
import Mathlib.Tactic.Linarith

/-!
# Path C -- residue count quotient/remainder reduction

Round 48 made the final branch explicitly consume the coefficient-bearing
residue count target plus one counting-side residual.  This file decomposes
that residue count target one layer further.

The quotient-main part is already closed by
`PathC_ResidueQuotientMainClosure`: it is exactly the double local-density
main term.  The remaining residue-side worker target is therefore the signed
remainder tail bound exposed here as
`ResidueDoubleDivisorRemainderTailSubtargetAtSqrt`.

This keeps the strict coefficient-`1` route marked as a strong sufficient
case, while the active branch still flows through the coefficient-bearing
count target.
-/

namespace Gdbh
namespace PathCResidueCountQuotientRemainder

open Gdbh.PathCResidueCoprimeSplitDensityConstantBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant
   ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant
   residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit)
open Gdbh.PathCResidueConstantCountClosure
  (pathC_kGoldbach_of_splitCountWithConstant_and_countingInput)
open Gdbh.PathCResidueCountCountingAdapters
  (pathC_kGoldbach_of_splitCountWithConstant_and_occupiedAverage
   pathC_kGoldbach_of_splitCountWithConstant_and_occupiedLogUpgrade
   pathC_kGoldbach_of_splitCountWithConstant_and_schnirelmannDensity_pos
   pathC_kGoldbach_of_splitCountWithConstant_and_uniformLowerBound)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorRemainderAtSqrtBound
   residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder
   residueDoubleDivisorQuotientMainSumAtSqrt
   residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueQuotientMainClosure
  (residueDoubleDivisorQuotientMainLocalDensityReduction)
open Gdbh.PathCSingularCountingInterface
  (GoldbachSingularMultiplierOccupiedAverageBound
   GoldbachSingularMultiplierOccupiedLogToAverageUpgrade PathCCountingInput)
open Gdbh.PathCPrimesSumsetDensity (PrimesSumsetUniformLowerBound)
open Gdbh.PathCKGoldbach (primesSumset)

/-! ## Residue-side remainder subtarget -/

/-- The signed-remainder tail bound is the strict smaller residue-side
subtarget below the coefficient-bearing unsplit count target.

This is definitionally the existing Round 21 remainder residual, but is named
here as the current post-Round-48 worker handoff. -/
def ResidueDoubleDivisorRemainderTailSubtargetAtSqrt : Prop :=
  ResidueDoubleDivisorRemainderAtSqrtBound

/-- The remainder subtarget implies the coefficient-bearing unsplit count
target directly through the closed quotient-main local-density equality. -/
theorem residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderSubtarget
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt) :
    ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant := by
  refine ⟨1, by norm_num, ?_⟩
  intro n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder]
  have hMain : residueDoubleDivisorQuotientMainSumAtSqrt n =
      (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold residueDoubleDivisorQuotientMainSumAtSqrt
      residueDoubleDivisorLocalDensitySumAtSqrt
    rw [residueDoubleDivisorQuotientMainLocalDensityReduction]
  have hRem' := hRem n hn
  rw [hMain]
  linarith

/-- The remainder subtarget also implies the active coefficient-bearing split
count target. -/
theorem residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant :=
  residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
    (residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)

/-! ## Final adapters after the quotient-main closure -/

/-- Final adapter from the remainder subtarget and any supported counting
input. -/
theorem pathC_kGoldbach_of_remainderSubtarget_and_countingInput
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)
    hCounting

/-- Final adapter from the remainder subtarget and occupied-average
counting. -/
theorem pathC_kGoldbach_of_remainderSubtarget_and_occupiedAverage
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_occupiedAverage
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)
    hOcc

/-- Final adapter from the remainder subtarget and the no-log-loss
occupied-average upgrade. -/
theorem pathC_kGoldbach_of_remainderSubtarget_and_occupiedLogUpgrade
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_occupiedLogUpgrade
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)
    hUpgrade

/-- Final adapter from the remainder subtarget and a uniform lower bound for
`primesSumset`. -/
theorem pathC_kGoldbach_of_remainderSubtarget_and_uniformLowerBound
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_uniformLowerBound
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)
    hUniform

/-- Final adapter from the remainder subtarget and positive Schnirelmann
density of `primesSumset`. -/
theorem pathC_kGoldbach_of_remainderSubtarget_and_schnirelmannDensity_pos
    (hRem : ResidueDoubleDivisorRemainderTailSubtargetAtSqrt)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_schnirelmannDensity_pos
    (residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
      hRem)
    hσ

end PathCResidueCountQuotientRemainder
end Gdbh

#print axioms
  Gdbh.PathCResidueCountQuotientRemainder.residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderSubtarget
#print axioms
  Gdbh.PathCResidueCountQuotientRemainder.residueCoprimeSplitExactCountToLocalDensityWithConstant_of_remainderSubtarget
#print axioms
  Gdbh.PathCResidueCountQuotientRemainder.pathC_kGoldbach_of_remainderSubtarget_and_countingInput
#print axioms
  Gdbh.PathCResidueCountQuotientRemainder.pathC_kGoldbach_of_remainderSubtarget_and_occupiedAverage
#print axioms
  Gdbh.PathCResidueCountQuotientRemainder.pathC_kGoldbach_of_remainderSubtarget_and_uniformLowerBound
