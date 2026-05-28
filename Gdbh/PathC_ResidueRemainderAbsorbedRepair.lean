/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCountQuotientRemainderFalseCatch
import Gdbh.PathC_ResidueQuotientMainClosure
import Mathlib.Tactic.Ring

/-!
# Path C -- residue remainder absorbed repair

Round 50 refuted the strict signed-remainder target
`ResidueDoubleDivisorRemainderTailSubtargetAtSqrt`.  This file records the
honest coefficient-bearing repair: the signed remainder is not forced into the
Bonferroni tail alone, but may be absorbed into the extra main-term coefficient
of the active count-to-local-density target.

The quotient-main term is already closed as exactly
`n * residueDoubleDivisorLocalDensitySumAtSqrt n`, so the remaining worker
target is only the absorbed signed-remainder inequality below.
-/

namespace Gdbh
namespace PathCResidueRemainderAbsorbedRepair

open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCoprimeSplitDensityConstantBridge
  (ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant
   ResidueDoubleDivisorExactCountToLocalDensityFixedConstantAtSqrtBound
   residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit)
open Gdbh.PathCResidueCountQuotientRemainderFalseCatch
  (ResidueCountPrimaryTargetAfterRemainderFalseCatch)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorRemainderAtSqrtBound
   residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder
   residueDoubleDivisorQuotientMainSumAtSqrt
   residueDoubleDivisorRemainderSumAtSqrt)
open Gdbh.PathCResidueQuotientMainClosure
  (residueDoubleDivisorQuotientMainLocalDensityReduction)
open Gdbh.PathCResidueConstantCountClosure
  (pathC_kGoldbach_of_splitCountWithConstant_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Fixed-coefficient repair for the signed-remainder route.  The remainder is
allowed to use the extra `(C1 - 1)` share of the main local-density term,
instead of being forced into the Bonferroni tail alone. -/
noncomputable def
    ResidueDoubleDivisorRemainderAbsorbedFixedConstantAtSqrt
    (C1 : ℝ) : Prop :=
  1 ≤ C1 ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorRemainderSumAtSqrt n
        ≤ (C1 - 1) *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Existential coefficient form of the absorbed signed-remainder repair. -/
noncomputable def
    ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant : Prop :=
  ∃ C1 : ℝ,
    ResidueDoubleDivisorRemainderAbsorbedFixedConstantAtSqrt C1

/-- The strict signed-remainder target is the `C1 = 1` special case of the
absorbed repair.  Round 50 shows that this special case is false, so the
existential coefficient form above is the intended worker target. -/
theorem residueRemainderAbsorbedWithConstant_of_strictRemainder
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant := by
  refine ⟨1, by norm_num, ?_⟩
  intro n hn
  simpa using hRem n hn

/-- The absorbed signed-remainder repair closes the coefficient-bearing
unsplit count-to-local-density target, using the already closed quotient-main
calculation. -/
theorem residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderAbsorbed
    (hRem :
      ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant) :
    ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBoundWithConstant := by
  rcases hRem with ⟨C1, hC1_ge, hRemBd⟩
  refine ⟨C1, ?_, ?_⟩
  · linarith
  · intro n hn
    rw [residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder]
    have hMain : residueDoubleDivisorQuotientMainSumAtSqrt n =
        (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
      unfold residueDoubleDivisorQuotientMainSumAtSqrt
        residueDoubleDivisorLocalDensitySumAtSqrt
      rw [residueDoubleDivisorQuotientMainLocalDensityReduction]
    rw [hMain]
    have hRem' := hRemBd n hn
    calc
      (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n
          + residueDoubleDivisorRemainderSumAtSqrt n
          ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n
              + ((C1 - 1) *
                  ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
                + residueBonferroniTailAtSqrt n (Nat.sqrt n)) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hRem'
                    ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
      _ = C1 * (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n
            + residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
            ring

/-- The absorbed signed-remainder repair supplies the restored Round 50
primary residue-side target. -/
theorem primaryTargetAfterRemainderFalseCatch_of_remainderAbsorbed
    (hRem :
      ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant) :
    ResidueCountPrimaryTargetAfterRemainderFalseCatch :=
  residueCoprimeSplitExactCountToLocalDensityWithConstant_of_unsplit
    (residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderAbsorbed
      hRem)

/-- Final Path C adapter from the absorbed signed-remainder repair and any
supported counting input. -/
theorem pathC_kGoldbach_of_remainderAbsorbed_and_countingInput
    (hRem :
      ResidueDoubleDivisorRemainderAbsorbedAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    (primaryTargetAfterRemainderFalseCatch_of_remainderAbsorbed hRem)
    hCounting

end PathCResidueRemainderAbsorbedRepair
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderAbsorbedRepair.residueRemainderAbsorbedWithConstant_of_strictRemainder
#print axioms
  Gdbh.PathCResidueRemainderAbsorbedRepair.residueDoubleDivisorExactCountToLocalDensityWithConstant_of_remainderAbsorbed
#print axioms
  Gdbh.PathCResidueRemainderAbsorbedRepair.primaryTargetAfterRemainderFalseCatch_of_remainderAbsorbed
#print axioms
  Gdbh.PathCResidueRemainderAbsorbedRepair.pathC_kGoldbach_of_remainderAbsorbed_and_countingInput
