/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCoprimeSplitDensityBridge
import Mathlib.Tactic

/-!
# Path C -- split local-density depth removal

`PathC_ResidueCoprimeSplitDensityBridge` reduces the current residue
double-divisor residual to a split count-to-density estimate and a split
local-density Euler identity.  This file removes one mechanical obstacle from
the Euler side: at `z = sqrt n` and canonical depth `canonicalK n = 2n`, the
subset-size filter is already the full powerset.

The remaining Euler worker target is therefore the untruncated
coprime/overlap local-density identity.
-/

namespace Gdbh
namespace PathCResidueSplitLocalDensityDepth

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueCoprimeSplitDensityBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound
   ResidueCoprimeSplitLocalDensityEulerAtSqrt
   residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_splitLocalDensity
   pathC_kGoldbach_of_residueCoprimeSplitDensity_and_countingInput
   residueDoubleDivisorCoprimeLocalDensitySum
   residueDoubleDivisorCoprimeLocalDensitySumAtSqrt
   residueDoubleDivisorLocalDensityPairWeight
   residueDoubleDivisorNonCoprimeLocalDensitySum
   residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorCoprimeSplit
  (ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The untruncated coprime part of the compatible local-density sum. -/
noncomputable def residueDoubleDivisorCoprimeLocalDensityFullSum
    (n z : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset,
    ∑ d₂ ∈ (residuePrimeSet z).powerset,
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        residueDoubleDivisorLocalDensityPairWeight n d₁ d₂
      else 0

/-- The untruncated shared-prime overlap part of the compatible local-density
sum. -/
noncomputable def residueDoubleDivisorNonCoprimeLocalDensityFullSum
    (n z : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset,
    ∑ d₂ ∈ (residuePrimeSet z).powerset,
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        0
      else residueDoubleDivisorLocalDensityPairWeight n d₁ d₂

/-- The untruncated coprime local-density part at `z = sqrt n`. -/
noncomputable def residueDoubleDivisorCoprimeLocalDensityFullSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorCoprimeLocalDensityFullSum n (Nat.sqrt n)

/-- The untruncated shared-prime overlap local-density part at `z = sqrt n`. -/
noncomputable def residueDoubleDivisorNonCoprimeLocalDensityFullSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorNonCoprimeLocalDensityFullSum n (Nat.sqrt n)

/-- Untruncated split Euler worker target after the canonical-depth filter is
removed. -/
def ResidueCoprimeSplitFullLocalDensityEulerAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCoprimeLocalDensityFullSumAtSqrt n
      + residueDoubleDivisorNonCoprimeLocalDensityFullSumAtSqrt n
        = goldbachResidueMainFactor n (Nat.sqrt n)

/-- At the final threshold, every odd-prime subset has size at most the
canonical depth `2n`. -/
theorem residuePrimeSet_card_sqrt_le_canonicalK
    (n : ℕ) (hn : 16 ≤ n) :
    (residuePrimeSet (Nat.sqrt n)).card ≤ canonicalK n := by
  classical
  have hsub :
      residuePrimeSet (Nat.sqrt n) ⊆ Finset.range (Nat.sqrt n + 1) := by
    intro p hp
    have hpIcc : p ∈ Finset.Icc 3 (Nat.sqrt n) :=
      (Finset.mem_filter.mp hp).1
    have hp_le : p ≤ Nat.sqrt n := (Finset.mem_Icc.mp hpIcc).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hp_le)
  have hcard := Finset.card_le_card hsub
  have hsqrt_le : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  simp only [Finset.card_range] at hcard
  unfold canonicalK
  omega

/-- The canonical-depth filter is the full powerset at `z = sqrt n`. -/
theorem residuePrimeSet_powerset_filter_card_le_canonicalK
    (n : ℕ) (hn : 16 ≤ n) :
    (residuePrimeSet (Nat.sqrt n)).powerset.filter
        (fun d => d.card ≤ canonicalK n)
      = (residuePrimeSet (Nat.sqrt n)).powerset := by
  classical
  refine Finset.filter_eq_self.mpr ?_
  intro d hd
  exact le_trans (Finset.card_le_card (Finset.mem_powerset.mp hd))
    (residuePrimeSet_card_sqrt_le_canonicalK n hn)

/-- The canonical-depth coprime local-density sum is already untruncated. -/
theorem residueDoubleDivisorCoprimeLocalDensitySumAtSqrt_eq_full
    (n : ℕ) (hn : 16 ≤ n) :
    residueDoubleDivisorCoprimeLocalDensitySumAtSqrt n =
      residueDoubleDivisorCoprimeLocalDensityFullSumAtSqrt n := by
  classical
  have hfilter := residuePrimeSet_powerset_filter_card_le_canonicalK n hn
  have hfilter' :
      (residuePrimeSet (Nat.sqrt n)).powerset.filter
          (fun d => d.card ≤ 2 * n)
        = (residuePrimeSet (Nat.sqrt n)).powerset := by
    simpa [canonicalK] using hfilter
  unfold residueDoubleDivisorCoprimeLocalDensitySumAtSqrt
    residueDoubleDivisorCoprimeLocalDensitySum
    residueDoubleDivisorCoprimeLocalDensityFullSumAtSqrt
    residueDoubleDivisorCoprimeLocalDensityFullSum
  simp [canonicalK]
  refine Finset.sum_congr hfilter' ?_
  intro d₁ _hd₁
  refine Finset.sum_congr hfilter' ?_
  intro d₂ _hd₂
  rfl

/-- The canonical-depth overlap local-density sum is already untruncated. -/
theorem residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt_eq_full
    (n : ℕ) (hn : 16 ≤ n) :
    residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt n =
      residueDoubleDivisorNonCoprimeLocalDensityFullSumAtSqrt n := by
  classical
  have hfilter := residuePrimeSet_powerset_filter_card_le_canonicalK n hn
  have hfilter' :
      (residuePrimeSet (Nat.sqrt n)).powerset.filter
          (fun d => d.card ≤ 2 * n)
        = (residuePrimeSet (Nat.sqrt n)).powerset := by
    simpa [canonicalK] using hfilter
  unfold residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt
    residueDoubleDivisorNonCoprimeLocalDensitySum
    residueDoubleDivisorNonCoprimeLocalDensityFullSumAtSqrt
    residueDoubleDivisorNonCoprimeLocalDensityFullSum
  simp [canonicalK]
  refine Finset.sum_congr hfilter' ?_
  intro d₁ _hd₁
  refine Finset.sum_congr hfilter' ?_
  intro d₂ _hd₂
  rfl

/-- The untruncated split Euler residual implies the split Euler residual. -/
theorem residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
    (hFull : ResidueCoprimeSplitFullLocalDensityEulerAtSqrt) :
    ResidueCoprimeSplitLocalDensityEulerAtSqrt := by
  intro n hn
  rw [residueDoubleDivisorCoprimeLocalDensitySumAtSqrt_eq_full n hn,
    residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt_eq_full n hn]
  exact hFull n hn

/-- Split count-to-density plus the untruncated split Euler residual close the
active coprime/non-coprime worker target. -/
theorem residueCoprimeSplitCanonicalAtSqrtBound_of_count_and_fullEuler
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hFull : ResidueCoprimeSplitFullLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound :=
  residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity hCount
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_full hFull)

/-- Split count-to-density plus the untruncated split Euler residual close the
strict residue canonical kernel. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_count_and_fullEuler
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hFull : ResidueCoprimeSplitFullLocalDensityEulerAtSqrt) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_splitLocalDensity hCount
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_full hFull)

/-- Final K-Goldbach bridge from split count-to-density, untruncated split
Euler, and any supported counting input. -/
theorem pathC_kGoldbach_of_residueFullSplitDensity_and_countingInput
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hFull : ResidueCoprimeSplitFullLocalDensityEulerAtSqrt)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCoprimeSplitDensity_and_countingInput hCount
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_full hFull) hCounting

end PathCResidueSplitLocalDensityDepth
end Gdbh

#print axioms
  Gdbh.PathCResidueSplitLocalDensityDepth.residuePrimeSet_card_sqrt_le_canonicalK
#print axioms
  Gdbh.PathCResidueSplitLocalDensityDepth.residueDoubleDivisorCoprimeLocalDensitySumAtSqrt_eq_full
#print axioms
  Gdbh.PathCResidueSplitLocalDensityDepth.residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
#print axioms
  Gdbh.PathCResidueSplitLocalDensityDepth.residueCoprimeSplitCanonicalAtSqrtBound_of_count_and_fullEuler
#print axioms
  Gdbh.PathCResidueSplitLocalDensityDepth.pathC_kGoldbach_of_residueFullSplitDensity_and_countingInput
