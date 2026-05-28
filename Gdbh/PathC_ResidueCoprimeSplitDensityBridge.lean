/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueDoubleDivisorCoprimeSplit
import Gdbh.PathC_ResidueDoubleDivisorDensityDecomposition

/-!
# Path C -- coprime split to local-density bridge

Round 8 split the explicit double-divisor count into coprime divisor-product
pairs and shared-prime overlap pairs.  The existing density decomposition
compares the unsplit count to a compatible local-density sum.

This file aligns those two layers.  It splits the compatible local-density
sum into the same coprime and overlap parts, then exposes the current worker
target as two smaller residuals:

* a split count-to-density estimate;
* a split local-density-to-residue-main-factor identity.
-/

namespace Gdbh
namespace PathCResidueCoprimeSplitDensityBridge

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorCoprimeSplit
  (ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_coprimeSplit
   pathC_kGoldbach_of_residueCoprimeSplitCanonical_and_countingInput
   residueDoubleDivisorCoprimeCountingSumAtSqrt
   residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime
   residueDoubleDivisorNonCoprimeCountingSumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound
   ResidueDoubleDivisorLocalDensityEulerAtSqrt
   ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt
   residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch
   residueDoubleDivisorLocalDensitySum residueDoubleDivisorLocalDensitySumAtSqrt
   residuePairCompatibilityWeight)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- One local-density summand for a pair of truncated divisor sets. -/
noncomputable def residueDoubleDivisorLocalDensityPairWeight
    (n : ℕ) (d₁ d₂ : Finset ℕ) : ℝ :=
  (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
    (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
    residuePairCompatibilityWeight n d₁ d₂

/-- The compatible local-density sum restricted to coprime divisor products. -/
noncomputable def residueDoubleDivisorCoprimeLocalDensitySum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        residueDoubleDivisorLocalDensityPairWeight n d₁ d₂
      else 0

/-- The compatible local-density sum over shared-prime overlap pairs. -/
noncomputable def residueDoubleDivisorNonCoprimeLocalDensitySum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        0
      else residueDoubleDivisorLocalDensityPairWeight n d₁ d₂

/-- The coprime local-density part at the final threshold and canonical
depth. -/
noncomputable def residueDoubleDivisorCoprimeLocalDensitySumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorCoprimeLocalDensitySum n (Nat.sqrt n) (canonicalK n)

/-- The shared-prime overlap local-density part at the final threshold and
canonical depth. -/
noncomputable def residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorNonCoprimeLocalDensitySum n (Nat.sqrt n) (canonicalK n)

/-- Split count-to-density residual.  This is the CRT/counting task in the
same coprime/non-coprime coordinates as the active Round 8 residual. -/
def ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCoprimeCountingSumAtSqrt n
      + residueDoubleDivisorNonCoprimeCountingSumAtSqrt n
        ≤ (n : ℝ) *
            (residueDoubleDivisorCoprimeLocalDensitySumAtSqrt n
              + residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- Split local-density algebra residual. -/
def ResidueCoprimeSplitLocalDensityEulerAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCoprimeLocalDensitySumAtSqrt n
      + residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt n
        = goldbachResidueMainFactor n (Nat.sqrt n)

/-- The unsplit compatible local-density sum is exactly its coprime part plus
its shared-prime overlap part. -/
theorem residueDoubleDivisorLocalDensitySum_eq_coprime_add_nonCoprime
    (n z k : ℕ) :
    residueDoubleDivisorLocalDensitySum n z k =
      residueDoubleDivisorCoprimeLocalDensitySum n z k
        + residueDoubleDivisorNonCoprimeLocalDensitySum n z k := by
  classical
  unfold residueDoubleDivisorLocalDensitySum
    residueDoubleDivisorCoprimeLocalDensitySum
    residueDoubleDivisorNonCoprimeLocalDensitySum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d₁ _hd₁
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d₂ _hd₂
  change residueDoubleDivisorLocalDensityPairWeight n d₁ d₂ =
    (if (d₁.prod id).Coprime (d₂.prod id) then
      residueDoubleDivisorLocalDensityPairWeight n d₁ d₂
    else 0) +
    if (d₁.prod id).Coprime (d₂.prod id) then
      0
    else residueDoubleDivisorLocalDensityPairWeight n d₁ d₂
  by_cases hcop : (d₁.prod id).Coprime (d₂.prod id)
  · rw [if_pos hcop, if_pos hcop]
    ring
  · rw [if_neg hcop, if_neg hcop]
    ring

/-- At the final threshold, the unsplit local-density sum is exactly the
coprime part plus the shared-prime overlap part. -/
theorem residueDoubleDivisorLocalDensitySumAtSqrt_eq_coprime_add_nonCoprime
    (n : ℕ) :
    residueDoubleDivisorLocalDensitySumAtSqrt n =
      residueDoubleDivisorCoprimeLocalDensitySumAtSqrt n
        + residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt n := by
  simpa [residueDoubleDivisorLocalDensitySumAtSqrt,
    residueDoubleDivisorCoprimeLocalDensitySumAtSqrt,
    residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt] using
      residueDoubleDivisorLocalDensitySum_eq_coprime_add_nonCoprime
        n (Nat.sqrt n) (canonicalK n)

/-- The split count-to-density residual plus the split local-density algebra
residual imply the active coprime/non-coprime worker target. -/
theorem residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound := by
  intro n hn
  have h := hCount n hn
  rw [hEuler n hn] at h
  exact h

/-- The unsplit count-to-density residual implies the split count-to-density
residual through the two closed partition identities. -/
theorem residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_unsplit
    (hCount : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound := by
  intro n hn
  have h := hCount n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime] at h
  rw [residueDoubleDivisorLocalDensitySumAtSqrt_eq_coprime_add_nonCoprime] at h
  exact h

/-- The unsplit local-density Euler residual implies the split local-density
Euler residual through the closed density partition. -/
theorem residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit
    (hEuler : ResidueDoubleDivisorLocalDensityEulerAtSqrt) :
    ResidueCoprimeSplitLocalDensityEulerAtSqrt := by
  intro n hn
  rw [← residueDoubleDivisorLocalDensitySumAtSqrt_eq_coprime_add_nonCoprime]
  exact hEuler n hn

/-- The more primitive Goldbach-density match residual also implies the split
local-density Euler residual. -/
theorem residueCoprimeSplitLocalDensityEulerAtSqrt_of_goldbachDensityMatch
    (hMatch : ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueCoprimeSplitLocalDensityEulerAtSqrt :=
  residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit
    (residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch hMatch)

/-- Existing unsplit density residuals are enough to close the current
coprime/non-coprime worker target. -/
theorem residueCoprimeSplitCanonicalAtSqrtBound_of_unsplitLocalDensity
    (hCount : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound)
    (hEuler : ResidueDoubleDivisorLocalDensityEulerAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound :=
  residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
    (residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_unsplit hCount)
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit hEuler)

/-- Existing unsplit count residual plus Goldbach-density matching close the
current coprime/non-coprime worker target. -/
theorem residueCoprimeSplitCanonicalAtSqrtBound_of_unsplitCount_and_goldbachDensityMatch
    (hCount : ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound)
    (hMatch : ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound :=
  residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
    (residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_unsplit hCount)
    (residueCoprimeSplitLocalDensityEulerAtSqrt_of_goldbachDensityMatch hMatch)

/-- Final strict residue-kernel bridge from the split density residuals. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_splitLocalDensity
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_coprimeSplit
    (residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
      hCount hEuler)

/-- Final K-Goldbach bridge from the split density residuals and any supported
counting input. -/
theorem pathC_kGoldbach_of_residueCoprimeSplitDensity_and_countingInput
    (hCount : ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hEuler : ResidueCoprimeSplitLocalDensityEulerAtSqrt)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCoprimeSplitCanonical_and_countingInput
    (residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
      hCount hEuler)
    hCounting

end PathCResidueCoprimeSplitDensityBridge
end Gdbh

#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityBridge.residueDoubleDivisorLocalDensitySum_eq_coprime_add_nonCoprime
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityBridge.residueCoprimeSplitCanonicalAtSqrtBound_of_splitLocalDensity
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityBridge.residueCoprimeSplitCanonicalAtSqrtBound_of_unsplitLocalDensity
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityBridge.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_splitLocalDensity
#print axioms
  Gdbh.PathCResidueCoprimeSplitDensityBridge.pathC_kGoldbach_of_residueCoprimeSplitDensity_and_countingInput
