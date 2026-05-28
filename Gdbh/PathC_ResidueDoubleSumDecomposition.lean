/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex
-/
import Gdbh.PathC_ResidueBonferroniKernelDecomposition
import Gdbh.PathC_PairedBonferroniSumRearrange

/-!
# Path C -- residue double-sum decomposition

`PathC_ResidueBonferroniKernelDecomposition` already closes the indicator
layer and reduces the strict residue canonical kernel to
`ResidueDoubleSumCanonicalAtSqrtBound`, a bound on the summed paired
Bonferroni majorant.

This file peels off the next mechanical layer.  The existing closed
rearrangement theorem turns that `m`-sum of products into the explicit
double-divisor counting sum.  The remaining named work item is therefore
`ResidueDoubleDivisorCanonicalAtSqrtBound`.
-/

namespace Gdbh
namespace PathCResidueDoubleSumDecomposition

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel
   pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail
   residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition
  (ResidueDoubleSumCanonicalAtSqrtBound residuePairedBonferroniMajorant
   residuePrimeSet residuePrimeSet_prime truncatedMoebiusDivisorSum
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleSum)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The explicit double-divisor counting sum obtained after rearranging the
summed paired Bonferroni majorant. -/
noncomputable def residueDoubleDivisorCountingSum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        ((Finset.Icc 1 (n - 1)).filter
          (fun m => (d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m))).card

/-- The final-threshold, canonical-depth double-divisor counting sum. -/
noncomputable def residueDoubleDivisorCountingSumAtSqrt (n : ℕ) : ℝ :=
  residueDoubleDivisorCountingSum n (Nat.sqrt n) (canonicalK n)

/-- The remaining strict sub-Prop after the closed indicator and rearrangement
layers: bound the explicit double-divisor counting sum by the actual residue
main factor and the canonical tail. -/
def ResidueDoubleDivisorCanonicalAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCountingSumAtSqrt n
      ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- The closed rearrangement layer: the `m`-sum of paired Bonferroni
majorants is exactly the explicit double-divisor counting sum. -/
theorem residueMajorantSum_eq_doubleDivisorCountingSum
    {n z : ℕ} (hn : 2 ≤ n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
        residuePairedBonferroniMajorant n z m)
      = residueDoubleDivisorCountingSum n z (canonicalK n) := by
  classical
  have hP : ∀ p ∈ residuePrimeSet z, Nat.Prime p := by
    intro p hp
    exact residuePrimeSet_prime hp
  simpa [residuePairedBonferroniMajorant, truncatedMoebiusDivisorSum,
    residueDoubleDivisorCountingSum, canonicalK] using
      Gdbh.PathCPairedBonferroniSumRearrange.pairedBonferroniSumRearrange_holds
        (residuePrimeSet z) n (canonicalK n) hn hP

/-- At the final threshold and canonical depth, the rearranged sum is
`residueDoubleDivisorCountingSumAtSqrt`. -/
theorem residueMajorantSumAtSqrt_eq_doubleDivisorCountingSumAtSqrt
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
        residuePairedBonferroniMajorant n (Nat.sqrt n) m)
      = residueDoubleDivisorCountingSumAtSqrt n := by
  simpa [residueDoubleDivisorCountingSumAtSqrt] using
    (residueMajorantSum_eq_doubleDivisorCountingSum
      (n := n) (z := Nat.sqrt n) hn)

/-- The explicit double-divisor residual implies the previous double-sum
residual. -/
theorem residueDoubleSumCanonicalAtSqrtBound_of_doubleDivisor
    (hDivisor : ResidueDoubleDivisorCanonicalAtSqrtBound) :
    ResidueDoubleSumCanonicalAtSqrtBound := by
  intro n hn
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ 16).trans hn
  rw [residueMajorantSumAtSqrt_eq_doubleDivisorCountingSumAtSqrt hn2]
  exact hDivisor n hn

/-- The explicit double-divisor residual closes the strict residue canonical
kernel through the already-closed indicator layer. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
    (hDivisor : ResidueDoubleDivisorCanonicalAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleSum
    (residueDoubleSumCanonicalAtSqrtBound_of_doubleDivisor hDivisor)

/-- Final K-Goldbach bridge from the explicit double-divisor residual and any
supported counting input. -/
theorem pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput
    (hDivisor : ResidueDoubleDivisorCanonicalAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail
    (brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor hDivisor)
    hCounting

end PathCResidueDoubleSumDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueDoubleSumDecomposition.residueMajorantSum_eq_doubleDivisorCountingSum
#print axioms
  Gdbh.PathCResidueDoubleSumDecomposition.residueDoubleSumCanonicalAtSqrtBound_of_doubleDivisor
#print axioms
  Gdbh.PathCResidueDoubleSumDecomposition.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
#print axioms
  Gdbh.PathCResidueDoubleSumDecomposition.pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput
