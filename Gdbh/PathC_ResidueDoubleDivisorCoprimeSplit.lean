/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueDoubleSumDecomposition

/-!
# Path C -- residue double-divisor coprime split

`PathC_ResidueDoubleSumDecomposition` reduces the residue Bonferroni
kernel to an explicit double-divisor counting sum.  This file splits that
sum into the part where the two divisor products are coprime and the
overlap part where they are not.

This is the next safe CRT-facing layer.  The coprime part is the natural
input for Chinese-remainder counting, while the non-coprime part records
the shared-prime overlap explicitly instead of hiding it inside a false
standalone endpoint-error estimate.
-/

namespace Gdbh
namespace PathCResidueDoubleDivisorCoprimeSplit

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleSumDecomposition
  (ResidueDoubleDivisorCanonicalAtSqrtBound
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
   pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput
   residueDoubleDivisorCountingSum residueDoubleDivisorCountingSumAtSqrt)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The summand attached to one pair of truncated divisor sets. -/
noncomputable def residueDoubleDivisorPairWeight
    (n : ℕ) (d₁ d₂ : Finset ℕ) : ℝ :=
  (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
    (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
    ((Finset.Icc 1 (n - 1)).filter
      (fun m => (d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m))).card

/-- The explicit double-divisor sum restricted to coprime divisor products. -/
noncomputable def residueDoubleDivisorCoprimeCountingSum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        residueDoubleDivisorPairWeight n d₁ d₂
      else 0

/-- The explicit double-divisor sum over pairs with shared divisor-product
content. -/
noncomputable def residueDoubleDivisorNonCoprimeCountingSum
    (n z k : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d₂ ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      if Nat.Coprime (d₁.prod id) (d₂.prod id) then
        0
      else residueDoubleDivisorPairWeight n d₁ d₂

/-- The coprime divisor-product part at the final threshold and canonical
depth. -/
noncomputable def residueDoubleDivisorCoprimeCountingSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorCoprimeCountingSum n (Nat.sqrt n) (canonicalK n)

/-- The non-coprime divisor-product part at the final threshold and canonical
depth. -/
noncomputable def residueDoubleDivisorNonCoprimeCountingSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorNonCoprimeCountingSum n (Nat.sqrt n) (canonicalK n)

/-- The next strict worker target after the coprime/non-coprime partition. -/
def ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorCoprimeCountingSumAtSqrt n
      + residueDoubleDivisorNonCoprimeCountingSumAtSqrt n
        ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- The full explicit double-divisor sum is the sum of its coprime and
non-coprime divisor-product parts. -/
theorem residueDoubleDivisorCountingSum_eq_coprime_add_nonCoprime
    (n z k : ℕ) :
    residueDoubleDivisorCountingSum n z k =
      residueDoubleDivisorCoprimeCountingSum n z k
        + residueDoubleDivisorNonCoprimeCountingSum n z k := by
  classical
  unfold residueDoubleDivisorCountingSum
    residueDoubleDivisorCoprimeCountingSum
    residueDoubleDivisorNonCoprimeCountingSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d₁ hd₁
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d₂ hd₂
  change residueDoubleDivisorPairWeight n d₁ d₂ =
    (if (d₁.prod id).Coprime (d₂.prod id) then
      residueDoubleDivisorPairWeight n d₁ d₂
    else 0) +
    if (d₁.prod id).Coprime (d₂.prod id) then
      0
    else residueDoubleDivisorPairWeight n d₁ d₂
  by_cases hcop : (d₁.prod id).Coprime (d₂.prod id)
  · rw [if_pos hcop, if_pos hcop]
    ring
  · rw [if_neg hcop, if_neg hcop]
    ring

/-- At the final threshold, the explicit double-divisor sum is exactly the
coprime part plus the shared-prime overlap part. -/
theorem residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime
    (n : ℕ) :
    residueDoubleDivisorCountingSumAtSqrt n =
      residueDoubleDivisorCoprimeCountingSumAtSqrt n
        + residueDoubleDivisorNonCoprimeCountingSumAtSqrt n := by
  simpa [residueDoubleDivisorCountingSumAtSqrt,
    residueDoubleDivisorCoprimeCountingSumAtSqrt,
    residueDoubleDivisorNonCoprimeCountingSumAtSqrt] using
      residueDoubleDivisorCountingSum_eq_coprime_add_nonCoprime
        n (Nat.sqrt n) (canonicalK n)

/-- The coprime/non-coprime residual implies the previous explicit
double-divisor residual. -/
theorem residueDoubleDivisorCanonicalAtSqrtBound_of_coprimeSplit
    (hSplit : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound) :
    ResidueDoubleDivisorCanonicalAtSqrtBound := by
  intro n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_coprime_add_nonCoprime]
  exact hSplit n hn

/-- The coprime/non-coprime residual closes the strict residue canonical
kernel through the already-closed double-divisor bridge. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_coprimeSplit
    (hSplit : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
    (residueDoubleDivisorCanonicalAtSqrtBound_of_coprimeSplit hSplit)

/-- Final K-Goldbach bridge from the coprime/non-coprime residual and any
supported counting input. -/
theorem pathC_kGoldbach_of_residueCoprimeSplitCanonical_and_countingInput
    (hSplit : ResidueDoubleDivisorCoprimeSplitCanonicalAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput
    (residueDoubleDivisorCanonicalAtSqrtBound_of_coprimeSplit hSplit)
    hCounting

end PathCResidueDoubleDivisorCoprimeSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueDoubleDivisorCoprimeSplit.residueDoubleDivisorCountingSum_eq_coprime_add_nonCoprime
#print axioms
  Gdbh.PathCResidueDoubleDivisorCoprimeSplit.residueDoubleDivisorCanonicalAtSqrtBound_of_coprimeSplit
#print axioms
  Gdbh.PathCResidueDoubleDivisorCoprimeSplit.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_coprimeSplit
#print axioms
  Gdbh.PathCResidueDoubleDivisorCoprimeSplit.pathC_kGoldbach_of_residueCoprimeSplitCanonical_and_countingInput
