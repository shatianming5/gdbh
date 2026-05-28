/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderCompatibleSupport
import Mathlib.Tactic.Ring

/-!
# Path C -- coprime split for the compatible residue remainder

Round 74 reduced the active signed-remainder upper worker to the
gcd-compatible support.  This file splits that compatible-support sum into
coprime and non-coprime divisor-pair parts.

The split is algebraic.  It does not assert cancellation or a new analytic
estimate; it exposes two smaller log-squared upper workers and proves that
they recombine into the Round 74 worker.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderCoprimeSplit

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderCompatibleSupport
  (ResidueCompatibleRemainderLogSquaredUpperAfter
   ResidueCompatibleRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderLogSquaredUpperEventually_and_countingInput
   residueCompatiblePairCountingRemainder
   residueDoubleDivisorCompatibleRemainderSum
   residueDoubleDivisorCompatibleRemainderSumAtSqrt)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pair-level coprime split -/

/-- Compatible pair remainder restricted to coprime divisor products. -/
noncomputable def residueCoprimeCompatiblePairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if Nat.gcd (d1.prod id) (d2.prod id) = 1 then
    residueCompatiblePairCountingRemainder n d1 d2
  else
    0

/-- Compatible pair remainder restricted to non-coprime divisor products. -/
noncomputable def residueNonCoprimeCompatiblePairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if Nat.gcd (d1.prod id) (d2.prod id) = 1 then
    0
  else
    residueCompatiblePairCountingRemainder n d1 d2

/-- The compatible pair remainder is the sum of its coprime and non-coprime
parts. -/
theorem residueCompatiblePairCountingRemainder_eq_coprime_add_nonCoprime
    (n : ℕ) (d1 d2 : Finset ℕ) :
    residueCompatiblePairCountingRemainder n d1 d2 =
      residueCoprimeCompatiblePairCountingRemainder n d1 d2 +
        residueNonCoprimeCompatiblePairCountingRemainder n d1 d2 := by
  unfold residueCoprimeCompatiblePairCountingRemainder
    residueNonCoprimeCompatiblePairCountingRemainder
  by_cases hcop : Nat.gcd (d1.prod id) (d2.prod id) = 1
  · have hcop' :
        (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) = 1 := by
      simpa using hcop
    simp [hcop']
  · have hcop' :
        ¬ (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) = 1 := by
      simpa using hcop
    simp [hcop']

/-! ## Sum-level coprime split -/

/-- Coprime part of the compatible signed remainder sum. -/
noncomputable def residueDoubleDivisorCoprimeCompatibleRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueCoprimeCompatiblePairCountingRemainder n d1 d2

/-- Non-coprime part of the compatible signed remainder sum. -/
noncomputable def residueDoubleDivisorNonCoprimeCompatibleRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueNonCoprimeCompatiblePairCountingRemainder n d1 d2

/-- At-sqrt coprime compatible signed remainder. -/
noncomputable def residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorCoprimeCompatibleRemainderSum n (Nat.sqrt n)
    (canonicalK n)

/-- At-sqrt non-coprime compatible signed remainder. -/
noncomputable def residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorNonCoprimeCompatibleRemainderSum n (Nat.sqrt n)
    (canonicalK n)

/-- The compatible signed remainder sum is the sum of its coprime and
non-coprime parts. -/
theorem residueDoubleDivisorCompatibleRemainderSum_eq_coprime_add_nonCoprime
    (n z k : ℕ) :
    residueDoubleDivisorCompatibleRemainderSum n z k =
      residueDoubleDivisorCoprimeCompatibleRemainderSum n z k +
        residueDoubleDivisorNonCoprimeCompatibleRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorCompatibleRemainderSum
    residueDoubleDivisorCoprimeCompatibleRemainderSum
    residueDoubleDivisorNonCoprimeCompatibleRemainderSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d1 _hd1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d2 _hd2
  rw [residueCompatiblePairCountingRemainder_eq_coprime_add_nonCoprime]
  ring

/-- At-sqrt version of the coprime/non-coprime split. -/
theorem residueDoubleDivisorCompatibleRemainderSumAtSqrt_eq_coprime_add_nonCoprime
    (n : ℕ) :
    residueDoubleDivisorCompatibleRemainderSumAtSqrt n =
      residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt n +
        residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorCompatibleRemainderSumAtSqrt,
    residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt,
    residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt] using
      residueDoubleDivisorCompatibleRemainderSum_eq_coprime_add_nonCoprime
        n (Nat.sqrt n) (canonicalK n)

/-! ## Split log-squared upper workers -/

/-- Large-range upper bound for the coprime compatible signed remainder. -/
noncomputable def ResidueCoprimeCompatibleRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Large-range upper bound for the non-coprime compatible signed remainder. -/
noncomputable def ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual coprime compatible signed-remainder upper worker. -/
noncomputable def
    ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueCoprimeCompatibleRemainderLogSquaredUpperAfter N A

/-- Eventual non-coprime compatible signed-remainder upper worker. -/
noncomputable def
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter N A

/-- Bundled eventual coprime/non-coprime split worker. -/
noncomputable def
    ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually : Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperEventually

/-! ## Recombination bridge -/

/-- Raising the threshold preserves the coprime upper worker. -/
theorem residueCoprimeCompatibleRemainderLogSquaredUpperAfter_mono
    {N M : ℕ} {A : ℝ} (hNM : N ≤ M)
    (h : ResidueCoprimeCompatibleRemainderLogSquaredUpperAfter N A) :
    ResidueCoprimeCompatibleRemainderLogSquaredUpperAfter M A := by
  rcases h with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact hbd n hn (by omega)

/-- Raising the threshold preserves the non-coprime upper worker. -/
theorem residueNonCoprimeCompatibleRemainderLogSquaredUpperAfter_mono
    {N M : ℕ} {A : ℝ} (hNM : N ≤ M)
    (h : ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter N A) :
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter M A := by
  rcases h with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact hbd n hn (by omega)

/-- Same-threshold coprime and non-coprime upper bounds imply the compatible
upper bound. -/
theorem residueCompatibleRemainderLogSquaredUpperAfter_of_coprime_nonCoprime
    {N : ℕ} {A B : ℝ}
    (hCop :
      ResidueCoprimeCompatibleRemainderLogSquaredUpperAfter N A)
    (hNon :
      ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter N B) :
    ResidueCompatibleRemainderLogSquaredUpperAfter N (A + B) := by
  rcases hCop with ⟨hA, hCopBd⟩
  rcases hNon with ⟨hB, hNonBd⟩
  refine ⟨by positivity, ?_⟩
  intro n hn hsqrt
  have hCop' := hCopBd n hn hsqrt
  have hNon' := hNonBd n hn hsqrt
  rw [residueDoubleDivisorCompatibleRemainderSumAtSqrt_eq_coprime_add_nonCoprime]
  calc
    |residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt n +
        residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt n|
        ≤ |residueDoubleDivisorCoprimeCompatibleRemainderSumAtSqrt n| +
            |residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt n| :=
          abs_add_le _ _
    _ ≤ A * (n : ℝ) / (Real.log (n : ℝ))^2 +
          B * (n : ℝ) / (Real.log (n : ℝ))^2 :=
          add_le_add hCop' hNon'
    _ = (A + B) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
          ring

/-- Eventual coprime/non-coprime split workers imply the Round 74 compatible
upper worker. -/
theorem residueCompatibleRemainderLogSquaredUpperEventually_of_coprimeSplit
    (hSplit :
      ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderLogSquaredUpperEventually := by
  rcases hSplit with ⟨⟨NC, A, hCop⟩, ⟨NN, B, hNon⟩⟩
  refine ⟨max NC NN, A + B, ?_⟩
  exact
    residueCompatibleRemainderLogSquaredUpperAfter_of_coprime_nonCoprime
      (residueCoprimeCompatibleRemainderLogSquaredUpperAfter_mono
        (le_max_left NC NN) hCop)
      (residueNonCoprimeCompatibleRemainderLogSquaredUpperAfter_mono
        (le_max_right NC NN) hNon)

/-- Final Path C adapter from the coprime/non-coprime compatible upper split
and any supported counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderCoprimeSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderLogSquaredUpperEventually_and_countingInput
    (residueCompatibleRemainderLogSquaredUpperEventually_of_coprimeSplit
      hSplit)
    hCounting

end PathCResidueRemainderCoprimeSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderCoprimeSplit.residueCompatiblePairCountingRemainder_eq_coprime_add_nonCoprime
#print axioms
  Gdbh.PathCResidueRemainderCoprimeSplit.residueDoubleDivisorCompatibleRemainderSum_eq_coprime_add_nonCoprime
#print axioms
  Gdbh.PathCResidueRemainderCoprimeSplit.residueCompatibleRemainderLogSquaredUpperAfter_of_coprime_nonCoprime
#print axioms
  Gdbh.PathCResidueRemainderCoprimeSplit.residueCompatibleRemainderLogSquaredUpperEventually_of_coprimeSplit
#print axioms
  Gdbh.PathCResidueRemainderCoprimeSplit.pathC_kGoldbach_of_compatibleRemainderCoprimeSplit_and_countingInput
