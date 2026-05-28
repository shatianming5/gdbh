/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderCoprimeSplit
import Gdbh.PathC_ResiduePrimeSetProductSupport
import Mathlib.Tactic.Ring

/-!
# Path C -- intersection support for the shared-prime residue remainder

Round 77 rewrites the non-coprime compatible remainder from a product-gcd
condition into explicit intersection language.  For products of subsets of
`residuePrimeSet z`, non-coprimality is exactly nonempty intersection, and
compatibility is divisibility by the product over that intersection.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderIntersectionSplit

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResiduePrimeSetProductSupport
  (residuePrimeSubset_coprime_iff_inter_eq_empty
   residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairCountingRemainder)
open Gdbh.PathCResidueRemainderCompatibleSupport
  (residueCompatiblePairCountingRemainder)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually
   ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
   ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter
   ResidueNonCoprimeCompatibleRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderCoprimeSplit_and_countingInput
   residueDoubleDivisorNonCoprimeCompatibleRemainderSum
   residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt
   residueNonCoprimeCompatiblePairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pair-level intersection support -/

/-- The shared-prime branch of the compatible pair remainder, written in
intersection language. -/
noncomputable def residueSharedPrimeIntersectionPairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if d1 ∩ d2 = ∅ then
    0
  else if (d1 ∩ d2).prod id ∣ n then
    residuePairCountingRemainder n d1 d2
  else
    0

/-- On residue-prime subsets, the non-coprime compatible pair remainder is
the shared-prime intersection branch. -/
theorem residueNonCoprimeCompatiblePairCountingRemainder_eq_sharedPrimeIntersection
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z) :
    residueNonCoprimeCompatiblePairCountingRemainder n d1 d2 =
      residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 := by
  classical
  have hgcd_empty :
      Nat.gcd (d1.prod id) (d2.prod id) = 1 ↔ d1 ∩ d2 = ∅ := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact residuePrimeSubset_coprime_iff_inter_eq_empty hd1 hd2
  have hdiv_inter :
      Nat.gcd (d1.prod id) (d2.prod id) ∣ n ↔
        (d1 ∩ d2).prod id ∣ n :=
    residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd hd1 hd2 n
  unfold residueNonCoprimeCompatiblePairCountingRemainder
    residueSharedPrimeIntersectionPairCountingRemainder
    residueCompatiblePairCountingRemainder
  by_cases hinter : d1 ∩ d2 = ∅
  · have hgcd : Nat.gcd (d1.prod id) (d2.prod id) = 1 :=
      hgcd_empty.mpr hinter
    have hgcd' : (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) = 1 := by
      simpa using hgcd
    simp [hinter, hgcd']
  · have hgcd_ne : Nat.gcd (d1.prod id) (d2.prod id) ≠ 1 := by
      intro hgcd
      exact hinter (hgcd_empty.mp hgcd)
    have hgcd_ne' : ¬ (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) = 1 := by
      simpa using hgcd_ne
    by_cases hdiv : Nat.gcd (d1.prod id) (d2.prod id) ∣ n
    · have hinter_div : (d1 ∩ d2).prod id ∣ n := hdiv_inter.mp hdiv
      have hdiv' : (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) ∣ n := by
        simpa using hdiv
      have hinter_div' : (∏ x ∈ d1 ∩ d2, x) ∣ n := by
        simpa using hinter_div
      simp [hinter, hgcd_ne', hdiv', hinter_div']
    · have hinter_not_div : ¬ (d1 ∩ d2).prod id ∣ n := by
        intro h
        exact hdiv (hdiv_inter.mpr h)
      have hdiv' : ¬ (∏ x ∈ d1, x).gcd (∏ x ∈ d2, x) ∣ n := by
        simpa using hdiv
      have hinter_not_div' : ¬ (∏ x ∈ d1 ∩ d2, x) ∣ n := by
        simpa using hinter_not_div
      simp [hinter, hgcd_ne', hdiv', hinter_not_div']

/-- The shared-prime branch vanishes on disjoint divisor supports. -/
theorem residueSharedPrimeIntersectionPairCountingRemainder_eq_zero_of_inter_empty
    (n : ℕ) {d1 d2 : Finset ℕ} (hinter : d1 ∩ d2 = ∅) :
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 = 0 := by
  simp [residueSharedPrimeIntersectionPairCountingRemainder, hinter]

/-- On nonempty shared support and compatible intersection product, the
shared-prime branch is the original pair remainder. -/
theorem residueSharedPrimeIntersectionPairCountingRemainder_eq_of_inter_dvd
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hinter : d1 ∩ d2 ≠ ∅) (hdiv : (d1 ∩ d2).prod id ∣ n) :
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 =
      residuePairCountingRemainder n d1 d2 := by
  have hdiv' : (∏ x ∈ d1 ∩ d2, x) ∣ n := by
    simpa using hdiv
  simp [residueSharedPrimeIntersectionPairCountingRemainder, hinter, hdiv']

/-! ## Sum-level intersection support -/

/-- The shared-prime intersection version of the compatible signed remainder
sum. -/
noncomputable def residueDoubleDivisorSharedPrimeIntersectionRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueSharedPrimeIntersectionPairCountingRemainder n d1 d2

/-- At-sqrt shared-prime intersection signed remainder. -/
noncomputable def residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeIntersectionRemainderSum n (Nat.sqrt n)
    (canonicalK n)

/-- The Round 75 non-coprime compatible remainder is the shared-prime
intersection remainder. -/
theorem residueDoubleDivisorNonCoprimeCompatibleRemainderSum_eq_sharedPrimeIntersection
    (n z k : ℕ) :
    residueDoubleDivisorNonCoprimeCompatibleRemainderSum n z k =
      residueDoubleDivisorSharedPrimeIntersectionRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorNonCoprimeCompatibleRemainderSum
    residueDoubleDivisorSharedPrimeIntersectionRemainderSum
  refine Finset.sum_congr rfl ?_
  intro d1 hd1
  have hd1_sub : d1 ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd1).1
  refine Finset.sum_congr rfl ?_
  intro d2 hd2
  have hd2_sub : d2 ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd2).1
  rw [residueNonCoprimeCompatiblePairCountingRemainder_eq_sharedPrimeIntersection
    hd1_sub hd2_sub]

/-- At-sqrt version of the shared-prime intersection equality. -/
theorem
    residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt_eq_sharedPrimeIntersection
    (n : ℕ) :
    residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt n =
      residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt,
    residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt] using
      residueDoubleDivisorNonCoprimeCompatibleRemainderSum_eq_sharedPrimeIntersection
        n (Nat.sqrt n) (canonicalK n)

/-! ## Intersection worker and recombination -/

/-- Large-range upper bound for the shared-prime intersection signed
remainder. -/
noncomputable def ResidueSharedPrimeIntersectionRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual shared-prime intersection signed-remainder upper worker. -/
noncomputable def
    ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeIntersectionRemainderLogSquaredUpperAfter N A

/-- Bounding the shared-prime intersection remainder bounds the Round 75
non-coprime compatible remainder. -/
theorem residueNonCoprimeCompatibleRemainderLogSquaredUpperAfter_of_sharedPrimeIntersection
    {N : ℕ} {A : ℝ}
    (hShared :
      ResidueSharedPrimeIntersectionRemainderLogSquaredUpperAfter N A) :
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperAfter N A := by
  rcases hShared with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [residueDoubleDivisorNonCoprimeCompatibleRemainderSumAtSqrt_eq_sharedPrimeIntersection]
  exact hbd n hn hsqrt

/-- Eventual shared-prime intersection upper worker implies the Round 75
non-coprime compatible upper worker. -/
theorem residueNonCoprimeCompatibleRemainderLogSquaredUpperEventually_of_sharedPrimeIntersection
    (hShared :
      ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually) :
    ResidueNonCoprimeCompatibleRemainderLogSquaredUpperEventually := by
  rcases hShared with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueNonCoprimeCompatibleRemainderLogSquaredUpperAfter_of_sharedPrimeIntersection
      hN⟩

/-- Bundled coprime plus shared-prime intersection worker. -/
noncomputable def
    ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually

/-- The intersection split supplies the Round 75 coprime/non-coprime split
worker. -/
theorem residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
    (hSplit :
      ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hShared⟩
  exact ⟨hCop,
    residueNonCoprimeCompatibleRemainderLogSquaredUpperEventually_of_sharedPrimeIntersection
      hShared⟩

/-- Final Path C adapter from the coprime/intersection split and any supported
counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderIntersectionSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderCoprimeSplit_and_countingInput
    (residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
      hSplit)
    hCounting

end PathCResidueRemainderIntersectionSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderIntersectionSplit.residueNonCoprimeCompatiblePairCountingRemainder_eq_sharedPrimeIntersection
#print axioms
  Gdbh.PathCResidueRemainderIntersectionSplit.residueDoubleDivisorNonCoprimeCompatibleRemainderSum_eq_sharedPrimeIntersection
#print axioms
  Gdbh.PathCResidueRemainderIntersectionSplit.residueNonCoprimeCompatibleRemainderLogSquaredUpperAfter_of_sharedPrimeIntersection
#print axioms
  Gdbh.PathCResidueRemainderIntersectionSplit.residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
#print axioms
  Gdbh.PathCResidueRemainderIntersectionSplit.pathC_kGoldbach_of_compatibleRemainderIntersectionSplit_and_countingInput
