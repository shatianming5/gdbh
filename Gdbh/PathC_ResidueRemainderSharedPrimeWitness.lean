/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderIntersectionSplit
import Gdbh.PathC_ResiduePrimeSetProductSupport

/-!
# Path C -- witness support for the shared-prime residue remainder

Round 78 refines the Round77 shared-prime intersection branch by making the
divisor-of-`n` witness explicit.  If a nonempty product over
`d1 ∩ d2` divides `n`, then every prime in that intersection divides `n`.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderSharedPrimeWitness

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResiduePrimeSetProductSupport
  (residuePrimeSubset_prod_dvd_iff_forall_prime_dvd)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairCountingRemainder)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually
   ResidueSharedPrimeIntersectionRemainderLogSquaredUpperAfter
   ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderIntersectionSplit_and_countingInput
   residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
   residueDoubleDivisorSharedPrimeIntersectionRemainderSum
   residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt
   residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pair-level witness support -/

/-- If the intersection product divides `n`, then every shared residue prime
divides `n`. -/
theorem residueSharedPrimeIntersection_prime_dvd_of_prod_dvd
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z)
    {p : ℕ} (hp : p ∈ d1 ∩ d2)
    (hprod : (d1 ∩ d2).prod id ∣ n) :
    p ∣ n := by
  have hinter_sub : d1 ∩ d2 ⊆ residuePrimeSet z := by
    intro q hq
    exact hd1 (Finset.mem_inter.mp hq).1
  exact
    (residuePrimeSubset_prod_dvd_iff_forall_prime_dvd hinter_sub n).mp
      hprod p hp

/-- The shared-prime branch vanishes if no shared prime divides `n`. -/
theorem residueSharedPrimeIntersectionPairCountingRemainder_eq_zero_of_no_shared_prime_dvd
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z)
    (hno : ∀ p ∈ d1 ∩ d2, ¬ p ∣ n) :
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 = 0 := by
  classical
  by_cases hinter : d1 ∩ d2 = ∅
  · simp [residueSharedPrimeIntersectionPairCountingRemainder, hinter]
  · by_cases hprod : (d1 ∩ d2).prod id ∣ n
    · exfalso
      rcases (d1 ∩ d2).eq_empty_or_nonempty with hEmpty | hNonempty
      · exact hinter hEmpty
      · rcases hNonempty with ⟨p, hp⟩
        exact hno p hp
          (residueSharedPrimeIntersection_prime_dvd_of_prod_dvd
            hd1 hp hprod)
    · have hprod' : ¬ (∏ x ∈ d1 ∩ d2, x) ∣ n := by
        simpa using hprod
      simp [residueSharedPrimeIntersectionPairCountingRemainder, hinter,
        hprod']

/-- The shared-prime branch with an explicit witness-prime support condition. -/
noncomputable def residueSharedPrimeWitnessPairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if ∃ p : ℕ, p ∈ d1 ∩ d2 ∧ p ∣ n then
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2
  else
    0

/-- On residue-prime subsets, the shared-prime intersection branch equals its
witness-supported version. -/
theorem residueSharedPrimeIntersectionPairCountingRemainder_eq_witness
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) :
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 =
      residueSharedPrimeWitnessPairCountingRemainder n d1 d2 := by
  classical
  unfold residueSharedPrimeWitnessPairCountingRemainder
  by_cases hw : ∃ p : ℕ, p ∈ d1 ∩ d2 ∧ p ∣ n
  · have hw' : ∃ p : ℕ, p ∈ d1 ∧ p ∈ d2 ∧ p ∣ n := by
      rcases hw with ⟨p, hp, hpdiv⟩
      exact ⟨p, (Finset.mem_inter.mp hp).1,
        (Finset.mem_inter.mp hp).2, hpdiv⟩
    simp [hw']
  · have hno : ∀ p ∈ d1 ∩ d2, ¬ p ∣ n := by
      intro p hp hpdiv
      exact hw ⟨p, hp, hpdiv⟩
    have hzero :
        residueSharedPrimeIntersectionPairCountingRemainder n d1 d2 = 0 :=
      residueSharedPrimeIntersectionPairCountingRemainder_eq_zero_of_no_shared_prime_dvd
        hd1 hno
    simp [hzero]

/-! ## Sum-level witness support -/

/-- The witness-supported shared-prime signed remainder sum. -/
noncomputable def residueDoubleDivisorSharedPrimeWitnessRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueSharedPrimeWitnessPairCountingRemainder n d1 d2

/-- At-sqrt witness-supported shared-prime signed remainder. -/
noncomputable def residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeWitnessRemainderSum n (Nat.sqrt n)
    (canonicalK n)

/-- The Round77 shared-prime intersection remainder equals its witness-supported
version. -/
theorem residueDoubleDivisorSharedPrimeIntersectionRemainderSum_eq_witness
    (n z k : ℕ) :
    residueDoubleDivisorSharedPrimeIntersectionRemainderSum n z k =
      residueDoubleDivisorSharedPrimeWitnessRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorSharedPrimeIntersectionRemainderSum
    residueDoubleDivisorSharedPrimeWitnessRemainderSum
  refine Finset.sum_congr rfl ?_
  intro d1 hd1
  have hd1_sub : d1 ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd1).1
  refine Finset.sum_congr rfl ?_
  intro d2 _hd2
  rw [residueSharedPrimeIntersectionPairCountingRemainder_eq_witness
    hd1_sub]

/-- At-sqrt version of the witness-supported equality. -/
theorem residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt_eq_witness
    (n : ℕ) :
    residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt n =
      residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt,
    residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt] using
      residueDoubleDivisorSharedPrimeIntersectionRemainderSum_eq_witness
        n (Nat.sqrt n) (canonicalK n)

/-! ## Witness worker and recombination -/

/-- Large-range upper bound for the witness-supported shared-prime remainder. -/
noncomputable def ResidueSharedPrimeWitnessRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual witness-supported shared-prime upper worker. -/
noncomputable def
    ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeWitnessRemainderLogSquaredUpperAfter N A

/-- Bounding the witness-supported shared-prime remainder bounds the Round77
intersection remainder. -/
theorem residueSharedPrimeIntersectionRemainderLogSquaredUpperAfter_of_witness
    {N : ℕ} {A : ℝ}
    (hWitness :
      ResidueSharedPrimeWitnessRemainderLogSquaredUpperAfter N A) :
    ResidueSharedPrimeIntersectionRemainderLogSquaredUpperAfter N A := by
  rcases hWitness with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [residueDoubleDivisorSharedPrimeIntersectionRemainderSumAtSqrt_eq_witness]
  exact hbd n hn hsqrt

/-- Eventual witness-supported shared-prime upper worker implies the Round77
intersection upper worker. -/
theorem residueSharedPrimeIntersectionRemainderLogSquaredUpperEventually_of_witness
    (hWitness :
      ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually) :
    ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually := by
  rcases hWitness with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueSharedPrimeIntersectionRemainderLogSquaredUpperAfter_of_witness
      hN⟩

/-- Bundled coprime plus witness-supported shared-prime worker. -/
noncomputable def
    ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually : Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually

/-- The witness split supplies the Round77 coprime/intersection split worker. -/
theorem residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
    (hSplit :
      ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hWitness⟩
  exact ⟨hCop,
    residueSharedPrimeIntersectionRemainderLogSquaredUpperEventually_of_witness
      hWitness⟩

/-- The witness split also supplies the Round75 coprime/non-coprime split
worker. -/
theorem residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_witnessSplit
    (hSplit :
      ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually) :
    Gdbh.PathCResidueRemainderCoprimeSplit.ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually :=
  residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
    (residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
      hSplit)

/-- Final Path C adapter from the coprime/witness split and any supported
counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderWitnessSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderIntersectionSplit_and_countingInput
    (residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
      hSplit)
    hCounting

end PathCResidueRemainderSharedPrimeWitness
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.residueSharedPrimeIntersection_prime_dvd_of_prod_dvd
#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.residueSharedPrimeIntersectionPairCountingRemainder_eq_witness
#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.residueDoubleDivisorSharedPrimeIntersectionRemainderSum_eq_witness
#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.residueSharedPrimeIntersectionRemainderLogSquaredUpperAfter_of_witness
#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
#print axioms
  Gdbh.PathCResidueRemainderSharedPrimeWitness.pathC_kGoldbach_of_compatibleRemainderWitnessSplit_and_countingInput
