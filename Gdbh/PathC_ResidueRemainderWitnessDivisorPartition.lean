/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSharedPrimeWitness

/-!
# Path C -- divisor-filter support for the shared-prime witness branch

Round 79 normalizes the Round78 witness condition against the finite set of
residue primes dividing `n`.  This is a support/filter normalization, not a
disjoint sum over witnesses: a divisor pair can have multiple shared prime
witnesses.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessDivisorPartition

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderSharedPrimeWitness
  (ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually
   ResidueSharedPrimeWitnessRemainderLogSquaredUpperAfter
   ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderWitnessSplit_and_countingInput
   residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
   residueDoubleDivisorSharedPrimeWitnessRemainderSum
   residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt
   residueSharedPrimeWitnessPairCountingRemainder)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pair-level divisor-filter support -/

/-- Residue primes up to `z` that divide `n`. -/
noncomputable def residuePrimeDivisorWitnessSet (n z : ℕ) : Finset ℕ :=
  (residuePrimeSet z).filter (fun p => p ∣ n)

/-- The residue-prime divisor witness set is contained in the residue-prime
set. -/
theorem residuePrimeDivisorWitnessSet_subset (n z : ℕ) :
    residuePrimeDivisorWitnessSet n z ⊆ residuePrimeSet z := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- Membership in the divisor witness set is exactly residue-prime membership
plus divisibility by `n`. -/
theorem mem_residuePrimeDivisorWitnessSet_iff
    {n z p : ℕ} :
    p ∈ residuePrimeDivisorWitnessSet n z ↔ p ∈ residuePrimeSet z ∧ p ∣ n := by
  simp [residuePrimeDivisorWitnessSet]

/-- The shared-prime witness condition is equivalently a witness in the finite
residue-prime divisor set. -/
theorem residueSharedPrimeWitnessCondition_iff_primeDivisorWitness
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) :
    (∃ p : ℕ, p ∈ d1 ∩ d2 ∧ p ∣ n) ↔
      ∃ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n z ∧ p ∈ d1 ∩ d2 := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hpdiv⟩
    have hpResidue : p ∈ residuePrimeSet z :=
      hd1 (Finset.mem_inter.mp hp).1
    exact ⟨p, Finset.mem_filter.mpr ⟨hpResidue, hpdiv⟩, hp⟩
  · intro h
    rcases h with ⟨p, hpWitness, hpInter⟩
    exact ⟨p, hpInter, (Finset.mem_filter.mp hpWitness).2⟩

/-- The shared-prime branch supported by residue prime divisors of `n`. -/
noncomputable def residueSharedPrimeDivisorWitnessPairCountingRemainder
    (n z : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if ∃ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n z ∧ p ∈ d1 ∩ d2 then
    residueSharedPrimeIntersectionPairCountingRemainder n d1 d2
  else
    0

/-- On residue-prime subsets, the Round78 witness branch equals the divisor-set
witness branch. -/
theorem residueSharedPrimeWitnessPairCountingRemainder_eq_divisorWitness
    {z n : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) :
    residueSharedPrimeWitnessPairCountingRemainder n d1 d2 =
      residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2 := by
  classical
  have hiff :=
    residueSharedPrimeWitnessCondition_iff_primeDivisorWitness
      (z := z) (n := n) (d1 := d1) (d2 := d2) hd1
  unfold residueSharedPrimeWitnessPairCountingRemainder
    residueSharedPrimeDivisorWitnessPairCountingRemainder
  by_cases hw : ∃ p : ℕ, p ∈ d1 ∩ d2 ∧ p ∣ n
  · have hdw :
        ∃ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n z ∧ p ∈ d1 ∩ d2 :=
      hiff.mp hw
    rw [if_pos hw, if_pos hdw]
  · have hdw :
        ¬ ∃ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n z ∧ p ∈ d1 ∩ d2 :=
      fun h => hw (hiff.mpr h)
    rw [if_neg hw, if_neg hdw]

/-! ## Sum-level divisor-filter support -/

/-- The divisor-filter supported shared-prime signed remainder sum. -/
noncomputable def residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2

/-- At-sqrt divisor-filter supported shared-prime signed remainder. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum n (Nat.sqrt n)
    (canonicalK n)

/-- The Round78 witness-supported remainder equals the divisor-filter
witness-supported remainder. -/
theorem residueDoubleDivisorSharedPrimeWitnessRemainderSum_eq_divisorWitness
    (n z k : ℕ) :
    residueDoubleDivisorSharedPrimeWitnessRemainderSum n z k =
      residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorSharedPrimeWitnessRemainderSum
    residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum
  refine Finset.sum_congr rfl ?_
  intro d1 hd1
  have hd1_sub : d1 ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd1).1
  refine Finset.sum_congr rfl ?_
  intro d2 _hd2
  rw [residueSharedPrimeWitnessPairCountingRemainder_eq_divisorWitness
    hd1_sub]

/-- At-sqrt version of the divisor-filter witness equality. -/
theorem residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt_eq_divisorWitness
    (n : ℕ) :
    residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt n =
      residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt,
    residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt] using
      residueDoubleDivisorSharedPrimeWitnessRemainderSum_eq_divisorWitness
        n (Nat.sqrt n) (canonicalK n)

/-! ## Divisor-filter worker and recombination -/

/-- Large-range upper bound for the divisor-filter witness remainder. -/
noncomputable def
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual divisor-filter witness upper worker. -/
noncomputable def
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually :
      Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter N A

/-- Bounding the divisor-filter witness remainder bounds the Round78 witness
remainder. -/
theorem residueSharedPrimeWitnessRemainderLogSquaredUpperAfter_of_divisorWitness
    {N : ℕ} {A : ℝ}
    (hDivisor :
      ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter N A) :
    ResidueSharedPrimeWitnessRemainderLogSquaredUpperAfter N A := by
  rcases hDivisor with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [residueDoubleDivisorSharedPrimeWitnessRemainderSumAtSqrt_eq_divisorWitness]
  exact hbd n hn hsqrt

/-- Eventual divisor-filter witness upper worker implies the Round78 witness
upper worker. -/
theorem residueSharedPrimeWitnessRemainderLogSquaredUpperEventually_of_divisorWitness
    (hDivisor :
      ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually) :
    ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually := by
  rcases hDivisor with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueSharedPrimeWitnessRemainderLogSquaredUpperAfter_of_divisorWitness
      hN⟩

/-- Bundled coprime plus divisor-filter witness worker. -/
noncomputable def
    ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually

/-- The divisor-filter split supplies the Round78 witness split worker. -/
theorem residueCompatibleRemainderWitnessSplitLogSquaredUpperEventually_of_divisorWitnessSplit
    (hSplit :
      ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hDivisor⟩
  exact ⟨hCop,
    residueSharedPrimeWitnessRemainderLogSquaredUpperEventually_of_divisorWitness
      hDivisor⟩

/-- Final Path C adapter from the coprime/divisor-filter witness split and any
supported counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderDivisorWitnessSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderWitnessSplit_and_countingInput
    (residueCompatibleRemainderWitnessSplitLogSquaredUpperEventually_of_divisorWitnessSplit
      hSplit)
    hCounting

end PathCResidueRemainderWitnessDivisorPartition
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.residueSharedPrimeWitnessCondition_iff_primeDivisorWitness
#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.residueSharedPrimeWitnessPairCountingRemainder_eq_divisorWitness
#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.residueDoubleDivisorSharedPrimeWitnessRemainderSum_eq_divisorWitness
#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.residueSharedPrimeWitnessRemainderLogSquaredUpperAfter_of_divisorWitness
#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.residueCompatibleRemainderWitnessSplitLogSquaredUpperEventually_of_divisorWitnessSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessDivisorPartition.pathC_kGoldbach_of_compatibleRemainderDivisorWitnessSplit_and_countingInput
