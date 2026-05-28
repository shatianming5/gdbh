/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCover

/-!
# Path C -- prime-first rearrangement of the witness cover

Round 81 commutes the finite cover from Round 80 so that the outer sum ranges
over residue-prime divisors of `n`.  This is still a cover: a divisor pair with
several shared witnesses is counted several times.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverRearrange

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
   residuePrimeDivisorWitnessSet)
open Gdbh.PathCResidueRemainderWitnessCover
  (ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually
   ResidueSharedPrimeWitnessCoverLogSquaredUpperAfter
   ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderWitnessCoverSplit_and_countingInput
   residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
   residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum
   residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt
   residueSharedPrimeDivisorWitnessPairCover)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Prime-first cover sum -/

/-- Prime-first version of the divisor-witness cover.  The inner pair sums
still retain the indicator `p ∈ d1 ∩ d2`; this keeps overlaps honest. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
    (n z k : ℕ) : ℝ :=
  ∑ p ∈ residuePrimeDivisorWitnessSet n z,
    ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
        |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
          (if p ∈ d1 ∩ d2 then
            |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
          else
            0)

/-- At-sqrt prime-first divisor-witness cover. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
    n (Nat.sqrt n) (canonicalK n)

/-- The Round80 cover sum is equal to its prime-first rearrangement. -/
theorem residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum_eq_primeFirst
    (n z k : ℕ) :
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum n z k =
      residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
        n z k := by
  classical
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)
  let W : Finset ℕ := residuePrimeDivisorWitnessSet n z
  unfold residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
    residueSharedPrimeDivisorWitnessPairCover
  change
    ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (∑ p ∈ W,
          if p ∈ d1 ∩ d2 then
            |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
          else
            0)
    =
    ∑ p ∈ W, ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0)
  calc
    ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (∑ p ∈ W,
          if p ∈ d1 ∩ d2 then
            |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
          else
            0)
      =
    ∑ d1 ∈ F, ∑ d2 ∈ F, ∑ p ∈ W,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0) := by
        apply Finset.sum_congr rfl
        intro d1 _hd1
        apply Finset.sum_congr rfl
        intro d2 _hd2
        rw [Finset.mul_sum]
    _ =
    ∑ d1 ∈ F, ∑ p ∈ W, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0) := by
        apply Finset.sum_congr rfl
        intro d1 _hd1
        rw [Finset.sum_comm]
    _ =
    ∑ p ∈ W, ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0) := by
        rw [Finset.sum_comm]

/-- At-sqrt version of the prime-first cover rearrangement. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt_eq_primeFirst
    (n : ℕ) :
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt n =
      residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt
        n := by
  simpa [residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt,
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt] using
      residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum_eq_primeFirst
        n (Nat.sqrt n) (canonicalK n)

/-! ## Prime-first cover worker and recombination -/

/-- Large-range upper bound for the prime-first finite cover. -/
noncomputable def ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual prime-first finite-cover upper worker. -/
noncomputable def
    ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually :
      Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter N A

/-- Bounding the prime-first cover bounds the Round80 cover. -/
theorem residueSharedPrimeWitnessCoverLogSquaredUpperAfter_of_primeFirst
    {N : ℕ} {A : ℝ}
    (hPrimeFirst :
      ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter N A) :
    ResidueSharedPrimeWitnessCoverLogSquaredUpperAfter N A := by
  rcases hPrimeFirst with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt_eq_primeFirst]
  exact hbd n hn hsqrt

/-- Eventual prime-first cover worker implies the Round80 cover worker. -/
theorem residueSharedPrimeWitnessCoverLogSquaredUpperEventually_of_primeFirst
    (hPrimeFirst :
      ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually) :
    ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually := by
  rcases hPrimeFirst with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueSharedPrimeWitnessCoverLogSquaredUpperAfter_of_primeFirst hN⟩

/-- Bundled coprime plus prime-first finite-cover worker. -/
noncomputable def
    ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually

/-- The prime-first cover split supplies the Round80 cover split worker. -/
theorem residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
    (hSplit :
      ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hPrimeFirst⟩
  exact ⟨hCop,
    residueSharedPrimeWitnessCoverLogSquaredUpperEventually_of_primeFirst
      hPrimeFirst⟩

/-- The prime-first cover split supplies the Round79 divisor-witness split
worker. -/
theorem residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_primeFirstSplit
    (hSplit :
      ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually :=
  residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
    (residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
      hSplit)

/-- Final Path C adapter from the coprime/prime-first cover split and any
supported counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderPrimeFirstCoverSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderWitnessCoverSplit_and_countingInput
    (residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
      hSplit)
    hCounting

end PathCResidueRemainderWitnessCoverRearrange
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum_eq_primeFirst
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt_eq_primeFirst
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.residueSharedPrimeWitnessCoverLogSquaredUpperAfter_of_primeFirst
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_primeFirstSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverRearrange.pathC_kGoldbach_of_compatibleRemainderPrimeFirstCoverSplit_and_countingInput
