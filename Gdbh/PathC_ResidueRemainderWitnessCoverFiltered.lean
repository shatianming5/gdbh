/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverRearrange

/-!
# Path C -- filtered support for the prime-first witness cover

Round 82 pushes the `p ∈ d1 ∩ d2` indicator from the prime-first cover into
the finite supports for `d1` and `d2`.  The resulting form is still an
overlapping cover: the outer witness-prime sum is retained.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFiltered

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (residuePrimeDivisorWitnessSet)
open Gdbh.PathCResidueRemainderWitnessCoverRearrange
  (ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually
   ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter
   ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderPrimeFirstCoverSplit_and_countingInput
   residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
   residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
   residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Filtered prime-first cover -/

/-- Divisor subsets in the residue support, with cardinal cutoff, containing
the witness prime `p`. -/
noncomputable def residueWitnessContainingDivisorFamily
    (z k p : ℕ) : Finset (Finset ℕ) :=
  ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).filter
    (fun d => p ∈ d)

/-- Filtered-support version of the prime-first cover. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
    (n z k : ℕ) : ℝ :=
  ∑ p ∈ residuePrimeDivisorWitnessSet n z,
    ∑ d1 ∈ residueWitnessContainingDivisorFamily z k p,
      ∑ d2 ∈ residueWitnessContainingDivisorFamily z k p,
        |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|

/-- At-sqrt filtered-support cover. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
    n (Nat.sqrt n) (canonicalK n)

/-- The prime-first cover is equal to its filtered-support form. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum_eq_filtered
    (n z k : ℕ) :
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum n z k =
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum n z k := by
  classical
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)
  let W : Finset ℕ := residuePrimeDivisorWitnessSet n z
  let g : ℕ → Finset ℕ → Finset ℕ → ℝ := fun p d1 d2 =>
    |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
      (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
      |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
  unfold residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
    residueWitnessContainingDivisorFamily
  change
    ∑ p ∈ W, ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0)
    =
    ∑ p ∈ W, ∑ d1 ∈ F.filter (fun d => p ∈ d),
      ∑ d2 ∈ F.filter (fun d => p ∈ d),
        |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
  calc
    ∑ p ∈ W, ∑ d1 ∈ F, ∑ d2 ∈ F,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        (if p ∈ d1 ∩ d2 then
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        else
          0)
      =
    ∑ p ∈ W, ∑ d1 ∈ F,
      if p ∈ d1 then
        ∑ d2 ∈ F, if p ∈ d2 then g p d1 d2 else 0
      else
        0 := by
        apply Finset.sum_congr rfl
        intro p _hp
        apply Finset.sum_congr rfl
        intro d1 _hd1
        by_cases hp1 : p ∈ d1
        · rw [if_pos hp1]
          apply Finset.sum_congr rfl
          intro d2 _hd2
          by_cases hp2 : p ∈ d2
          · have hpinter : p ∈ d1 ∩ d2 :=
              Finset.mem_inter.mpr ⟨hp1, hp2⟩
            rw [if_pos hp2, if_pos hpinter]
          · have hpinter : ¬ p ∈ d1 ∩ d2 := by
              intro h
              exact hp2 (Finset.mem_inter.mp h).2
            rw [if_neg hp2, if_neg hpinter, mul_zero]
        · rw [if_neg hp1]
          apply Finset.sum_eq_zero
          intro d2 _hd2
          have hpinter : ¬ p ∈ d1 ∩ d2 := by
            intro h
            exact hp1 (Finset.mem_inter.mp h).1
          rw [if_neg hpinter, mul_zero]
    _ =
    ∑ p ∈ W, ∑ d1 ∈ F.filter (fun d => p ∈ d),
      ∑ d2 ∈ F, if p ∈ d2 then g p d1 d2 else 0 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (Finset.sum_filter (fun d1 => p ∈ d1)
          (fun d1 => ∑ d2 ∈ F,
            if p ∈ d2 then g p d1 d2 else 0)).symm
    _ =
    ∑ p ∈ W, ∑ d1 ∈ F.filter (fun d => p ∈ d),
      ∑ d2 ∈ F.filter (fun d => p ∈ d), g p d1 d2 := by
        apply Finset.sum_congr rfl
        intro p _hp
        apply Finset.sum_congr rfl
        intro d1 _hd1
        exact (Finset.sum_filter (fun d2 => p ∈ d2)
          (fun d2 => g p d1 d2)).symm

/-- At-sqrt version of the filtered-support equality. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt_eq_filtered
    (n : ℕ) :
    residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt n =
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n := by
  simpa [residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt,
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt] using
      residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum_eq_filtered
        n (Nat.sqrt n) (canonicalK n)

/-! ## Filtered cover worker and recombination -/

/-- Large-range upper bound for the filtered-support cover. -/
noncomputable def ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual filtered-support cover upper worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually :
      Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A

/-- Bounding the filtered-support cover bounds the Round81 prime-first cover. -/
theorem residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter_of_filtered
    {N : ℕ} {A : ℝ}
    (hFiltered :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A) :
    ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter N A := by
  rcases hFiltered with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt_eq_filtered]
  exact hbd n hn hsqrt

/-- Eventual filtered-support cover worker implies the Round81 prime-first
cover worker. -/
theorem residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually_of_filtered
    (hFiltered :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually) :
    ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually := by
  rcases hFiltered with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter_of_filtered
      hN⟩

/-- Bundled coprime plus filtered-support finite-cover worker. -/
noncomputable def
    ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually

/-- The filtered-support split supplies the Round81 prime-first split worker. -/
theorem residueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually_of_filteredSplit
    (hSplit :
      ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hFiltered⟩
  exact ⟨hCop,
    residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually_of_filtered
      hFiltered⟩

/-- Final Path C adapter from the coprime/filtered-cover split and any
supported counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderFilteredCoverSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderPrimeFirstCoverSplit_and_countingInput
    (residueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually_of_filteredSplit
      hSplit)
    hCounting

end PathCResidueRemainderWitnessCoverFiltered
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum_eq_filtered
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt_eq_filtered
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter_of_filtered
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually_of_filtered
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.residueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually_of_filteredSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFiltered.pathC_kGoldbach_of_compatibleRemainderFilteredCoverSplit_and_countingInput
