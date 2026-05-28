/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessDivisorPartition

/-!
# Path C -- finite cover for the shared-prime divisor witness branch

Round 80 converts the divisor-witness support into an honest finite cover
bound.  The cover sums over all residue-prime divisors of `n` that witness a
shared prime in `d1 ∩ d2`; it is an upper bound, not a disjoint decomposition.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCover

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
   ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter
   ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderDivisorWitnessSplit_and_countingInput
   residueCompatibleRemainderWitnessSplitLogSquaredUpperEventually_of_divisorWitnessSplit
   residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum
   residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt
   residuePrimeDivisorWitnessSet
   residueSharedPrimeDivisorWitnessPairCountingRemainder)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pair-level finite cover -/

/-- Pair-level finite cover over all residue-prime divisor witnesses.  Multiple
witnesses are counted multiple times, intentionally giving an upper bound. -/
noncomputable def residueSharedPrimeDivisorWitnessPairCover
    (n z : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  ∑ p ∈ residuePrimeDivisorWitnessSet n z,
    if p ∈ d1 ∩ d2 then
      |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
    else
      0

/-- The pair cover is nonnegative. -/
theorem residueSharedPrimeDivisorWitnessPairCover_nonneg
    (n z : ℕ) (d1 d2 : Finset ℕ) :
    0 ≤ residueSharedPrimeDivisorWitnessPairCover n z d1 d2 := by
  classical
  unfold residueSharedPrimeDivisorWitnessPairCover
  apply Finset.sum_nonneg
  intro p _hp
  by_cases hpinter : p ∈ d1 ∩ d2
  · simp [hpinter]
  · simp [hpinter]

/-- The divisor-witness pair branch is bounded by its finite cover. -/
theorem residueSharedPrimeDivisorWitnessPair_abs_le_cover
    (n z : ℕ) (d1 d2 : Finset ℕ) :
    |residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2| ≤
      residueSharedPrimeDivisorWitnessPairCover n z d1 d2 := by
  classical
  unfold residueSharedPrimeDivisorWitnessPairCountingRemainder
  by_cases hw :
      ∃ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n z ∧ p ∈ d1 ∩ d2
  · rcases hw with ⟨p, hpWitness, hpInter⟩
    rw [if_pos ⟨p, hpWitness, hpInter⟩]
    unfold residueSharedPrimeDivisorWitnessPairCover
    let f : ℕ → ℝ := fun q =>
      if q ∈ d1 ∩ d2 then
        |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
      else
        0
    have hf_nonneg :
        ∀ q ∈ residuePrimeDivisorWitnessSet n z, 0 ≤ f q := by
      intro q _hq
      dsimp [f]
      by_cases hqinter : q ∈ d1 ∩ d2
      · rw [if_pos hqinter]
        positivity
      · rw [if_neg hqinter]
    have hfp :
        f p = |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| := by
      dsimp [f]
      rw [if_pos hpInter]
    calc
      |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
          = f p := hfp.symm
      _ ≤ ∑ q ∈ residuePrimeDivisorWitnessSet n z, f q :=
          Finset.single_le_sum hf_nonneg hpWitness
  · rw [if_neg hw, abs_zero]
    exact residueSharedPrimeDivisorWitnessPairCover_nonneg n z d1 d2

/-! ## Double-sum finite cover -/

/-- Double-divisor cover sum for the shared-prime divisor-witness branch. -/
noncomputable def residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        residueSharedPrimeDivisorWitnessPairCover n z d1 d2

/-- At-sqrt double-divisor cover sum. -/
noncomputable def
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum n (Nat.sqrt n)
    (canonicalK n)

/-- The signed divisor-witness remainder is bounded by the double-divisor
finite cover. -/
theorem residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum_abs_le_coverSum
    (n z k : ℕ) :
    |residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum n z k| ≤
      residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum n z k := by
  classical
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)
  unfold residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum
  change
    |∑ d1 ∈ F, ∑ d2 ∈ F,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2| ≤
      ∑ d1 ∈ F, ∑ d2 ∈ F,
        |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
          residueSharedPrimeDivisorWitnessPairCover n z d1 d2
  calc
    |∑ d1 ∈ F, ∑ d2 ∈ F,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2|
        ≤ ∑ d1 ∈ F,
            |∑ d2 ∈ F,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residueSharedPrimeDivisorWitnessPairCountingRemainder
                  n z d1 d2| :=
          Finset.abs_sum_le_sum_abs
            (fun d1 => ∑ d2 ∈ F,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residueSharedPrimeDivisorWitnessPairCountingRemainder
                  n z d1 d2)
            F
    _ ≤ ∑ d1 ∈ F, ∑ d2 ∈ F,
          |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
            (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
            residueSharedPrimeDivisorWitnessPairCountingRemainder
              n z d1 d2| := by
          apply Finset.sum_le_sum
          intro d1 _hd1
          exact Finset.abs_sum_le_sum_abs
            (fun d2 =>
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residueSharedPrimeDivisorWitnessPairCountingRemainder
                  n z d1 d2)
            F
    _ ≤ ∑ d1 ∈ F, ∑ d2 ∈ F,
          |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
            (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
            residueSharedPrimeDivisorWitnessPairCover n z d1 d2 := by
          apply Finset.sum_le_sum
          intro d1 _hd1
          apply Finset.sum_le_sum
          intro d2 _hd2
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (residueSharedPrimeDivisorWitnessPair_abs_le_cover n z d1 d2)
            (abs_nonneg _)

/-- At-sqrt version of the finite cover bound. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt_abs_le_coverSum
    (n : ℕ) :
    |residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt n| ≤
      residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt n := by
  simpa [residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt,
    residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt] using
      residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum_abs_le_coverSum
        n (Nat.sqrt n) (canonicalK n)

/-! ## Cover worker and recombination -/

/-- Large-range upper bound for the finite cover of the shared-prime
divisor-witness remainder. -/
noncomputable def ResidueSharedPrimeWitnessCoverLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual finite-cover upper worker. -/
noncomputable def ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually :
    Prop :=
  ∃ N : ℕ, ∃ A : ℝ,
    ResidueSharedPrimeWitnessCoverLogSquaredUpperAfter N A

/-- Bounding the finite cover bounds the Round79 divisor-witness remainder. -/
theorem residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter_of_cover
    {N : ℕ} {A : ℝ}
    (hCover : ResidueSharedPrimeWitnessCoverLogSquaredUpperAfter N A) :
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter N A := by
  rcases hCover with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact
    (residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt_abs_le_coverSum
      n).trans (hbd n hn hsqrt)

/-- Eventual finite-cover upper worker implies the Round79 divisor-witness
upper worker. -/
theorem residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually_of_cover
    (hCover : ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually) :
    ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually := by
  rcases hCover with ⟨N, A, hN⟩
  exact ⟨N, A,
    residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter_of_cover hN⟩

/-- Bundled coprime plus finite-cover worker. -/
noncomputable def
    ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually

/-- The finite-cover split supplies the Round79 divisor-witness split worker. -/
theorem residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
    (hSplit :
      ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hCover⟩
  exact ⟨hCop,
    residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually_of_cover
      hCover⟩

/-- Final Path C adapter from the coprime/finite-cover split and any supported
counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderWitnessCoverSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderDivisorWitnessSplit_and_countingInput
    (residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
      hSplit)
    hCounting

end PathCResidueRemainderWitnessCover
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.residueSharedPrimeDivisorWitnessPair_abs_le_cover
#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum_abs_le_coverSum
#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt_abs_le_coverSum
#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperAfter_of_cover
#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCover.pathC_kGoldbach_of_compatibleRemainderWitnessCoverSplit_and_countingInput
