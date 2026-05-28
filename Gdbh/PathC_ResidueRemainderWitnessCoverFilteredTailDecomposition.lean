/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredThresholdSplit
import Mathlib.Tactic.Ring

/-!
# Path C -- tail decomposition for the filtered witness-cover worker

Round 87 decomposes the remaining large-range filtered-cover worker into
smaller named pieces:

* a uniform remainder envelope for each filtered `(p, d1, d2)` term;
* a witness-prime/divisor-family cardinality envelope;
* a weighted tail inequality for the resulting scalar envelope.

This file is a decomposition layer only.  It does not close the analytic tail
and it does not reuse the finite cardinal envelope as a large-range
log-squared estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredTailDecomposition

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (residuePrimeDivisorWitnessSet)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter
   residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
   residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt
   residueWitnessContainingDivisorFamily)

/-! ## Weighted envelope sums -/

/-- Weighted filtered-cover envelope after replacing every pair-counting
remainder by the scalar envelope `R n`. -/
noncomputable def residueFilteredCoverRemainderEnvelopeWeightedSum
    (R : ℕ → ℝ) (n z k : ℕ) : ℝ :=
  ∑ p ∈ residuePrimeDivisorWitnessSet n z,
    ∑ d1 ∈ residueWitnessContainingDivisorFamily z k p,
      ∑ d2 ∈ residueWitnessContainingDivisorFamily z k p,
        |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ)| * R n

/-- At-sqrt form of the weighted filtered-cover envelope. -/
noncomputable def residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt
    (R : ℕ → ℝ) (n : ℕ) : ℝ :=
  residueFilteredCoverRemainderEnvelopeWeightedSum R n (Nat.sqrt n)
    (canonicalK n)

/-! ## Smaller tail Props -/

/-- Uniform termwise remainder envelope on the large square-root tail. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter
    (N : ℕ) (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
    0 ≤ R n ∧
      ∀ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n (Nat.sqrt n) →
        ∀ d1 : Finset ℕ,
          d1 ∈ residueWitnessContainingDivisorFamily
            (Nat.sqrt n) (canonicalK n) p →
        ∀ d2 : Finset ℕ,
          d2 ∈ residueWitnessContainingDivisorFamily
            (Nat.sqrt n) (canonicalK n) p →
          |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| ≤ R n

/-- Weighted witness-prime tail estimate after the uniform remainder envelope
has been inserted into the filtered cover. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter
    (N : ℕ) (R : ℕ → ℝ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt R n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Cardinality envelope for the witness-prime set and every filtered
divisor family on the large square-root tail. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyCardinalityAfter
    (N : ℕ) (Cw Cd : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
    0 ≤ Cw n ∧ 0 ≤ Cd n ∧
      ((residuePrimeDivisorWitnessSet n (Nat.sqrt n)).card : ℝ) ≤ Cw n ∧
        ∀ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n (Nat.sqrt n) →
          ((residueWitnessContainingDivisorFamily
            (Nat.sqrt n) (canonicalK n) p).card : ℝ) ≤ Cd n

/-- Scalar cardinal-tail inequality after replacing the support by the
witness-prime and divisor-family cardinality envelopes. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverCardinalityTailAfter
    (N : ℕ) (R Cw Cd : ℕ → ℝ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      Cw n * (Cd n * (Cd n * R n)) ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Bundled Round87 decomposition of the filtered-cover tail worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverTailDecompositionAfter
    (N : ℕ) (R Cw Cd : ℕ → ℝ) (A : ℝ) : Prop :=
  ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter N R ∧
    ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyCardinalityAfter N Cw Cd ∧
      ResidueSharedPrimeWitnessFilteredCoverCardinalityTailAfter N R Cw Cd A

/-! ## Termwise envelope bridge -/

/-- The filtered cover is bounded by the weighted scalar envelope whenever
`R n` bounds every filtered pair remainder. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_remainderEnvelopeWeightedSum
    {N : ℕ} {R : ℕ → ℝ} {n : ℕ}
    (hRem :
      ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter N R)
    (hn : 16 ≤ n) (hsqrt : N + 1 ≤ Nat.sqrt n) :
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
      residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt R n := by
  classical
  rcases hRem n hn hsqrt with ⟨_hR_nonneg, hTerm⟩
  unfold residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt
    residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
    residueFilteredCoverRemainderEnvelopeWeightedSum
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro d1 hd1
  apply Finset.sum_le_sum
  intro d2 hd2
  exact mul_le_mul_of_nonneg_left
    (hTerm p hp d1 hd1 d2 hd2)
    (abs_nonneg _)

/-- The uniform termwise envelope plus the weighted-prime tail estimate imply
the existing filtered-cover large-range worker. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_remainderEnvelope_and_weightedPrimeTail
    {N : ℕ} {R : ℕ → ℝ} {A : ℝ}
    (hRem :
      ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter N R)
    (hTail :
      ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter N R A) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A := by
  rcases hTail with ⟨hA, hTailBd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact
    (residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_remainderEnvelopeWeightedSum
      hRem hn hsqrt).trans (hTailBd n hn hsqrt)

/-! ## Cardinality bridge to the weighted tail -/

private theorem filtered_moebius_weight_le_one (d1 d2 : Finset ℕ) :
    |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| ≤ (1 : ℝ) := by
  rw [abs_mul]
  have hmu1 :
      |((ArithmeticFunction.moebius (d1.prod id) : ℤ) : ℝ)| ≤
        (1 : ℝ) := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d1.prod id))
  have hmu2 :
      |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| ≤
        (1 : ℝ) := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d2.prod id))
  have hmu2_nonneg :
      0 ≤ |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| :=
    abs_nonneg _
  have hmul :=
    mul_le_mul hmu1 hmu2 hmu2_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hmul

/-- The weighted scalar envelope is bounded by witness-prime and
divisor-family cardinality envelopes. -/
theorem
    residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt_le_cardinality
    {R Cw Cd : ℕ → ℝ} {n : ℕ}
    (hR_nonneg : 0 ≤ R n)
    (hCw_card :
      ((residuePrimeDivisorWitnessSet n (Nat.sqrt n)).card : ℝ) ≤ Cw n)
    (hCd_nonneg : 0 ≤ Cd n)
    (hCd_card :
      ∀ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n (Nat.sqrt n) →
        ((residueWitnessContainingDivisorFamily
          (Nat.sqrt n) (canonicalK n) p).card : ℝ) ≤ Cd n) :
    residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt R n ≤
      Cw n * (Cd n * (Cd n * R n)) := by
  classical
  let W : Finset ℕ := residuePrimeDivisorWitnessSet n (Nat.sqrt n)
  let Fp : ℕ → Finset (Finset ℕ) :=
    fun p => residueWitnessContainingDivisorFamily
      (Nat.sqrt n) (canonicalK n) p
  unfold residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt
    residueFilteredCoverRemainderEnvelopeWeightedSum
  change
    ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| * R n
      ≤ Cw n * (Cd n * (Cd n * R n))
  calc
    ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| * R n
        ≤ ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p, R n := by
          apply Finset.sum_le_sum
          intro p _hp
          apply Finset.sum_le_sum
          intro d1 _hd1
          apply Finset.sum_le_sum
          intro d2 _hd2
          have hmul :=
            mul_le_mul_of_nonneg_right
              (filtered_moebius_weight_le_one d1 d2) hR_nonneg
          simpa using hmul
    _ ≤ ∑ p ∈ W, Cd n * (Cd n * R n) := by
          apply Finset.sum_le_sum
          intro p hp
          have hFp_card :
              ((Fp p).card : ℝ) ≤ Cd n := by
            dsimp [Fp]
            exact hCd_card p hp
          have hFp_nonneg : 0 ≤ ((Fp p).card : ℝ) := by positivity
          have hcard_sq :
              ((Fp p).card : ℝ) * ((Fp p).card : ℝ) ≤
                Cd n * Cd n :=
            mul_le_mul hFp_card hFp_card hFp_nonneg hCd_nonneg
          have hmul :=
            mul_le_mul_of_nonneg_right hcard_sq hR_nonneg
          calc
            ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p, R n
                = ((Fp p).card : ℝ) *
                    (((Fp p).card : ℝ) * R n) := by
                  rw [Finset.sum_const, Finset.sum_const]
                  simp [nsmul_eq_mul]
            _ = (((Fp p).card : ℝ) * ((Fp p).card : ℝ)) * R n := by
                  ring
            _ ≤ (Cd n * Cd n) * R n := hmul
            _ = Cd n * (Cd n * R n) := by ring
    _ = (W.card : ℝ) * (Cd n * (Cd n * R n)) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    _ ≤ Cw n * (Cd n * (Cd n * R n)) := by
          have hconst_nonneg :
              0 ≤ Cd n * (Cd n * R n) :=
            mul_nonneg hCd_nonneg (mul_nonneg hCd_nonneg hR_nonneg)
          exact mul_le_mul_of_nonneg_right hCw_card hconst_nonneg

/-- Cardinality controls plus the scalar cardinal-tail inequality imply the
weighted-prime tail estimate. -/
theorem
    residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_cardinalityTail
    {N : ℕ} {R Cw Cd : ℕ → ℝ} {A : ℝ}
    (hR_nonneg :
      ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n → 0 ≤ R n)
    (hCard :
      ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyCardinalityAfter
        N Cw Cd)
    (hTail :
      ResidueSharedPrimeWitnessFilteredCoverCardinalityTailAfter
        N R Cw Cd A) :
    ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter N R A := by
  rcases hTail with ⟨hA, hTailBd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rcases hCard n hn hsqrt with ⟨_hCw_nonneg, hCd_nonneg, hWcard, hDcard⟩
  exact
    (residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt_le_cardinality
      (R := R) (Cw := Cw) (Cd := Cd)
      (hR_nonneg n hn hsqrt) hWcard hCd_nonneg hDcard).trans
        (hTailBd n hn hsqrt)

/-- The bundled Round87 decomposition implies the existing filtered-cover tail
worker. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_tailDecomposition
    {N : ℕ} {R Cw Cd : ℕ → ℝ} {A : ℝ}
    (hDecomp :
      ResidueSharedPrimeWitnessFilteredCoverTailDecompositionAfter
        N R Cw Cd A) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A := by
  rcases hDecomp with ⟨hRem, hCard, hTail⟩
  exact
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_remainderEnvelope_and_weightedPrimeTail
      hRem
      (residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_cardinalityTail
        (fun n hn hsqrt => (hRem n hn hsqrt).1) hCard hTail)

end PathCResidueRemainderWitnessCoverFilteredTailDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition.residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_remainderEnvelopeWeightedSum
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition.residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_remainderEnvelope_and_weightedPrimeTail
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition.residueFilteredCoverRemainderEnvelopeWeightedSumAtSqrt_le_cardinality
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition.residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_cardinalityTail
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition.residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_tailDecomposition
