/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredTailDecomposition

/-!
# Path C -- termwise split for the filtered witness-cover remainder

Round 88 decomposes the Round87 uniform shared-prime remainder input into
two smaller named pieces:

* a raw pair-counting remainder envelope for `residuePairCountingRemainder`;
* the filtered-cover support fact that the outer witness prime lies in both
  divisor supports and divides `n`.

This is a decomposition layer only.  It does not assert an analytic estimate
for the raw pair-counting remainder.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredTermwise

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairCountingRemainder)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (mem_residuePrimeDivisorWitnessSet_iff residuePrimeDivisorWitnessSet)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (residueWitnessContainingDivisorFamily)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition
  (ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter)

/-! ## Smaller termwise Props -/

/-- Raw pair-counting remainder envelope on the large square-root tail. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter
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
          |residuePairCountingRemainder n d1 d2| ≤ R n

/-- Filtered-cover support for the outer witness prime in each covered
pair. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter
    (N : ℕ) : Prop :=
  ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
    ∀ p : ℕ, p ∈ residuePrimeDivisorWitnessSet n (Nat.sqrt n) →
      ∀ d1 : Finset ℕ,
        d1 ∈ residueWitnessContainingDivisorFamily
          (Nat.sqrt n) (canonicalK n) p →
      ∀ d2 : Finset ℕ,
        d2 ∈ residueWitnessContainingDivisorFamily
          (Nat.sqrt n) (canonicalK n) p →
        p ∈ d1 ∩ d2 ∧ p ∣ n

/-- Bundled termwise decomposition of the Round87 uniform remainder input. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter
    (N : ℕ) (R : ℕ → ℝ) : Prop :=
  ResidueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter N ∧
    ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter N R

/-! ## Closed support facts -/

/-- A divisor family filtered by `p ∈ d` puts `p` in both supports. -/
theorem residueWitnessContainingDivisorFamily_mem_inter
    {z k p : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ residueWitnessContainingDivisorFamily z k p)
    (hd2 : d2 ∈ residueWitnessContainingDivisorFamily z k p) :
    p ∈ d1 ∩ d2 := by
  classical
  unfold residueWitnessContainingDivisorFamily at hd1 hd2
  exact
    Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp hd1).2, (Finset.mem_filter.mp hd2).2⟩

/-- The filtered-cover support input is closed algebraically. -/
theorem
    residueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter_holds
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter N := by
  intro n _hn _hsqrt p hp d1 hd1 d2 hd2
  exact
    ⟨residueWitnessContainingDivisorFamily_mem_inter hd1 hd2,
      (mem_residuePrimeDivisorWitnessSet_iff.mp hp).2⟩

/-! ## Termwise bridges -/

/-- The shared-prime branch is controlled by the raw pair remainder whenever
the scalar envelope is nonnegative. -/
theorem
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_nonneg
    (n : ℕ) (d1 d2 : Finset ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (hPair : |residuePairCountingRemainder n d1 d2| ≤ R) :
    |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| ≤ R := by
  classical
  by_cases hEmpty : d1 ∩ d2 = ∅
  · simpa [residueSharedPrimeIntersectionPairCountingRemainder, hEmpty] using hR
  · by_cases hDiv : (d1 ∩ d2).prod id ∣ n
    · have hDiv' : (∏ x ∈ d1 ∩ d2, x) ∣ n := by
        simpa using hDiv
      simpa [residueSharedPrimeIntersectionPairCountingRemainder, hEmpty, hDiv']
        using hPair
    · have hDiv' : ¬ (∏ x ∈ d1 ∩ d2, x) ∣ n := by
        simpa using hDiv
      simpa [residueSharedPrimeIntersectionPairCountingRemainder, hEmpty, hDiv']
        using hR

/-- Support-aware form of the termwise raw-pair bridge. -/
theorem
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_support
    (n p : ℕ) (d1 d2 : Finset ℕ) {R : ℝ}
    (hSupport : p ∈ d1 ∩ d2 ∧ p ∣ n)
    (hR : 0 ≤ R)
    (hPair : |residuePairCountingRemainder n d1 d2| ≤ R) :
    |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| ≤ R := by
  classical
  have hInter_ne : d1 ∩ d2 ≠ ∅ := by
    intro hEmpty
    have hp_empty : p ∉ d1 ∩ d2 := by
      simp [hEmpty]
    exact hp_empty hSupport.1
  by_cases hDiv : (d1 ∩ d2).prod id ∣ n
  · have hDiv' : (∏ x ∈ d1 ∩ d2, x) ∣ n := by
      simpa using hDiv
    simpa [residueSharedPrimeIntersectionPairCountingRemainder, hInter_ne, hDiv']
      using hPair
  · have hDiv' : ¬ (∏ x ∈ d1 ∩ d2, x) ∣ n := by
      simpa using hDiv
    simpa [residueSharedPrimeIntersectionPairCountingRemainder, hInter_ne, hDiv']
      using hR

/-- A raw pair-counting envelope implies the Round87 uniform shared-prime
remainder envelope. -/
theorem
    residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_pairRemainderEnvelope
    {N : ℕ} {R : ℕ → ℝ}
    (hPair :
      ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter N R) :
    ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter N R := by
  intro n hn hsqrt
  rcases hPair n hn hsqrt with ⟨hR, hPairBd⟩
  refine ⟨hR, ?_⟩
  intro p hp d1 hd1 d2 hd2
  exact
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_nonneg
      n d1 d2 hR (hPairBd p hp d1 hd1 d2 hd2)

/-- The bundled termwise decomposition implies the Round87 uniform
shared-prime remainder envelope. -/
theorem
    residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_termwiseDecomposition
    {N : ℕ} {R : ℕ → ℝ}
    (hDecomp :
      ResidueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter N R) :
    ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter N R := by
  rcases hDecomp with ⟨hSupport, hPair⟩
  intro n hn hsqrt
  rcases hPair n hn hsqrt with ⟨hR, hPairBd⟩
  refine ⟨hR, ?_⟩
  intro p hp d1 hd1 d2 hd2
  exact
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_support
      n p d1 d2 (hSupport n hn hsqrt p hp d1 hd1 d2 hd2)
      hR (hPairBd p hp d1 hd1 d2 hd2)

/-- Since the support half is closed, the raw pair-counting envelope alone
packages the bundled termwise decomposition. -/
theorem
    residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_of_pairRemainderEnvelope
    {N : ℕ} {R : ℕ → ℝ}
    (hPair :
      ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter N R) :
    ResidueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter N R := by
  exact
    ⟨residueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter_holds N,
      hPair⟩

end PathCResidueRemainderWitnessCoverFilteredTermwise
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeWitnessFilteredCoverSharedPrimeSupportAfter_holds
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_nonneg
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeIntersectionPairCountingRemainder_abs_le_pairRemainder_of_support
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_pairRemainderEnvelope
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_termwiseDecomposition
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_of_pairRemainderEnvelope
