/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredEnvelope
import Mathlib.Tactic.Linarith

/-!
# Path C -- applications of the filtered witness-cover envelope

Round 84 connects the Round83 filtered-cover envelope to the elementary
cardinality input `(residuePrimeSet z).card ≤ z`.  This gives a reusable
finite-prefix linear envelope for any range with `Nat.sqrt n ≤ N`.

This file is finite and algebraic.  It does not close the eventual
large-range log-squared filtered-cover worker.
-/

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelope
  (residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_cardinalityEnvelope
   residueFilteredCoverCardinalityEnvelope)

/-! ## Elementary residue-prime cardinal input -/

/-- The residue prime set up to `z` has at most `z` elements. -/
theorem residuePrimeSet_card_le_self (z : ℕ) :
    (residuePrimeSet z).card ≤ z := by
  unfold residuePrimeSet
  have hfilter :
      ((Finset.Icc 3 z).filter Nat.Prime).card ≤ (Finset.Icc 3 z).card := by
    exact Finset.card_filter_le (Finset.Icc 3 z) Nat.Prime
  have hIcc : (Finset.Icc 3 z).card ≤ z := by
    rw [Nat.card_Icc]
    omega
  exact hfilter.trans hIcc

/-- If `z ≤ N`, then the residue prime set up to `z` has cardinal at most
`N`. -/
theorem residuePrimeSet_card_le_of_le {z N : ℕ} (hzN : z ≤ N) :
    (residuePrimeSet z).card ≤ N :=
  (residuePrimeSet_card_le_self z).trans hzN

/-! ## At-sqrt filtered-cover envelope applications -/

/-- Coarse filtered-cover finite-prefix multiplier for `Nat.sqrt n ≤ N`. -/
noncomputable def residueFilteredCoverSqrtAtMostEnvelope (N : ℕ) : ℝ :=
  residueFilteredCoverCardinalityEnvelope N

/-- If `Nat.sqrt n ≤ N`, the Round83 filtered cover is bounded by the
corresponding `N`-envelope. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_at_most
    (N : ℕ) {n : ℕ} (hsqrt_le_N : Nat.sqrt n ≤ N) :
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
      residueFilteredCoverSqrtAtMostEnvelope N * (n : ℝ) := by
  have hcard :
      (residuePrimeSet (Nat.sqrt n)).card ≤ N :=
    residuePrimeSet_card_le_of_le hsqrt_le_N
  simpa [residueFilteredCoverSqrtAtMostEnvelope] using
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_cardinalityEnvelope
      (n := n) (M := N) hcard

/-- Fixed-coefficient linear finite-prefix worker for the filtered witness
cover.  This is intentionally linear in `n`; it is not the final log-squared
large-range worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt
    (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n ≤ N →
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
        A * (n : ℝ)

/-- Existential coefficient form of the filtered-cover linear finite-prefix
worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixWithConstant
    (N : ℕ) : Prop :=
  ∃ A : ℝ,
    ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt N A

/-- Every finite square-root prefix has the explicit Round83 cardinal
envelope as a linear filtered-cover bound. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt N
      (residueFilteredCoverSqrtAtMostEnvelope N) := by
  refine ⟨?_, ?_⟩
  · unfold residueFilteredCoverSqrtAtMostEnvelope
      residueFilteredCoverCardinalityEnvelope
    positivity
  · intro n _hn hsqrt_le_N
    exact
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_at_most
        N hsqrt_le_N

/-- Existential finite-prefix form of the explicit filtered-cover envelope. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixWithConstant_explicit
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixWithConstant N :=
  ⟨residueFilteredCoverSqrtAtMostEnvelope N,
    residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit N⟩

/-- Specialization of the filtered-cover envelope to the existing
`Nat.sqrt n ≤ 10000` finite boundary. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_le_ten_thousand
    {n : ℕ} (hsqrt_le_ten_thousand : Nat.sqrt n ≤ 10000) :
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
      residueFilteredCoverSqrtAtMostEnvelope 10000 * (n : ℝ) :=
  residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_at_most
    10000 hsqrt_le_ten_thousand

end PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications.residuePrimeSet_card_le_self
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications.residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_at_most
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications.residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications.residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_le_ten_thousand
