/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredFinitePrefix

/-!
# Path C -- threshold split for the filtered witness-cover branch

Round 86 exposes the filtered-cover worker in the same finite-prefix/tail
shape used elsewhere in the residue-remainder route.  Round85 already closes
the bounded prefix for every fixed `N`; the remaining honest analytic task is
only the large-range estimate `N + 1 <= Nat.sqrt n`.

This file is an adapter.  It does not strengthen the current eventual worker
or assert a uniform finite-prefix constant independent of `N`.
-/

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredThresholdSplit

open Gdbh.PathCResidueRemainderCoprimeSplit
  (ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually
   ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter
   ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually
   pathC_kGoldbach_of_compatibleRemainderFilteredCoverSplit_and_countingInput
   residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredFinitePrefix
  (ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt
   residueFilteredCoverFinitePrefixLogLoss
   residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications
  (residueFilteredCoverSqrtAtMostEnvelope)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Full-range and threshold-split filtered-cover workers -/

/-- Fixed-coefficient full-range filtered-cover bound. -/
noncomputable def ResidueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt
    (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n →
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Fixed-threshold split for the filtered-cover worker: Round85 handles the
bounded prefix, while the large-range tail remains the analytic input. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt
    (N : ℕ) : Prop :=
  ∃ A₀ A₁ : ℝ,
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt N A₀ ∧
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A₁

/-- Existential threshold-split form of the filtered-cover worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit :
      Prop :=
  ∃ N : ℕ,
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt N

/-! ## Recombination and equivalence with the existing eventual worker -/

/-- A finite-prefix bound and a large-range bound combine into a full-range
filtered-cover bound, with coefficient `max A₀ A₁`. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt_of_thresholdSplitAtSqrt
    {N : ℕ} {A₀ A₁ : ℝ}
    (hPrefix :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt N A₀)
    (hAfter :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A₁) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt
      (max A₀ A₁) := by
  rcases hPrefix with ⟨hA₀, hPrefixBd⟩
  rcases hAfter with ⟨hA₁, hAfterBd⟩
  refine ⟨lt_of_lt_of_le hA₁ (le_max_right A₀ A₁), ?_⟩
  intro n hn
  have hden_pos : 0 < (Real.log (n : ℝ))^2 :=
    Gdbh.PathCBrunErrorDecayProof.log_natCast_sq_pos (by omega : 3 ≤ n)
  by_cases hsqrt : Nat.sqrt n ≤ N
  · have hbd := hPrefixBd n hn hsqrt
    have hnum :
        A₀ * (n : ℝ) ≤ max A₀ A₁ * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left A₀ A₁) (by positivity)
    have hscale :
        A₀ * (n : ℝ) / (Real.log (n : ℝ))^2 ≤
          max A₀ A₁ * (n : ℝ) / (Real.log (n : ℝ))^2 :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    exact hbd.trans hscale
  · have hafter_sqrt : N + 1 ≤ Nat.sqrt n :=
      Nat.succ_le_iff.mpr (lt_of_not_ge hsqrt)
    have hbd := hAfterBd n hn hafter_sqrt
    have hnum :
        A₁ * (n : ℝ) ≤ max A₀ A₁ * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right A₀ A₁) (by positivity)
    have hscale :
        A₁ * (n : ℝ) / (Real.log (n : ℝ))^2 ≤
          max A₀ A₁ * (n : ℝ) / (Real.log (n : ℝ))^2 :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    exact hbd.trans hscale

/-- Fixed-threshold split form supplies a full-range filtered-cover
coefficient. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredWithConstant_of_thresholdSplitAtSqrt
    {N : ℕ}
    (hSplit :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt N) :
    ∃ A : ℝ,
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt A := by
  rcases hSplit with ⟨A₀, A₁, hPrefix, hAfter⟩
  exact ⟨max A₀ A₁,
    residueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt_of_thresholdSplitAtSqrt
      hPrefix hAfter⟩

/-- A threshold split immediately supplies the existing eventual filtered-cover
worker by keeping its large-range half. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually_of_thresholdSplit
    (hSplit :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually := by
  rcases hSplit with ⟨N, A₀, A₁, _hPrefix, hAfter⟩
  exact ⟨N, A₁, hAfter⟩

/-- Round85 closes the finite-prefix half for any fixed threshold, so an
existing large-range tail bound yields the threshold-split form. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt_of_after
    {N : ℕ} {A : ℝ}
    (hAfter :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt N := by
  exact
    ⟨residueFilteredCoverSqrtAtMostEnvelope N *
        residueFilteredCoverFinitePrefixLogLoss N,
      A,
      residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit N,
      hAfter⟩

/-- The existing eventual filtered-cover worker yields the explicit
finite/tail threshold split. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_of_eventually
    (hEventually :
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit := by
  rcases hEventually with ⟨N, A, hAfter⟩
  exact ⟨N,
    residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt_of_after
      hAfter⟩

/-- The threshold split is equivalent to the existing eventual worker, but
with the bounded prefix made explicit and closed by Round85. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_iff_eventually :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit ↔
      ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually :=
  ⟨residueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually_of_thresholdSplit,
    residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_of_eventually⟩

/-! ## Final-chain adapter with the coprime branch -/

/-- Coprime branch plus filtered-cover finite/tail split. -/
noncomputable def
    ResidueCompatibleRemainderFilteredCoverThresholdSplitLogSquaredUpperEventually :
      Prop :=
  ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually ∧
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit

/-- The threshold-split filtered-cover package supplies the existing
coprime/filtered-cover split worker. -/
theorem
    residueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually_of_thresholdSplit
    (hSplit :
      ResidueCompatibleRemainderFilteredCoverThresholdSplitLogSquaredUpperEventually) :
    ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually := by
  rcases hSplit with ⟨hCop, hFiltered⟩
  exact ⟨hCop,
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually_of_thresholdSplit
      hFiltered⟩

/-- Final Path C adapter from the coprime branch, the filtered-cover
finite/tail threshold split, and any supported counting input. -/
theorem
    pathC_kGoldbach_of_compatibleRemainderFilteredCoverThresholdSplit_and_countingInput
    (hSplit :
      ResidueCompatibleRemainderFilteredCoverThresholdSplitLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_compatibleRemainderFilteredCoverSplit_and_countingInput
    (residueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually_of_thresholdSplit
      hSplit)
    hCounting

end PathCResidueRemainderWitnessCoverFilteredThresholdSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredThresholdSplit.residueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt_of_thresholdSplitAtSqrt
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredThresholdSplit.residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt_of_after
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredThresholdSplit.residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_iff_eventually
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredThresholdSplit.residueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually_of_thresholdSplit
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredThresholdSplit.pathC_kGoldbach_of_compatibleRemainderFilteredCoverThresholdSplit_and_countingInput
