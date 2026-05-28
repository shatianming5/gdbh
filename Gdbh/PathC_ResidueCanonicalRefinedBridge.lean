/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueMainFactorMertensLower

/-!
# Path C -- residue canonical refined bridge

Round 42 closed the residue main-factor lower bound used by the analytic tail
decomposition.  This file records the more faithful bridge for the current
finite-sieve route: a residue-sifted at-sqrt upper bound with the refined
reservoir already implies the corrected canonical residual, because the
refined reservoir `n / (log n)^2` is absorbed by the closed main-factor lower
bound.

This keeps the score-positive target on the existing refined finite-sieve
input, instead of strengthening it to the false-prone bare
`goldbachResidueSiftedCount <= A * n / (log n)^2` estimate.
-/

set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalRefinedBridge

open Gdbh.PathCGoldbachResidues
  (GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueRefinedError)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality)
open Gdbh.PathCResidueCanonicalParametricCoarseSplit
  (ResidueCanonicalFromSqrtAfterAtSqrt
   ResidueCanonicalFromSqrtAfterAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtAfter
   pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput)
open Gdbh.PathCResidueMainFactorMertensLower
  (residueMainFactorLogSquaredLowerEventually_holds)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir_def)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Eventual refined-residual target -/

/-- Eventual form of the parameterized corrected residual. -/
noncomputable def ResidueCanonicalFromSqrtAfterEventually : Prop :=
  ∃ N : ℕ, ResidueCanonicalFromSqrtAfterAtSqrtWithConstant N

/-! ## Refined finite-sieve bridge -/

/-- The refined at-sqrt residue-sifted finite-sieve target implies the
eventual corrected canonical residual.

The only analytic input used here beyond the refined target is the already
closed Round 42 lower bound for the residue main factor. -/
theorem residueCanonicalFromSqrtAfterEventually_of_refinedAtSqrtWithErrorConstant
    (hRefined : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant) :
    ResidueCanonicalFromSqrtAfterEventually := by
  rcases hRefined with ⟨C1, CE, N0, hC1_pos, hCE_pos, hRefBd⟩
  rcases residueMainFactorLogSquaredLowerEventually_holds with
    ⟨NL, B, hLower⟩
  rcases hLower with ⟨hB_pos, hLowerBd⟩
  refine ⟨max NL N0, C1 + CE / B, ?_⟩
  refine ⟨by positivity, ?_⟩
  intro n hn16 hsqrt_after
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hn2 : 2 ≤ n := by omega
  have hN0_sqrt : N0 ≤ Nat.sqrt n := by
    have hmax : max NL N0 + 1 ≤ Nat.sqrt n := hsqrt_after
    omega
  have hN0n : N0 ≤ n := hN0_sqrt.trans (Nat.sqrt_le_self n)
  have hNLsqrt : NL + 1 ≤ Nat.sqrt n := by
    have hmax : max NL N0 + 1 ≤ Nat.sqrt n := hsqrt_after
    omega
  have href := hRefBd n hN0n hn2
  have hlower := hLowerBd n hn16 hNLsqrt
  have hn_gt_one : 1 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hlog_sq_ne : (Real.log (n : ℝ)) ^ 2 ≠ 0 := by positivity
  have hscale_nonneg : 0 ≤ (CE / B * (n : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlower hscale_nonneg
  have herr_absorb :
      CE * goldbachResidueRefinedError n (Nat.sqrt n) ≤
        (CE / B) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
    calc
      CE * goldbachResidueRefinedError n (Nat.sqrt n)
          = CE * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
              simp [goldbachResidueRefinedError, refinedReservoir_def]
      _ = (CE / B * (n : ℝ)) *
            (B / (Real.log (n : ℝ)) ^ 2) := by
              field_simp [ne_of_gt hB_pos, hlog_sq_ne]
      _ ≤ (CE / B * (n : ℝ)) *
            goldbachResidueMainFactor n (Nat.sqrt n) := hmul
      _ = (CE / B) * (n : ℝ) *
            goldbachResidueMainFactor n (Nat.sqrt n) := by ring
  have hcombine :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤
        (C1 + CE / B) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmain_eq :
        C1 * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) +
            (CE / B) * (n : ℝ) *
              goldbachResidueMainFactor n (Nat.sqrt n) =
          (C1 + CE / B) * (n : ℝ) *
            goldbachResidueMainFactor n (Nat.sqrt n) := by
      ring
    linarith
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcombine.trans (le_add_of_nonneg_right htail_nonneg)

/-! ## Integration adapters -/

/-- The refined at-sqrt finite-sieve target supplies the supported
finite-sieve input for the current Path C route. -/
theorem finiteSieveInput_of_refinedAtSqrtWithErrorConstant
    (hRefined : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant) :
    PathCFiniteSieveInput := by
  rcases
    residueCanonicalFromSqrtAfterEventually_of_refinedAtSqrtWithErrorConstant
      hRefined with ⟨N, hAfter⟩
  exact finiteSieveInput_of_residueCanonicalFromSqrtAfter N hAfter

/-- Final Path C adapter from the refined at-sqrt finite-sieve target and any
supported counting input. -/
theorem pathC_kGoldbach_of_refinedAtSqrtWithErrorConstant_and_countingInput
    (hRefined : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  rcases
    residueCanonicalFromSqrtAfterEventually_of_refinedAtSqrtWithErrorConstant
      hRefined with ⟨N, hAfter⟩
  exact
    pathC_kGoldbach_of_residueCanonicalFromSqrtAfter_and_countingInput
      N hAfter hCounting

end PathCResidueCanonicalRefinedBridge
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalRefinedBridge.residueCanonicalFromSqrtAfterEventually_of_refinedAtSqrtWithErrorConstant
#print axioms
  Gdbh.PathCResidueCanonicalRefinedBridge.finiteSieveInput_of_refinedAtSqrtWithErrorConstant
#print axioms
  Gdbh.PathCResidueCanonicalRefinedBridge.pathC_kGoldbach_of_refinedAtSqrtWithErrorConstant_and_countingInput
