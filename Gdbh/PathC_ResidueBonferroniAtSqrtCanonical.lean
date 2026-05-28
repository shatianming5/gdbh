/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_BrunBonferroniSubSqrtCanonical
import Gdbh.PathC_PairedBrunStirlingSqrt
import Gdbh.PathC_SingularCountingInterface

/-!
# Path C -- residue Bonferroni at-sqrt canonical target

This file isolates the next strict finite-sieve sub-Prop for the
kernel-plus-counting route.  The target is the residue-sifted analogue of the
existing paired canonical Brun-Bonferroni residual: fixed at `z = sqrt n`,
fixed depth `k(n) = 2n`, fixed main coefficient `1`, and an explicit
Bonferroni tail.

The file only supplies mechanical bridges.  The named canonical inequality
remains the genuine finite-sieve work item.
-/

namespace Gdbh
namespace PathCResidueBonferroniAtSqrtCanonical

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir refinedReservoir_def)
open Gdbh.PathCGoldbachResidues
  (BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
   GoldbachResidueErrorBoundedByRefinedAtSqrt
   goldbachResidueMainFactor goldbachResidueSiftedCount)
open Gdbh.PathCPairedBrunStirlingSqrt
  (pairedBrunStirlingTruncationErrorSqrt_canonical)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput
   pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput)

/-- The explicit canonical Bonferroni tail with depth `canonicalK n = 2n`.

It is kept as a two-variable function so it can be used directly as the
abstract error reservoir in
`BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError`. -/
noncomputable def residueBonferroniTailAtSqrt (n z : ℕ) : ℝ :=
  (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
    / ((2 * canonicalK n + 1).factorial : ℝ)

/-- The strict residue at-sqrt canonical Bonferroni residual.

This is the concrete finite-sieve worker target: prove the residue-sifted
upper bound at `z = sqrt n` with the actual residue main factor and the
explicit canonical tail. -/
def BrunGoldbachResidueSiftedAtSqrtCanonicalKernel : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
      ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- The independent error worker target for the canonical tail. -/
def ResidueBonferroniTailAtSqrtErrorBound : Prop :=
  GoldbachResidueErrorBoundedByRefinedAtSqrt residueBonferroniTailAtSqrt

/-- The explicit canonical Stirling tail is already dominated by the refined
at-sqrt reservoir. -/
theorem residueBonferroniTailAtSqrtErrorBound_holds :
    ResidueBonferroniTailAtSqrtErrorBound := by
  rcases pairedBrunStirlingTruncationErrorSqrt_canonical with ⟨N₀, hT5⟩
  refine ⟨1, max N₀ 4, by norm_num, ?_⟩
  intro n hn _hn2
  have hnT5 : N₀ ≤ n := (le_max_left N₀ 4).trans hn
  have hn4 : 4 ≤ n := (le_max_right N₀ 4).trans hn
  have htail :=
    hT5 n (Nat.sqrt n) hnT5 le_rfl
  have htail' :
      residueBonferroniTailAtSqrt n (Nat.sqrt n)
        ≤ (n : ℝ) / (2 * (Real.log (n : ℝ))^2) := by
    simpa [residueBonferroniTailAtSqrt, canonicalK] using htail
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn_real_gt_one : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact hn_real_gt_one
  have hlog_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hden_le : (Real.log (n : ℝ))^2 ≤ 2 * (Real.log (n : ℝ))^2 := by
    nlinarith [le_of_lt hlog_sq_pos]
  have hhalf_le :
      (n : ℝ) / (2 * (Real.log (n : ℝ))^2)
        ≤ (1 : ℝ) * refinedReservoir n (Nat.sqrt n) := by
    rw [refinedReservoir_def, one_mul]
    exact div_le_div_of_nonneg_left hn_nonneg hlog_sq_pos hden_le
  exact htail'.trans hhalf_le

/-- The canonical residue inequality is exactly the upper-bound worker field
with the explicit Bonferroni tail. -/
theorem residueSiftedUpperBoundAtSqrtWithError_of_canonical
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernel) :
    BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
      residueBonferroniTailAtSqrt := by
  refine ⟨1, 16, by norm_num, ?_⟩
  intro n hn _hn2
  simpa [one_mul] using hCan n hn

/-- Canonical residue upper bound plus its error estimate gives a supported
finite-sieve input for the corrected singular-counting route. -/
theorem finiteSieveInput_of_residueBonferroniCanonical
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
    (hErr : ResidueBonferroniTailAtSqrtErrorBound) :
    PathCFiniteSieveInput :=
  PathCFiniteSieveInput.atSqrtFields
    (residueSiftedUpperBoundAtSqrtWithError_of_canonical hCan) hErr

/-- Final route from the strict residue Bonferroni at-sqrt canonical residual,
its error domination estimate, and any supported counting input. -/
theorem pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
    (hErr : ResidueBonferroniTailAtSqrtErrorBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
    (residueSiftedUpperBoundAtSqrtWithError_of_canonical hCan)
    hErr hCounting

/-- Canonical residue upper bound alone now supplies the finite-sieve input,
because the explicit canonical tail is closed above. -/
theorem finiteSieveInput_of_residueBonferroniCanonical_closedTail
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernel) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueBonferroniCanonical hCan
    residueBonferroniTailAtSqrtErrorBound_holds

/-- Final route after closing the independent canonical-tail error estimate. -/
theorem pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail
    (hCan : BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput
    hCan residueBonferroniTailAtSqrtErrorBound_holds hCounting

end PathCResidueBonferroniAtSqrtCanonical
end Gdbh

#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.residueBonferroniTailAtSqrtErrorBound_holds
#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.residueSiftedUpperBoundAtSqrtWithError_of_canonical
#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.finiteSieveInput_of_residueBonferroniCanonical
#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput
#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.finiteSieveInput_of_residueBonferroniCanonical_closedTail
#print axioms
  Gdbh.PathCResidueBonferroniAtSqrtCanonical.pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail
