/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex kernel decomposition
-/
import Gdbh.PathC_LocalMainTermRefinedAtSqrtClosure

/-!
# Path C -- exact-error split for the at-sqrt residue kernel

This file adds a narrow, additive decomposition of the remaining kernel
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel`, definitionally the same Prop
as `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`.

The split separates the finite-sieve upper bound with an abstract error term
from the at-sqrt proof that this error term is dominated by the refined
reservoir used by the final Path C route.
-/

namespace Gdbh
namespace PathCKernelExactErrorDecomposition

open Gdbh.PathCGoldbachResidues
  (GoldbachResidueSiftedRefinedUpperBoundAtSqrt
   BrunGoldbachResidueSiftedUpperBoundWithError
   BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
   GoldbachResidueErrorDominatedByRefined
   goldbachResidueRefinedError
   brunGoldbachResidueSiftedUpperBoundAtSqrtWithError_of_all)
open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel)

/-! ## Smaller residual Props -/

/-- At-sqrt exact domination of an abstract finite-sieve error by the
canonical refined residue error. -/
def GoldbachResidueErrorDominatedByRefinedAtSqrt
    (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
    B n (Nat.sqrt n) ≤ goldbachResidueRefinedError n (Nat.sqrt n)

/-- Worker-friendly at-sqrt data: an abstract-error residue-sifted upper
bound together with exact at-sqrt domination of that error. -/
structure GoldbachResidueSiftedAtSqrtExactErrorData where
  B : ℕ → ℕ → ℝ
  upperBound : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B
  errorDominated : GoldbachResidueErrorDominatedByRefinedAtSqrt B

/-! ## Closed bridges -/

/-- All-threshold exact domination specializes to at-sqrt exact domination. -/
theorem goldbachResidueErrorDominatedByRefinedAtSqrt_of_all
    {B : ℕ → ℕ → ℝ}
    (hErr : GoldbachResidueErrorDominatedByRefined B) :
    GoldbachResidueErrorDominatedByRefinedAtSqrt B := by
  refine ⟨2, ?_⟩
  intro n _hn _hn2
  simpa [goldbachResidueRefinedError] using hErr n (Nat.sqrt n)

/-- The canonical refined residue error satisfies the at-sqrt exact
domination sub-Prop. -/
theorem goldbachResidueRefinedError_dominated_atSqrt :
    GoldbachResidueErrorDominatedByRefinedAtSqrt goldbachResidueRefinedError := by
  refine ⟨0, ?_⟩
  intro n _hn _hn2
  exact le_rfl

/-- All-threshold abstract-error data specializes to at-sqrt exact-error
data. -/
noncomputable def goldbachResidueSiftedAtSqrtExactErrorData_of_all
    {B : ℕ → ℕ → ℝ}
    (hUpper : BrunGoldbachResidueSiftedUpperBoundWithError B)
    (hErr : GoldbachResidueErrorDominatedByRefined B) :
    GoldbachResidueSiftedAtSqrtExactErrorData where
  B := B
  upperBound := brunGoldbachResidueSiftedUpperBoundAtSqrtWithError_of_all hUpper
  errorDominated := goldbachResidueErrorDominatedByRefinedAtSqrt_of_all hErr

/-- The exact-error data split closes the canonical at-sqrt residue kernel. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_exactErrorData
    (data : GoldbachResidueSiftedAtSqrtExactErrorData) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrt := by
  rcases data.upperBound with ⟨C₁, Nsift, hC₁_pos, hSiftBd⟩
  rcases data.errorDominated with ⟨Nerr, hErrBd⟩
  refine ⟨C₁, max Nsift Nerr, hC₁_pos, ?_⟩
  intro n hn hn2
  have hnSift : Nsift ≤ n := (le_max_left Nsift Nerr).trans hn
  have hnErr : Nerr ≤ n := (le_max_right Nsift Nerr).trans hn
  have hSift := hSiftBd n hnSift hn2
  have hErr := hErrBd n hnErr hn2
  linarith

/-- The exact-error data split closes the headline kernel alias. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_exactErrorData
    (data : GoldbachResidueSiftedAtSqrtExactErrorData) :
    BrunGoldbachLocalMainTermRefinedAtSqrtKernel :=
  goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_exactErrorData data

/-- All-threshold abstract-error upper bound plus all-threshold exact error
domination closes the headline kernel alias. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_all_exactError
    {B : ℕ → ℕ → ℝ}
    (hUpper : BrunGoldbachResidueSiftedUpperBoundWithError B)
    (hErr : GoldbachResidueErrorDominatedByRefined B) :
    BrunGoldbachLocalMainTermRefinedAtSqrtKernel :=
  brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_exactErrorData
    (goldbachResidueSiftedAtSqrtExactErrorData_of_all hUpper hErr)

end PathCKernelExactErrorDecomposition
end Gdbh

#print axioms
  Gdbh.PathCKernelExactErrorDecomposition.goldbachResidueErrorDominatedByRefinedAtSqrt_of_all
#print axioms
  Gdbh.PathCKernelExactErrorDecomposition.goldbachResidueRefinedError_dominated_atSqrt
#print axioms
  Gdbh.PathCKernelExactErrorDecomposition.goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_exactErrorData
#print axioms
  Gdbh.PathCKernelExactErrorDecomposition.brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_exactErrorData
