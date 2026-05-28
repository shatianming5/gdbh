/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityClosure
import Gdbh.PathC_ResidueDoubleDivisorQuotientDecomposition
import Mathlib.Tactic.Linarith

/-!
# Path C -- residue count-to-density handoff

Round 20 closed the local-density Euler algebra.  This file reconnects the
older quotient-main/remainder split to the active split count-to-density
target.  It does not prove either analytic counting residual; it only removes
the now-closed local-density algebra from that branch.
-/

namespace Gdbh
namespace PathCResidueCountToDensityClosure

open scoped BigOperators

open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorQuotientMainAtSqrtBound
   ResidueDoubleDivisorRemainderAtSqrtBound
   residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound)
open Gdbh.PathCResidueCoprimeSplitDensityBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound
   residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_unsplit)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- The existing quotient-main and signed-remainder residuals imply the
unsplit exact-count-to-local-density residual once the local-density Euler
algebra has been closed. -/
theorem residueDoubleDivisorExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound := by
  intro n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder]
  have hMain' := hMain n hn
  have hRem' := hRem n hn
  have hEuler :=
    _root_.Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt n hn
  rw [← hEuler] at hMain'
  linarith

/-- The quotient-main and signed-remainder residuals also imply the active
split count-to-density residual. -/
theorem residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound :=
  residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_unsplit
    (residueDoubleDivisorExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
      hMain hRem)

/-- The strict residue canonical kernel follows from the quotient-main and
signed-remainder residuals, with all local-density algebra already closed. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_quotientMain_and_remainder
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  _root_.Gdbh.PathCResidueFullLocalDensityClosure.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_count
    (residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
      hMain hRem)

/-- Final K-Goldbach bridge from quotient-main, signed-remainder, and any
supported singular-counting input. -/
theorem pathC_kGoldbach_of_residueQuotientRemainder_and_countingInput
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  _root_.Gdbh.PathCResidueFullLocalDensityClosure.pathC_kGoldbach_of_residueCount_and_countingInput
    (residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
      hMain hRem)
    hCounting

end PathCResidueCountToDensityClosure
end Gdbh

#print axioms
  Gdbh.PathCResidueCountToDensityClosure.residueDoubleDivisorExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
#print axioms
  Gdbh.PathCResidueCountToDensityClosure.residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
#print axioms
  Gdbh.PathCResidueCountToDensityClosure.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_quotientMain_and_remainder
