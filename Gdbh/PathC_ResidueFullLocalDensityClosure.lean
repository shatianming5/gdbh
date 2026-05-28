/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityStateExpansion
import Gdbh.PathC_ResidueSplitLocalDensityDepth

/-!
# Path C -- closed full local-density algebra chain

Round 19 closed the signed full local-density prime factorization.  This file
threads that theorem through the existing handoff bridges, so the residue
kernel route no longer carries an open local-density Euler algebra residual.

The remaining upstream worker target is the split exact-count to local-density
estimate; this file deliberately does not attempt that analytic/CRT bound.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityClosure

/-! ## Closed full local-density algebra residuals -/

/-- Closed Round 12 full local-density prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorization :
    _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.ResidueDoubleDivisorFullLocalDensityPrimeFactorization :=
  _root_.Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensityPrimeFactorization_of_signed
    _root_.Gdbh.PathCResidueFullLocalDensityStateExpansion.residueDoubleDivisorFullLocalDensitySignedPrimeFactorization

/-- Closed at-sqrt full local-density prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt :
    _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.ResidueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensitySigned.residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt_of_signed
    _root_.Gdbh.PathCResidueFullLocalDensityStateExpansion.residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt

/-- Closed full local-density Euler-product residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerProduct :
    _root_.Gdbh.PathCResidueFullLocalDensityEulerProduct.ResidueDoubleDivisorFullLocalDensityEulerProduct :=
  _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityEulerProduct_of_primeFactorization
    residueDoubleDivisorFullLocalDensityPrimeFactorization

/-- Closed at-sqrt full local-density Euler-product residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerProductAtSqrt :
    _root_.Gdbh.PathCResidueFullLocalDensityEulerProduct.ResidueDoubleDivisorFullLocalDensityEulerProductAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityEulerProductAtSqrt_of_primeFactorization
    residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt

/-- Closed all-level full local-density match with the Goldbach-density
powerset expansion. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity :
    _root_.Gdbh.PathCResidueFullLocalDensityReduction.ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity :=
  _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensity_of_primeFactorization
    residueDoubleDivisorFullLocalDensityPrimeFactorization

/-- Closed at-sqrt full local-density match with the Goldbach-density powerset
expansion. -/
theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt :
    _root_.Gdbh.PathCResidueFullLocalDensityReduction.ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensityPrimeFactor.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_primeFactorization
    residueDoubleDivisorFullLocalDensityPrimeFactorizationAtSqrt

/-- Closed at-sqrt local-density match after removing the canonical subset
cutoff. -/
theorem residueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt :
    _root_.Gdbh.PathCResidueDoubleDivisorDensityDecomposition.ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensityReduction.residueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt_of_full
    residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt

/-- Closed at-sqrt local-density Euler residual. -/
theorem residueDoubleDivisorLocalDensityEulerAtSqrt :
    _root_.Gdbh.PathCResidueDoubleDivisorDensityDecomposition.ResidueDoubleDivisorLocalDensityEulerAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensityReduction.residueDoubleDivisorLocalDensityEulerAtSqrt_of_full
    residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt

/-- Closed split local-density Euler residual in the coprime/non-coprime
coordinates used by the active residue kernel route. -/
theorem residueCoprimeSplitLocalDensityEulerAtSqrt :
    _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.ResidueCoprimeSplitLocalDensityEulerAtSqrt :=
  _root_.Gdbh.PathCResidueFullLocalDensityReduction.residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
    residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt

/-- Closed untruncated split local-density Euler residual. -/
theorem residueCoprimeSplitFullLocalDensityEulerAtSqrt :
    _root_.Gdbh.PathCResidueSplitLocalDensityDepth.ResidueCoprimeSplitFullLocalDensityEulerAtSqrt := by
  intro n hn
  have h := residueCoprimeSplitLocalDensityEulerAtSqrt n hn
  rw [
    _root_.Gdbh.PathCResidueSplitLocalDensityDepth.residueDoubleDivisorCoprimeLocalDensitySumAtSqrt_eq_full n hn,
    _root_.Gdbh.PathCResidueSplitLocalDensityDepth.residueDoubleDivisorNonCoprimeLocalDensitySumAtSqrt_eq_full n hn] at h
  exact h

/-! ## Reduced bridges for the residue kernel route -/

/-- The strict residue canonical kernel now only needs the split
count-to-density estimate on this branch. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_count
    (hCount :
      _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound) :
    _root_.Gdbh.PathCResidueBonferroniAtSqrtCanonical.BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_splitLocalDensity
    hCount residueCoprimeSplitLocalDensityEulerAtSqrt

/-- Final K-Goldbach bridge from the remaining residue count-to-density
estimate and any supported singular-counting input. -/
theorem pathC_kGoldbach_of_residueCount_and_countingInput
    (hCount :
      _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound)
    (hCounting : _root_.Gdbh.PathCSingularCountingInterface.PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.pathC_kGoldbach_of_residueCoprimeSplitDensity_and_countingInput
    hCount residueCoprimeSplitLocalDensityEulerAtSqrt hCounting

end PathCResidueFullLocalDensityClosure
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorFullLocalDensityPrimeFactorization
#print axioms
  Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt
#print axioms
  Gdbh.PathCResidueFullLocalDensityClosure.residueCoprimeSplitLocalDensityEulerAtSqrt
#print axioms
  Gdbh.PathCResidueFullLocalDensityClosure.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_count
