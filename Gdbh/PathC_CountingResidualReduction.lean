/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_KernelCountingRoute
import Gdbh.PathC_RepBoundCounting

/-!
# Path C -- counting residual reduction

This additive audit file records the exact counting-side target left by the
kernel-plus-counting route.

The corrected final route can consume any `PathCCountingInput`, but that
inductive wrapper is equivalent to the no-log-loss occupied-average upgrade,
and hence to the constant occupied-average bound.  Naming those equivalences
keeps future work focused on the real counting residual instead of treating
the wrapper as independent analytic content.
-/

namespace Gdbh
namespace PathCCountingResidualReduction

open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput
   GoldbachSingularMultiplierOccupiedAverageBound
   GoldbachSingularMultiplierOccupiedLogToAverageUpgrade
   goldbachSingularMultiplierOccupiedLogToAverageUpgrade_iff_occupiedAverage
   goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_countingInput)
open Gdbh.PathCKernelCountingRoute
  (pathC_kGoldbach_of_kernel_and_countingInput)
open Gdbh.PathCTwinAsymptotic (GoldbachRepresentationBound)
open Gdbh.PathCRepBoundCounting (repBoundAndChebyshevToAsymptotic_holds)
open Gdbh.PathCChebyshevLower (chebyshevPrimeLowerBound_holds)
open Gdbh.PathCTwinChebyshev (primesSumsetUniformLowerBound_of_asymptotic)

/-- The counting-input wrapper is exactly the no-log-loss occupied-average
upgrade, not an additional independent residual. -/
theorem pathCCountingInput_iff_occupiedLogUpgrade :
    PathCCountingInput ↔ GoldbachSingularMultiplierOccupiedLogToAverageUpgrade := by
  constructor
  · exact goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_countingInput
  · intro hUpgrade
    exact PathCCountingInput.logUpgrade hUpgrade

/-- The same counting-input wrapper is also equivalent to the constant
occupied-average bound, because the log-loss occupied-average estimate is
already closed in `PathC_SingularCountingInterface`. -/
theorem pathCCountingInput_iff_occupiedAverage :
    PathCCountingInput ↔ GoldbachSingularMultiplierOccupiedAverageBound := by
  constructor
  · intro hCounting
    exact
      (goldbachSingularMultiplierOccupiedLogToAverageUpgrade_iff_occupiedAverage).1
        ((pathCCountingInput_iff_occupiedLogUpgrade).1 hCounting)
  · intro hOcc
    exact PathCCountingInput.occupiedAverage hOcc

/-- A classical Brun-style Goldbach representation bound is one concrete way
to supply the counting input: the Schnirelmann counting theorem and Chebyshev
lower bound are already closed, leaving only `GoldbachRepresentationBound`. -/
theorem pathCCountingInput_of_goldbachRepresentationBound
    (hRep : GoldbachRepresentationBound) :
    PathCCountingInput :=
  PathCCountingInput.uniformLowerBound
    (primesSumsetUniformLowerBound_of_asymptotic
      (repBoundAndChebyshevToAsymptotic_holds
        hRep chebyshevPrimeLowerBound_holds))

/-- Kernel plus the classical Goldbach representation upper bound gives the
Path C K-Goldbach conclusion through the corrected counting route. -/
theorem pathC_kGoldbach_of_kernel_and_goldbachRepresentationBound
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hRep : GoldbachRepresentationBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_kernel_and_countingInput
    hKernel (pathCCountingInput_of_goldbachRepresentationBound hRep)

end PathCCountingResidualReduction
end Gdbh

#print axioms Gdbh.PathCCountingResidualReduction.pathCCountingInput_iff_occupiedLogUpgrade
#print axioms Gdbh.PathCCountingResidualReduction.pathCCountingInput_iff_occupiedAverage
#print axioms Gdbh.PathCCountingResidualReduction.pathCCountingInput_of_goldbachRepresentationBound
#print axioms Gdbh.PathCCountingResidualReduction.pathC_kGoldbach_of_kernel_and_goldbachRepresentationBound
