/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex Round 3 controller
-/
import Gdbh.PathC_LocalMainTermRefinedAtSqrtClosure
import Gdbh.PathC_SingularCountingInterface

/-!
# Path C — kernel plus counting-input route

This file records the highest-score current final-chain route found by the
master controller.

The older headline route in `PathC_KGoldbachUnconditional` consumes four
residuals:

* `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`;
* `SingularSeriesMertens3Bound`;
* `AtSqrtFixAStrongToUniversal`;
* `WeightedSchnirelmannResidualBridge`.

The corrected singular-counting interface already supports a more direct
route: a finite-sieve worker output plus a counting worker output implies the
Path C K-Goldbach conclusion.  Since the kernel is definitionally the
at-sqrt residue-sifted refined upper bound, it is already a supported
`PathCFiniteSieveInput`.

This does not close Path C unconditionally.  It replaces three risky bridge
obligations by the explicit counting residual `PathCCountingInput`, giving the
controller a clearer high-score target.
-/

namespace Gdbh
namespace PathCKernelCountingRoute

open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput
   GoldbachSingularMultiplierOccupiedAverageBound
   GoldbachSingularMultiplierOccupiedLogToAverageUpgrade
   pathC_kGoldbach_of_finiteSieveInput_and_countingInput
   pathC_kGoldbach_of_finiteSieveInput_and_occupied_average
   pathC_kGoldbach_of_finiteSieveInput_and_occupied_log_upgrade
   pathC_kGoldbach_of_finiteSieveInput_and_uniformLowerBound
   pathC_kGoldbach_of_finiteSieveInput_and_schnirelmannDensity_pos)
open Gdbh.PathCPrimesSumsetDensity (PrimesSumsetUniformLowerBound)
open Gdbh.PathCKGoldbach (primesSumset)

/-- The kernel residual is directly usable as a supported finite-sieve input
for the corrected singular-counting Path C route. -/
theorem finiteSieveInput_of_kernel
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    PathCFiniteSieveInput :=
  PathCFiniteSieveInput.atSqrtRefined hKernel

/-- **Kernel + counting-input final route.**

This is the score-preferred connector: once the kernel finite-sieve estimate
and any supported counting input are available, Path C K-Goldbach follows
without going through the old `SingularSeriesMertens3Bound`,
`AtSqrtFixAStrongToUniversal`, or `WeightedSchnirelmannResidualBridge`
route. -/
theorem pathC_kGoldbach_of_kernel_and_countingInput
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    (finiteSieveInput_of_kernel hKernel) hCounting

/-- Kernel route specialised to the occupied-average counting residual. -/
theorem pathC_kGoldbach_of_kernel_and_occupied_average
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_occupied_average
    (finiteSieveInput_of_kernel hKernel) hOcc

/-- Kernel route specialised to the no-log-loss occupied-average upgrade. -/
theorem pathC_kGoldbach_of_kernel_and_occupied_log_upgrade
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_occupied_log_upgrade
    (finiteSieveInput_of_kernel hKernel) hUpgrade

/-- Kernel route specialised to a uniform lower-bound counting residual. -/
theorem pathC_kGoldbach_of_kernel_and_uniformLowerBound
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_uniformLowerBound
    (finiteSieveInput_of_kernel hKernel) hUniform

/-- Kernel route specialised to positive Schnirelmann density of
`primesSumset`. -/
theorem pathC_kGoldbach_of_kernel_and_schnirelmannDensity_pos
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_schnirelmannDensity_pos
    (finiteSieveInput_of_kernel hKernel) hσ

end PathCKernelCountingRoute
end Gdbh

#print axioms Gdbh.PathCKernelCountingRoute.finiteSieveInput_of_kernel
#print axioms Gdbh.PathCKernelCountingRoute.pathC_kGoldbach_of_kernel_and_countingInput
#print axioms Gdbh.PathCKernelCountingRoute.pathC_kGoldbach_of_kernel_and_occupied_average
#print axioms Gdbh.PathCKernelCountingRoute.pathC_kGoldbach_of_kernel_and_occupied_log_upgrade
#print axioms Gdbh.PathCKernelCountingRoute.pathC_kGoldbach_of_kernel_and_uniformLowerBound
#print axioms Gdbh.PathCKernelCountingRoute.pathC_kGoldbach_of_kernel_and_schnirelmannDensity_pos
