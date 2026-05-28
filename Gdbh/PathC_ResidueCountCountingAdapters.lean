/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueConstantCountClosure
import Gdbh.PathC_CountingResidualReduction

/-!
# Path C -- residue count plus explicit counting adapters

Round 47 reduced the finite-sieve side to the coefficient-bearing residue
count target
`ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant`, plus an
abstract `PathCCountingInput`.

This file exposes the supported counting-side residuals directly at that
reduced residue target.  It keeps the final route focused on the two remaining
worker outputs:

* the coefficient-bearing residue count target;
* one explicit counting target, such as occupied average, no-log-loss upgrade,
  uniform lower bound, positive Schnirelmann density, or the stronger
  classical representation-bound route.
-/

namespace Gdbh
namespace PathCResidueCountCountingAdapters

open Gdbh.PathCResidueCoprimeSplitDensityConstantBridge
  (ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
open Gdbh.PathCResidueConstantCountClosure
  (finiteSieveInput_of_splitCountWithConstant
   pathC_kGoldbach_of_splitCountWithConstant_and_countingInput)
open Gdbh.PathCSingularCountingInterface
  (GoldbachSingularMultiplierOccupiedAverageBound
   GoldbachSingularMultiplierOccupiedLogToAverageUpgrade)
open Gdbh.PathCPrimesSumsetDensity (PrimesSumsetUniformLowerBound)
open Gdbh.PathCKGoldbach (primesSumset)
open Gdbh.PathCTwinAsymptotic (GoldbachRepresentationBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound)
open Gdbh.PathCCountingResidualReduction
  (pathCCountingInput_of_goldbachRepresentationBound)

/-! ## Asymptotic-density adapters -/

/-- Asymptotic-density handoff from the active coefficient-bearing residue
count target and occupied-average counting target. -/
theorem
    primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_occupiedAverage
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  Gdbh.PathCSingularCountingInterface.primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_average
    (finiteSieveInput_of_splitCountWithConstant hCount) hOcc

/-- Asymptotic-density handoff from the active residue count target and the
no-log-loss occupied-average upgrade. -/
theorem
    primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_occupiedLogUpgrade
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  Gdbh.PathCSingularCountingInterface.primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_log_upgrade
    (finiteSieveInput_of_splitCountWithConstant hCount) hUpgrade

/-- Asymptotic-density handoff from the active residue count target and a
uniform linear lower bound for `primesSumset`. -/
theorem
    primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_uniformLowerBound
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hUniform : PrimesSumsetUniformLowerBound) :
    PrimesSumsetAsymptoticLowerBound :=
  Gdbh.PathCSingularCountingInterface.primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_uniformLowerBound
    (finiteSieveInput_of_splitCountWithConstant hCount) hUniform

/-- Asymptotic-density handoff from the active residue count target and
positive Schnirelmann density of `primesSumset`. -/
theorem
    primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_schnirelmannDensity_pos
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    PrimesSumsetAsymptoticLowerBound :=
  Gdbh.PathCSingularCountingInterface.primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_schnirelmannDensity_pos
    (finiteSieveInput_of_splitCountWithConstant hCount) hσ

/-- Asymptotic-density handoff from the active residue count target and the
classical Goldbach representation-bound counting route. -/
theorem
    primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_goldbachRepresentationBound
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hRep : GoldbachRepresentationBound) :
    PrimesSumsetAsymptoticLowerBound :=
  Gdbh.PathCSingularCountingInterface.primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    (finiteSieveInput_of_splitCountWithConstant hCount)
    (pathCCountingInput_of_goldbachRepresentationBound hRep)

/-! ## Final K-Goldbach adapters -/

/-- Final Path C adapter from the active coefficient-bearing residue count
target and occupied-average counting target. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_occupiedAverage
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  Gdbh.PathCSingularCountingInterface.pathC_kGoldbach_of_finiteSieveInput_and_occupied_average
    (finiteSieveInput_of_splitCountWithConstant hCount) hOcc

/-- Final adapter from the active residue count target and the no-log-loss
occupied-average upgrade. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_occupiedLogUpgrade
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  Gdbh.PathCSingularCountingInterface.pathC_kGoldbach_of_finiteSieveInput_and_occupied_log_upgrade
    (finiteSieveInput_of_splitCountWithConstant hCount) hUpgrade

/-- Final adapter from the active residue count target and a uniform lower
bound for `primesSumset`. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_uniformLowerBound
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  Gdbh.PathCSingularCountingInterface.pathC_kGoldbach_of_finiteSieveInput_and_uniformLowerBound
    (finiteSieveInput_of_splitCountWithConstant hCount) hUniform

/-- Final adapter from the active residue count target and positive
Schnirelmann density of `primesSumset`. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_schnirelmannDensity_pos
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  Gdbh.PathCSingularCountingInterface.pathC_kGoldbach_of_finiteSieveInput_and_schnirelmannDensity_pos
    (finiteSieveInput_of_splitCountWithConstant hCount) hσ

/-- Final adapter from the active residue count target and the classical
Goldbach representation-bound counting route. -/
theorem pathC_kGoldbach_of_splitCountWithConstant_and_goldbachRepresentationBound
    (hCount :
      ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBoundWithConstant)
    (hRep : GoldbachRepresentationBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_splitCountWithConstant_and_countingInput
    hCount (pathCCountingInput_of_goldbachRepresentationBound hRep)

end PathCResidueCountCountingAdapters
end Gdbh

#print axioms
  Gdbh.PathCResidueCountCountingAdapters.primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_occupiedAverage
#print axioms
  Gdbh.PathCResidueCountCountingAdapters.primesSumsetAsymptoticLowerBound_of_splitCountWithConstant_and_uniformLowerBound
#print axioms
  Gdbh.PathCResidueCountCountingAdapters.pathC_kGoldbach_of_splitCountWithConstant_and_occupiedAverage
#print axioms
  Gdbh.PathCResidueCountCountingAdapters.pathC_kGoldbach_of_splitCountWithConstant_and_uniformLowerBound
#print axioms
  Gdbh.PathCResidueCountCountingAdapters.pathC_kGoldbach_of_splitCountWithConstant_and_goldbachRepresentationBound
