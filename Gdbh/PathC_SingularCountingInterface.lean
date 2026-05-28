import Gdbh.PathC_Final
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_GoldbachResidues
import Gdbh.PathC_LocalToSingular
import Gdbh.PathC_SingularAverage

/-!
# Path C -- Singular-factor counting interface

The honest Goldbach sieve naturally gives a representation bound with an
`n`-dependent singular multiplier.  The existing final Path C endpoint
consumes a uniform `GoldbachRepresentationBound`, so this file isolates the
missing counting bridge needed to use the singular-factor statement directly.

The all-integers average of the singular multiplier is now closed via
`PathC_SingularAverage`.  The occupied-sumset average remains a separate,
stronger counting input because it preserves the `countingUpTo primesSumset N`
factor used by the weighted Schnirelmann argument.
-/

namespace Gdbh
namespace PathCSingularCountingInterface

open scoped BigOperators
open Gdbh.PathCGoldbachLocalFactor
  (BrunGoldbachLocalMainTermRefined GoldbachRepresentationBoundWithSingularFactor
   BrunGoldbachLocalMainTermRefinedWithErrorConstant BrunGoldbachLocalMainTermRefinedAtSqrt
   BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant
   brunGoldbachLocalMainTermRefined_of_paired goldbachSingularMultiplier)
open Gdbh.PathCBrunRefinedComposition (BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCGoldbachResidues
  (BrunGoldbachResidueMainTermRefined BrunGoldbachResidueMainTermWithError
   BrunGoldbachResidueSiftedUpperBoundWithError
   GoldbachResidueSiftedRefinedUpperBound
   GoldbachResidueSiftedRefinedUpperBoundForLargeZ
   GoldbachResidueSiftedRefinedUpperBoundAtSqrt
   GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   GoldbachResidueSiftedBoundedErrorData
   GoldbachResidueSiftedAtSqrtBoundedErrorData
   GoldbachResidueErrorDominatedByRefined GoldbachResidueErrorBoundedByRefined
   BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
   GoldbachResidueErrorBoundedByRefinedAtSqrt
   brunGoldbachLocalMainTermRefined_of_residueMainTerm
   brunGoldbachResidueMainTermRefined_of_error_dominated
   brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound
   goldbachResidueSiftedAtSqrtBoundedErrorData_of_boundedErrorData
   goldbachResidueSiftedBoundedErrorData_of_refinedUpperBound
   goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_refinedUpperBound
   goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_forLargeZ
   goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt
   goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
   goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
   brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residue_error_bound)
open Gdbh.PathCLocalToSingular
  (goldbachRepresentationBoundWithSingularFactor_of_local_main
   goldbachRepresentationBoundWithSingularFactor_of_local_main_with_error_constant
   goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt
   goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant
   goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBound
   goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundForLargeZ
   goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrt
   goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   one_le_goldbachSingularMultiplier)
open Gdbh.PathCRepBoundCounting
  (weightedRepBoundAndOccupiedAverageToAsymptotic)
open Gdbh.PathCSingularAverage
  (sum_goldbachSingularMultiplier_le_two_mul_N)
open Gdbh.PathCKGoldbach (primesSumset primesSumset_zero primesSumset_one
  BoundedBasisFromPositiveDensity exists_K_goldbach_generic_of_bounded_basis
  boundedBasisFromPositiveDensity_of_schnirelmannBasisHalfDensity)
open Gdbh.PathCPrimesDensity (primesAndOne primesAndOne_zero primesAndOne_of_prime)
open Gdbh.PathCBasisHalfDensity (schnirelmannBasisHalfDensity_holds)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound
  PrimesSumsetUniformLowerBound
  primesSumsetDensity_pos_of_uniformLowerBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound
  primesSumsetUniformLowerBound_of_asymptotic)
open Gdbh.PathCChebyshevLower (chebyshevPrimeLowerBound_holds)

/-- Average-order control needed before a singular-factor representation
bound can feed the Schnirelmann counting argument. -/
def GoldbachSingularMultiplierAverageBound : Prop :=
  ∃ A : ℝ, ∃ N₀ : ℕ, 0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤ A * (N : ℝ)

/-- The global all-integers average of the corrected Goldbach singular
multiplier is uniformly bounded. -/
theorem goldbachSingularMultiplierAverageBound_holds :
    GoldbachSingularMultiplierAverageBound := by
  refine ⟨2, 0, by norm_num, ?_⟩
  intro N _hN
  simpa using sum_goldbachSingularMultiplier_le_two_mul_N N

/-- Weighted average control on the actual occupied Goldbach sumset values.

The all-integers average of the singular multiplier is a natural independent
target, but by itself it does not preserve the `countingUpTo primesSumset N`
factor in the Schnirelmann counting argument.  The direct singular-factor
counting route needs this occupied-set version, or an equivalent bridge that
controls the same weighted sum. -/
def GoldbachSingularMultiplierOccupiedAverageBound : Prop :=
  ∃ A : ℝ, ∃ N₀ : ℕ, 0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ (Finset.Icc 2 N).filter primesSumset,
        goldbachSingularMultiplier n) ≤
      A * (Gdbh.countingUpTo primesSumset N : ℝ)

/-- Every prime counted by `Nat.primeCounting N` contributes to
`countingUpTo primesSumset N`, since `p = 0 + p` with both summands in
`primesAndOne`. -/
theorem primeCounting_le_countingUpTo_primesSumset (N : ℕ) :
    Nat.primeCounting N ≤ Gdbh.countingUpTo primesSumset N := by
  classical
  have hcard : ((Finset.Icc 1 N).filter Nat.Prime).card = Nat.primeCounting N := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    apply Finset.card_bij (fun p _ => p)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hmem, hprime⟩
      rcases Finset.mem_Icc.mp hmem with ⟨_, hle⟩
      refine Finset.mem_filter.mpr ⟨?_, hprime⟩
      rw [Finset.mem_range]
      omega
    · intros _ _ _ _ h
      exact h
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hrange, hprime⟩
      refine ⟨p, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, hprime⟩
      refine Finset.mem_Icc.mpr ⟨hprime.one_lt.le, ?_⟩
      rw [Finset.mem_range] at hrange
      omega
  have hsub : ((Finset.Icc 1 N).filter Nat.Prime) ⊆
      (Finset.range (N + 1)).filter (fun k => 1 ≤ k ∧ primesSumset k) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpprime⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp1, hpN⟩
    refine Finset.mem_filter.mpr ⟨?_, hp1, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · unfold primesSumset
      rw [Gdbh.sumset_iff]
      exact ⟨0, p, primesAndOne_zero, primesAndOne_of_prime hpprime, by simp⟩
  have hle := Finset.card_le_card hsub
  simpa [Gdbh.countingUpTo, hcard] using hle

/-- Logarithmic lower bound for the occupied Goldbach sumset counting
function.  This is the unconditional density information obtained just from
the fact that every prime lies in `primesSumset`. -/
def PrimesSumsetLogLowerBound : Prop :=
  ∃ c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ ∀ N : ℕ, N₀ ≤ N →
    c * (N : ℝ) / Real.log (N : ℝ) ≤
      (Gdbh.countingUpTo primesSumset N : ℝ)

/-- Chebyshev's prime-counting lower bound gives a logarithmic lower bound
for the occupied sumset counting function.  This is useful as a diagnostic:
it is still weaker than the linear lower bound needed for Schnirelmann
positivity. -/
theorem primesSumset_log_lower_bound_of_chebyshev
    (hCheb : ChebyshevPrimeLowerBound) :
    PrimesSumsetLogLowerBound := by
  obtain ⟨c, N₀, hc_pos, hcheb⟩ := hCheb
  refine ⟨c, N₀, hc_pos, ?_⟩
  intro N hN
  have hprime_le_count : (Nat.primeCounting N : ℝ) ≤
      (Gdbh.countingUpTo primesSumset N : ℝ) := by
    exact_mod_cast primeCounting_le_countingUpTo_primesSumset N
  exact (hcheb N hN).trans hprime_le_count

/-- Unconditional logarithmic lower bound for the occupied Goldbach sumset. -/
theorem primesSumsetLogLowerBound_holds :
    PrimesSumsetLogLowerBound :=
  primesSumset_log_lower_bound_of_chebyshev chebyshevPrimeLowerBound_holds

/-- Log-loss occupied-average control.  This follows from the global average
bound and Chebyshev lower bound because `primesSumset` contains all primes.

The extra `Real.log N` factor is precisely the loss that prevents this from
being the constant occupied-average bound required by
`GoldbachSingularMultiplierOccupiedAverageBound`. -/
def GoldbachSingularMultiplierOccupiedLogAverageBound : Prop :=
  ∃ A : ℝ, ∃ N₀ : ℕ, 0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ (Finset.Icc 2 N).filter primesSumset,
        goldbachSingularMultiplier n) ≤
      A * Real.log (N : ℝ) * (Gdbh.countingUpTo primesSumset N : ℝ)

/-- Any global average bound for the singular multiplier upgrades to
log-loss occupied-average control from a logarithmic lower bound for the
occupied sumset. -/
theorem goldbachSingularMultiplierOccupiedLogAverageBound_of_average_and_logLowerBound
    (hAvg : GoldbachSingularMultiplierAverageBound)
    (hLog : PrimesSumsetLogLowerBound) :
    GoldbachSingularMultiplierOccupiedLogAverageBound := by
  classical
  obtain ⟨A₀, N_A, hA₀_pos, hAvgBd⟩ := hAvg
  obtain ⟨c, N_C, hc_pos, hcount⟩ := hLog
  refine ⟨A₀ / c, max (max N_A N_C) 3, by positivity, ?_⟩
  intro N hN
  have hNA : N_A ≤ N := by omega
  have hNC : N_C ≤ N := by omega
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hcount_lower : c * (N : ℝ) / Real.log (N : ℝ) ≤
      (Gdbh.countingUpTo primesSumset N : ℝ) := by
    exact hcount N hNC
  have hfactor_nonneg : 0 ≤ (A₀ / c) * Real.log (N : ℝ) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcount_lower hfactor_nonneg
  have havgN_le : A₀ * (N : ℝ) ≤
      (A₀ / c) * Real.log (N : ℝ) *
        (Gdbh.countingUpTo primesSumset N : ℝ) := by
    have hlhs' : (A₀ / c) * Real.log (N : ℝ) *
          (c * (N : ℝ) / Real.log (N : ℝ)) = A₀ * (N : ℝ) := by
      field_simp [ne_of_gt hc_pos, ne_of_gt hlog_pos]
    linarith [hmul, hlhs']
  have hocc_le_all :
      (∑ n ∈ (Finset.Icc 2 N).filter primesSumset,
          goldbachSingularMultiplier n) ≤
        ∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _hx _hxnot => by
        have h := one_le_goldbachSingularMultiplier x
        linarith)
  have hall_le :
      (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤
        A₀ * (N : ℝ) :=
    hAvgBd N hNA
  exact hocc_le_all.trans (hall_le.trans havgN_le)

/-- The closed global singular-multiplier average upgrades to log-loss
occupied-average control from any logarithmic lower bound for the occupied
sumset. -/
theorem goldbachSingularMultiplierOccupiedLogAverageBound_of_logLowerBound
    (hLog : PrimesSumsetLogLowerBound) :
    GoldbachSingularMultiplierOccupiedLogAverageBound :=
  goldbachSingularMultiplierOccupiedLogAverageBound_of_average_and_logLowerBound
    goldbachSingularMultiplierAverageBound_holds hLog

/-- The corrected singular multiplier has log-loss occupied-average control
under Chebyshev's prime-counting lower bound. -/
theorem goldbachSingularMultiplierOccupiedLogAverageBound_of_chebyshev
    (hCheb : ChebyshevPrimeLowerBound) :
    GoldbachSingularMultiplierOccupiedLogAverageBound :=
  goldbachSingularMultiplierOccupiedLogAverageBound_of_logLowerBound
    (primesSumset_log_lower_bound_of_chebyshev hCheb)

/-- Unconditional log-loss occupied-average control for the corrected
singular multiplier. -/
theorem goldbachSingularMultiplierOccupiedLogAverageBound_holds :
    GoldbachSingularMultiplierOccupiedLogAverageBound :=
  goldbachSingularMultiplierOccupiedLogAverageBound_of_chebyshev
    chebyshevPrimeLowerBound_holds

/-- Once a linear asymptotic lower bound for `primesSumset` is available,
the global singular-multiplier average automatically upgrades to the
occupied-average bound needed by the weighted counting bridge. -/
theorem goldbachSingularMultiplierOccupiedAverageBound_of_asymptoticLowerBound
    (hAsym : PrimesSumsetAsymptoticLowerBound) :
    GoldbachSingularMultiplierOccupiedAverageBound := by
  classical
  obtain ⟨ε, N₀, hε_pos, hbd⟩ := hAsym
  refine ⟨2 / ε, N₀, by positivity, ?_⟩
  intro N hN
  have hocc_le_all :
      (∑ n ∈ (Finset.Icc 2 N).filter primesSumset,
          goldbachSingularMultiplier n) ≤
        ∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _hx _hxnot => by
        have h := one_le_goldbachSingularMultiplier x
        linarith)
  have hall_le :
      (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤
        2 * (N : ℝ) :=
    sum_goldbachSingularMultiplier_le_two_mul_N N
  have hcount : ε * (N : ℝ) ≤
      (Gdbh.countingUpTo primesSumset N : ℝ) :=
    hbd N hN
  have hfactor_nonneg : 0 ≤ 2 / ε := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hfactor_nonneg
  have htwoN_le :
      2 * (N : ℝ) ≤
        (2 / ε) * (Gdbh.countingUpTo primesSumset N : ℝ) := by
    calc
      2 * (N : ℝ) = (2 / ε) * (ε * (N : ℝ)) := by
        field_simp [ne_of_gt hε_pos]
      _ ≤ (2 / ε) * (Gdbh.countingUpTo primesSumset N : ℝ) := hmul
  exact hocc_le_all.trans (hall_le.trans htwoN_le)

/-- A uniform linear lower bound on `primesSumset` is, in particular, the
eventual linear lower bound used by the singular counting route. -/
theorem primesSumsetAsymptoticLowerBound_of_uniformLowerBound
    (hUniform : PrimesSumsetUniformLowerBound) :
    PrimesSumsetAsymptoticLowerBound := by
  obtain ⟨ε, hε_pos, hbd⟩ := hUniform
  refine ⟨ε, 1, hε_pos, ?_⟩
  intro N hN
  exact hbd N hN

/-- A uniform linear lower bound on `primesSumset` gives the occupied-average
bound for the singular multiplier. -/
theorem goldbachSingularMultiplierOccupiedAverageBound_of_uniformLowerBound
    (hUniform : PrimesSumsetUniformLowerBound) :
    GoldbachSingularMultiplierOccupiedAverageBound :=
  goldbachSingularMultiplierOccupiedAverageBound_of_asymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_uniformLowerBound hUniform)

/-- Positive Schnirelmann density of `primesSumset` gives the eventual
linear lower bound used by the singular counting route. -/
theorem primesSumsetAsymptoticLowerBound_of_schnirelmannDensity_pos
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    PrimesSumsetAsymptoticLowerBound := by
  classical
  refine ⟨Gdbh.schnirelmannDensity primesSumset / 2, 1, by positivity, ?_⟩
  intro N hN
  have hσ_le_term :
      Gdbh.schnirelmannDensity primesSumset ≤
        Gdbh.schnirelmannTerm primesSumset N :=
    ciInf_le (Gdbh.bddBelow_range_schnirelmannTerm primesSumset) N
  have hterm_eq :
      Gdbh.schnirelmannTerm primesSumset N =
        (Gdbh.countingUpTo primesSumset N : ℝ) / N := by
    unfold Gdbh.schnirelmannTerm
    simp [hN]
  have hσ_le_ratio :
      Gdbh.schnirelmannDensity primesSumset ≤
        (Gdbh.countingUpTo primesSumset N : ℝ) / N := by
    simpa [hterm_eq] using hσ_le_term
  have hN_pos : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hhalf_le :
      Gdbh.schnirelmannDensity primesSumset / 2 ≤
        Gdbh.schnirelmannDensity primesSumset := by
    linarith
  calc
    Gdbh.schnirelmannDensity primesSumset / 2 * (N : ℝ)
        ≤ Gdbh.schnirelmannDensity primesSumset * (N : ℝ) := by
          exact mul_le_mul_of_nonneg_right hhalf_le (by positivity)
    _ ≤ ((Gdbh.countingUpTo primesSumset N : ℝ) / N) * (N : ℝ) := by
          exact mul_le_mul_of_nonneg_right hσ_le_ratio (by positivity)
    _ = (Gdbh.countingUpTo primesSumset N : ℝ) := by
          field_simp [ne_of_gt hN_pos]

/-- Positive Schnirelmann density of `primesSumset` is enough to remove the
occupied-average counting loss, because the global singular-multiplier
average is already closed. -/
theorem goldbachSingularMultiplierOccupiedAverageBound_of_schnirelmannDensity_pos
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    GoldbachSingularMultiplierOccupiedAverageBound :=
  goldbachSingularMultiplierOccupiedAverageBound_of_asymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_schnirelmannDensity_pos hσ)

/-- Exact remaining upgrade after the unconditional log-loss bound: remove
the logarithmic loss from occupied-average control. -/
def GoldbachSingularMultiplierOccupiedLogToAverageUpgrade : Prop :=
  GoldbachSingularMultiplierOccupiedLogAverageBound →
    GoldbachSingularMultiplierOccupiedAverageBound

/-- Since the log-loss occupied-average bound is already closed, the
log-to-average upgrade is equivalent to the constant occupied-average bound
itself.  This is the exact counting target left for the counting worker. -/
theorem goldbachSingularMultiplierOccupiedLogToAverageUpgrade_iff_occupiedAverage :
    GoldbachSingularMultiplierOccupiedLogToAverageUpgrade ↔
      GoldbachSingularMultiplierOccupiedAverageBound := by
  constructor
  · intro hUpgrade
    exact hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds
  · intro hOcc _hLog
    exact hOcc

/-- A linear asymptotic lower bound for `primesSumset` is one sufficient way
to remove the logarithmic loss from occupied-average control. -/
theorem goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_asymptoticLowerBound
    (hAsym : PrimesSumsetAsymptoticLowerBound) :
    GoldbachSingularMultiplierOccupiedLogToAverageUpgrade := by
  intro _hLog
  exact goldbachSingularMultiplierOccupiedAverageBound_of_asymptoticLowerBound hAsym

/-- A uniform linear lower bound on `primesSumset` is also sufficient for the
no-log-loss occupied-average upgrade. -/
theorem goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_uniformLowerBound
    (hUniform : PrimesSumsetUniformLowerBound) :
    GoldbachSingularMultiplierOccupiedLogToAverageUpgrade := by
  intro _hLog
  exact goldbachSingularMultiplierOccupiedAverageBound_of_uniformLowerBound hUniform

/-- Positive Schnirelmann density of `primesSumset` is a sufficient counting
target for the no-log-loss occupied-average upgrade. -/
theorem goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_schnirelmannDensity_pos
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    GoldbachSingularMultiplierOccupiedLogToAverageUpgrade := by
  intro _hLog
  exact goldbachSingularMultiplierOccupiedAverageBound_of_schnirelmannDensity_pos hσ

/-- The corrected counting bridge: a singular-factor Goldbach representation
bound, plus average control of the singular multiplier and Chebyshev, implies
the asymptotic lower bound for the prime sumset. -/
def SingularRepBoundAndChebyshevToAsymptotic : Prop :=
  GoldbachRepresentationBoundWithSingularFactor →
    GoldbachSingularMultiplierAverageBound →
      ChebyshevPrimeLowerBound → PrimesSumsetAsymptoticLowerBound

/-- Corrected weighted counting bridge for the singular-factor route.  This is
the bridge shape that retains the number of occupied sum values rather than
discarding it into a global average over all integers. -/
def SingularRepBoundAndOccupiedAverageToAsymptotic : Prop :=
  GoldbachRepresentationBoundWithSingularFactor →
    GoldbachSingularMultiplierOccupiedAverageBound →
      ChebyshevPrimeLowerBound → PrimesSumsetAsymptoticLowerBound

/-- The occupied-average singular counting bridge is the weighted form of the
P10 Schnirelmann counting argument. -/
theorem singularRepBoundAndOccupiedAverageToAsymptotic_holds :
    SingularRepBoundAndOccupiedAverageToAsymptotic := by
  intro hRep hOcc hCheb
  exact weightedRepBoundAndOccupiedAverageToAsymptotic
    goldbachSingularMultiplier
    (fun n => by
      have h := one_le_goldbachSingularMultiplier n
      linarith)
    hRep hOcc hCheb

private lemma exists_primesAndOne_list_of_primesSumset_list :
    ∀ (ps : List ℕ),
      (∀ p ∈ ps, primesSumset p) →
      ∃ qs : List ℕ,
        qs.length ≤ 2 * ps.length ∧
        (∀ q ∈ qs, primesAndOne q) ∧
        qs.sum = ps.sum
  | [], _ => by
    refine ⟨[], ?_, ?_, ?_⟩
    · simp
    · intro q hq
      cases hq
    · simp
  | p :: ps, hmem => by
    have hp : primesSumset p := hmem p (List.mem_cons_self)
    unfold primesSumset at hp
    rw [Gdbh.sumset_iff] at hp
    obtain ⟨a, b, hA, hB, _hab⟩ := hp
    have htail_mem : ∀ q ∈ ps, primesSumset q := by
      intro q hq
      exact hmem q (List.mem_cons_of_mem _ hq)
    obtain ⟨qs, hqs_len, hqs_mem, hqs_sum⟩ :=
      exists_primesAndOne_list_of_primesSumset_list ps htail_mem
    refine ⟨a :: b :: qs, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hA
      · rcases List.mem_cons.mp hq' with rfl | hq''
        · exact hB
        · exact hqs_mem q hq''
    · simp only [List.sum_cons]
      omega

/-- Direct final Path C connector from the asymptotic lower bound on the prime
sumset.  This is the reusable endpoint for both the uniform and singular
counting paths. -/
theorem pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (hAsym : PrimesSumsetAsymptoticLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  classical
  have hUniform := primesSumsetUniformLowerBound_of_asymptotic hAsym
  have hPos : 0 < Gdbh.schnirelmannDensity primesSumset :=
    primesSumsetDensity_pos_of_uniformLowerBound hUniform
  have hBasis : BoundedBasisFromPositiveDensity primesSumset :=
    boundedBasisFromPositiveDensity_of_schnirelmannBasisHalfDensity
      schnirelmannBasisHalfDensity_holds primesSumset
  obtain ⟨K, hK⟩ :=
    exists_K_goldbach_generic_of_bounded_basis primesSumset
      primesSumset_zero primesSumset_one hPos hBasis
  refine ⟨2 * (K + 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ps, hlen, hmem, hsum⟩ := hK n hn1
  obtain ⟨qs, hqs_len, hqs_mem, hqs_sum⟩ :=
    exists_primesAndOne_list_of_primesSumset_list ps hmem
  refine ⟨qs, ?_, ?_, ?_⟩
  · have : 2 * ps.length ≤ 2 * (K + 1) := by omega
    omega
  · intro q hq
    have hPA : primesAndOne q := hqs_mem q hq
    unfold Gdbh.PathCPrimesDensity.primesAndOne at hPA
    rcases hPA with h0 | h1 | hPrime
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl hPrime
  · rw [hqs_sum, hsum]

/-- Direct final Path C connector from a uniform linear lower bound on
`primesSumset`. -/
theorem pathC_kGoldbach_of_primesSumsetUniformLowerBound
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_uniformLowerBound hUniform)

/-- Direct final Path C connector from positive Schnirelmann density of
`primesSumset`.  This exposes the counting worker's positive-density target
as a complete route to the final `K`-Goldbach conclusion. -/
theorem pathC_kGoldbach_of_primesSumset_schnirelmannDensity_pos
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_schnirelmannDensity_pos hσ)

/-- Final Path C connector for the corrected singular-factor route.  The
remaining open content is exactly the singular counting bridge plus average
control of the multiplier. -/
theorem pathC_kGoldbach_of_singular_counting_bridge
    (hRep : GoldbachRepresentationBoundWithSingularFactor)
    (hAvg : GoldbachSingularMultiplierAverageBound)
    (hBridge : SingularRepBoundAndChebyshevToAsymptotic) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (hBridge hRep hAvg chebyshevPrimeLowerBound_holds)

/-- After the Mertens/Abel local-factor closure, the corrected Path C route
from a local Brun main term to the final `K`-Goldbach conclusion has only the
singular counting inputs left. -/
theorem pathC_kGoldbach_of_local_main_and_singular_counting
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hAvg : GoldbachSingularMultiplierAverageBound)
    (hBridge : SingularRepBoundAndChebyshevToAsymptotic) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_singular_counting_bridge
    (goldbachRepresentationBoundWithSingularFactor_of_local_main hMain)
    hAvg hBridge

/-- With the global singular multiplier average now closed, this connector
leaves only the local Brun main term and the global-average counting bridge. -/
theorem pathC_kGoldbach_of_local_main_and_singular_bridge
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hBridge : SingularRepBoundAndChebyshevToAsymptotic) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_singular_counting
    hMain goldbachSingularMultiplierAverageBound_holds hBridge

/-- Final connector for the corrected occupied-average singular route.  This
is the recommended target for the next counting-proof agent team. -/
theorem pathC_kGoldbach_of_local_main_and_occupied_singular_counting
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound)
    (hBridge : SingularRepBoundAndOccupiedAverageToAsymptotic) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (hBridge
      (goldbachRepresentationBoundWithSingularFactor_of_local_main hMain)
      hOcc
      chebyshevPrimeLowerBound_holds)

/-- With the occupied-average counting bridge closed, the corrected singular
Path C route now needs only the honest local Brun main term and occupied
average control of the Goldbach singular multiplier. -/
theorem pathC_kGoldbach_of_local_main_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_singular_counting
    hMain hOcc singularRepBoundAndOccupiedAverageToAsymptotic_holds

/-- Asymptotic-density connector for the final-assembly paired local main
term at `z = Nat.sqrt n`. -/
theorem primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt hMain)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Occupied-average connector for the final-assembly paired local main term
at `z = Nat.sqrt n`.  This is the narrowest paired-sieve worker target before
the singular counting input. -/
theorem pathC_kGoldbach_of_local_main_atSqrt_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_and_occupied_average
      hMain hOcc)

/-- Asymptotic-density connector for the final-assembly paired local main
term with a fixed error constant. -/
theorem primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_with_error_constant_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant
      hMain)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Occupied-average connector for the final-assembly paired local main term
with a fixed error constant. -/
theorem pathC_kGoldbach_of_local_main_atSqrt_with_error_constant_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_with_error_constant_and_occupied_average
      hMain hOcc)

/-- Final connector for the constant-error local main-term target.  The fixed
reservoir constant is absorbed before the weighted occupied-average counting
bridge is applied. -/
theorem pathC_kGoldbach_of_local_main_error_constant_and_occupied_average
    (hMain : BrunGoldbachLocalMainTermRefinedWithErrorConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (singularRepBoundAndOccupiedAverageToAsymptotic_holds
      (goldbachRepresentationBoundWithSingularFactor_of_local_main_with_error_constant hMain)
      hOcc
      chebyshevPrimeLowerBound_holds)

/-- Occupied-average connector for the older uniform paired-factor main-term
target, routed through the corrected local factor. -/
theorem pathC_kGoldbach_of_paired_main_and_occupied_average
    (hMain : BrunGoldbachPairedMainTermRefined)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_average
    (brunGoldbachLocalMainTermRefined_of_paired hMain) hOcc

/-- Occupied-average connector for the direct residue-set finite-sieve
target. -/
theorem pathC_kGoldbach_of_residue_main_and_occupied_average
    (hMain : BrunGoldbachResidueMainTermRefined)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_average
    (brunGoldbachLocalMainTermRefined_of_residueMainTerm hMain) hOcc

/-- Occupied-average connector for a residue-set main term with an abstract
finite-sieve error reservoir dominated by `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_main_error_and_occupied_average
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorDominatedByRefined B)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_main_and_occupied_average
    (brunGoldbachResidueMainTermRefined_of_error_dominated hMain hErr) hOcc

/-- Occupied-average connector for a residue-set main term whose finite-sieve
error is bounded by a fixed constant multiple of `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_main_bounded_error_and_occupied_average
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefined B)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_error_constant_and_occupied_average
    (brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residue_error_bound
      hMain hErr)
    hOcc

/-- Occupied-average connector for the most concrete finite-sieve target:
bound the odd-prime residue-sifted count, then bound its error by a fixed
multiple of `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_sifted_bounded_error_and_occupied_average
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefined B)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_main_bounded_error_and_occupied_average
    (brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound hSift)
    hErr hOcc

/-- Occupied-average connector consuming the finite-sieve bounded-error data
bundle directly. -/
theorem pathC_kGoldbach_of_residue_sifted_bounded_error_data_and_occupied_average
    (data : GoldbachResidueSiftedBoundedErrorData)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_bounded_error_and_occupied_average
    data.upperBound data.errorBound hOcc

/-- Asymptotic-density connector for the canonical refined-error
residue-sifted target.  This is the clean intermediate output before the
final Schnirelmann basis endpoint. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_and_occupied_average
    (hUpper : GoldbachResidueSiftedRefinedUpperBound)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBound hUpper)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Asymptotic-density connector for the large-sieve-range refined-error
residue-sifted target.  The small-threshold cases are discharged upstream by
`goldbachResidueSiftedRefinedUpperBound_of_forLargeZ`. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_forLargeZ_and_occupied_average
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundForLargeZ
      hLarge)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Asymptotic-density connector for the final-assembly residue-sifted target
at `z = Nat.sqrt n`. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_and_occupied_average
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrt
      hSift)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Occupied-average connector for the canonical refined-error residue-sifted
finite-sieve target.  This leaves only the refined upper-bound field, with
the error reservoir fixed to `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_and_occupied_average
    (hUpper : GoldbachResidueSiftedRefinedUpperBound)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_and_occupied_average
      hUpper hOcc)

/-- Occupied-average connector for the large-sieve-range refined-error
residue-sifted target. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_forLargeZ_and_occupied_average
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_forLargeZ_and_occupied_average
      hLarge hOcc)

/-- Occupied-average connector for the final-assembly residue-sifted target
at `z = Nat.sqrt n`. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_and_occupied_average
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_and_occupied_average
      hSift hOcc)

/-- Asymptotic-density connector for the final-assembly residue-sifted target
at `z = Nat.sqrt n` with a fixed error constant. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  singularRepBoundAndOccupiedAverageToAsymptotic_holds
    (goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
      hSift)
    hOcc
    chebyshevPrimeLowerBound_holds

/-- Occupied-average connector for the final-assembly residue-sifted target
at `z = Nat.sqrt n` with a fixed error constant. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
      hSift hOcc)

/-- Occupied-average connector for split at-sqrt finite-sieve work: one
worker proves the abstract-error upper bound and another proves at-sqrt error
domination by the refined reservoir. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_occupied_average
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
      hSift hErr)
    hOcc

/-- Occupied-average connector consuming the split at-sqrt finite-sieve data
bundle directly. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_average
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
      data)
    hOcc

/-- Connector exposing the exact remaining work after the unconditional
log-loss occupied-average bound: prove the no-log-loss upgrade. -/
theorem pathC_kGoldbach_of_local_main_and_occupied_log_upgrade
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_average
    hMain (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Asymptotic-density connector for the final-assembly paired local main
term, using the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_and_occupied_log_upgrade
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_and_occupied_average
    hMain (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Log-upgrade connector for the final-assembly paired local main term at
`z = Nat.sqrt n`. -/
theorem pathC_kGoldbach_of_local_main_atSqrt_and_occupied_log_upgrade
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_and_occupied_log_upgrade
      hMain hUpgrade)

/-- Asymptotic-density connector for the final-assembly paired local main
term with a fixed error constant, using the no-log-loss occupied-average
upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_with_error_constant_and_occupied_log_upgrade
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_with_error_constant_and_occupied_average
    hMain (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Log-upgrade connector for the final-assembly paired local main term with
a fixed error constant. -/
theorem pathC_kGoldbach_of_local_main_atSqrt_with_error_constant_and_occupied_log_upgrade
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_local_main_atSqrt_with_error_constant_and_occupied_log_upgrade
      hMain hUpgrade)

/-- Compatibility connector for the older uniform paired-factor main-term
target.  Since the corrected local factor dominates `pairedBrunFactor`, any
proof of the older refined main-term target can still feed the corrected
singular/occupied-average route. -/
theorem pathC_kGoldbach_of_paired_main_and_occupied_log_upgrade
    (hMain : BrunGoldbachPairedMainTermRefined)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_log_upgrade
    (brunGoldbachLocalMainTermRefined_of_paired hMain) hUpgrade

/-- Final connector for the direct residue-set finite-sieve target.  This is
the most concrete corrected target for a Halberstam-Richert/Brun worker:
prove the paired-sift main term with local density given by
`goldbachBadResidueSet`. -/
theorem pathC_kGoldbach_of_residue_main_and_occupied_log_upgrade
    (hMain : BrunGoldbachResidueMainTermRefined)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_and_occupied_log_upgrade
    (brunGoldbachLocalMainTermRefined_of_residueMainTerm hMain) hUpgrade

/-- Log-upgrade connector for a residue-set main term with an abstract
finite-sieve error reservoir dominated by `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_main_error_and_occupied_log_upgrade
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorDominatedByRefined B)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_main_and_occupied_log_upgrade
    (brunGoldbachResidueMainTermRefined_of_error_dominated hMain hErr)
    hUpgrade

/-- Log-upgrade connector for a residue-set main term whose finite-sieve
error is bounded by a fixed constant multiple of `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_main_bounded_error_and_occupied_log_upgrade
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefined B)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_local_main_error_constant_and_occupied_average
    (brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residue_error_bound
      hMain hErr)
    (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Log-upgrade connector for the most concrete finite-sieve target:
bound the odd-prime residue-sifted count, then bound its error by a fixed
multiple of `refinedReservoir`. -/
theorem pathC_kGoldbach_of_residue_sifted_bounded_error_and_occupied_log_upgrade
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefined B)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_main_bounded_error_and_occupied_log_upgrade
    (brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound hSift)
    hErr hUpgrade

/-- Log-upgrade connector consuming the finite-sieve bounded-error data
bundle directly. -/
theorem pathC_kGoldbach_of_residue_sifted_bounded_error_data_and_occupied_log_upgrade
    (data : GoldbachResidueSiftedBoundedErrorData)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_bounded_error_and_occupied_log_upgrade
    data.upperBound data.errorBound hUpgrade

/-- Asymptotic-density connector for the canonical refined-error
residue-sifted target, using the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_and_occupied_log_upgrade
    (hUpper : GoldbachResidueSiftedRefinedUpperBound)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_and_occupied_average
    hUpper (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Asymptotic-density connector for the large-sieve-range refined-error
residue-sifted target, using the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_forLargeZ_and_occupied_log_upgrade
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_forLargeZ_and_occupied_average
    hLarge (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Asymptotic-density connector for the final-assembly residue-sifted target
at `z = Nat.sqrt n`, using the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_and_occupied_log_upgrade
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_and_occupied_average
    hSift (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Asymptotic-density connector for the final-assembly residue-sifted target
with a fixed error constant, using the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    hSift (hUpgrade goldbachSingularMultiplierOccupiedLogAverageBound_holds)

/-- Log-upgrade connector for the canonical refined-error residue-sifted
finite-sieve target.  The finite-sieve worker now proves exactly
`GoldbachResidueSiftedRefinedUpperBound`; the remaining counting worker proves
the no-log-loss occupied-average upgrade. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_and_occupied_log_upgrade
    (hUpper : GoldbachResidueSiftedRefinedUpperBound)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_and_occupied_log_upgrade
      hUpper hUpgrade)

/-- Log-upgrade connector for the large-sieve-range refined-error
residue-sifted target.  This is the narrowest current two-worker Path C
route: finite-sieve work only for `3 ≤ z`, plus the counting upgrade. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_forLargeZ_and_occupied_log_upgrade
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_forLargeZ_and_occupied_log_upgrade
      hLarge hUpgrade)

/-- Log-upgrade connector for the final-assembly residue-sifted target at
`z = Nat.sqrt n`.  This is the narrowest current Path C route: one eventual
finite-sieve estimate at the actual assembly threshold plus the counting
upgrade. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_and_occupied_log_upgrade
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_and_occupied_log_upgrade
      hSift hUpgrade)

/-- Log-upgrade connector for the final-assembly residue-sifted target at
`z = Nat.sqrt n` with a fixed error constant.  This is the narrowest practical
two-worker Path C route: one eventual finite-sieve estimate plus the counting
upgrade. -/
theorem pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
      hSift hUpgrade)

/-- Log-upgrade connector for split at-sqrt finite-sieve work.  This is the
most parallel worker-friendly route: prove an abstract-error sieve upper
bound, prove the at-sqrt error domination, and prove the counting upgrade. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_occupied_log_upgrade
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
      hSift hErr)
    hUpgrade

/-- Log-upgrade connector consuming the split at-sqrt finite-sieve data bundle
directly. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_log_upgrade
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
      data)
    hUpgrade

/-- Full split-worker Path C data using the occupied-average counting target.
The finite-sieve fields can be proved independently from the counting field,
then handed to this integrator-facing bundle. -/
structure PathCAtSqrtSplitOccupiedAverageData where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  occupiedAverage : GoldbachSingularMultiplierOccupiedAverageBound

/-- Full split-worker Path C data using the no-log-loss occupied-average
upgrade.  This is the preferred agent-team handoff shape because the
unconditional log-loss bound is already closed. -/
structure PathCAtSqrtSplitLogUpgradeData where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  logUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade

/-- Full split-worker Path C data using a uniform linear lower bound on
`primesSumset` as the counting worker output. -/
structure PathCAtSqrtSplitUniformLowerBoundData where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  uniformLowerBound : PrimesSumsetUniformLowerBound

/-- Full split-worker Path C data using positive Schnirelmann density of
`primesSumset` as the counting worker output. -/
structure PathCAtSqrtSplitSchnirelmannDensityData where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  schnirelmannDensityPos : 0 < Gdbh.schnirelmannDensity primesSumset

/-- Counting worker output for the split at-sqrt Path C route.  The
constructors record the currently supported sufficient counting targets. -/
inductive PathCCountingInput : Prop where
  | occupiedAverage :
      GoldbachSingularMultiplierOccupiedAverageBound → PathCCountingInput
  | logUpgrade :
      GoldbachSingularMultiplierOccupiedLogToAverageUpgrade → PathCCountingInput
  | uniformLowerBound :
      PrimesSumsetUniformLowerBound → PathCCountingInput
  | schnirelmannDensityPos :
      0 < Gdbh.schnirelmannDensity primesSumset → PathCCountingInput

/-- Finite-sieve worker output for the split at-sqrt Path C route.  The
constructors record the supported handoff shapes, from raw split worker
fields up to stronger all-threshold targets. -/
inductive PathCFiniteSieveInput : Prop where
  | atSqrtFields {B : ℕ → ℕ → ℝ} :
      BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B →
      GoldbachResidueErrorBoundedByRefinedAtSqrt B →
      PathCFiniteSieveInput
  | atSqrtData :
      GoldbachResidueSiftedAtSqrtBoundedErrorData → PathCFiniteSieveInput
  | allThresholdData :
      GoldbachResidueSiftedBoundedErrorData → PathCFiniteSieveInput
  | atSqrtWithErrorConstant :
      GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant →
        PathCFiniteSieveInput
  | atSqrtRefined :
      GoldbachResidueSiftedRefinedUpperBoundAtSqrt → PathCFiniteSieveInput
  | refinedUpper :
      GoldbachResidueSiftedRefinedUpperBound → PathCFiniteSieveInput
  | forLargeZ :
      GoldbachResidueSiftedRefinedUpperBoundForLargeZ → PathCFiniteSieveInput

/-- Full split-worker Path C data using any supported counting worker output. -/
structure PathCAtSqrtSplitCountingData where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  counting : PathCCountingInput

/-- Fully unified Path C input data: one finite-sieve worker output plus one
counting worker output. -/
structure PathCUnifiedInputData where
  finiteSieve : PathCFiniteSieveInput
  counting : PathCCountingInput

/-- Any supported counting worker output gives the no-log-loss occupied
average upgrade consumed by the final split at-sqrt route. -/
theorem goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_countingInput :
    PathCCountingInput →
      GoldbachSingularMultiplierOccupiedLogToAverageUpgrade := by
  intro hCounting
  cases hCounting with
  | occupiedAverage hOcc =>
      exact
        (goldbachSingularMultiplierOccupiedLogToAverageUpgrade_iff_occupiedAverage).2
          hOcc
  | logUpgrade hUpgrade =>
      exact hUpgrade
  | uniformLowerBound hUniform =>
      exact goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_uniformLowerBound
        hUniform
  | schnirelmannDensityPos hσ =>
      exact
        goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_schnirelmannDensity_pos
          hσ

/-- Any supported finite-sieve worker output gives the final-assembly
constant-error at-sqrt finite-sieve target. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_finiteSieveInput :
    PathCFiniteSieveInput →
      GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant := by
  intro hFinite
  cases hFinite with
  | atSqrtFields hSift hErr =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
          hSift hErr
  | atSqrtData data =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
          data
  | allThresholdData data =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
          (goldbachResidueSiftedAtSqrtBoundedErrorData_of_boundedErrorData
            data)
  | atSqrtWithErrorConstant hSift =>
      exact hSift
  | atSqrtRefined hSift =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt
          hSift
  | refinedUpper hUpper =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt
          (goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_refinedUpperBound
            hUpper)
  | forLargeZ hLarge =>
      exact
        goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt
          (goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_forLargeZ hLarge)

/-- Asymptotic-density theorem from the occupied-average team data bundle. -/
theorem primesSumsetAsymptoticLowerBound_of_atSqrt_split_occupied_average_data
    (data : PathCAtSqrtSplitOccupiedAverageData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_average
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
      data.finiteSieve)
    data.occupiedAverage

/-- Asymptotic-density theorem from the log-upgrade team data bundle. -/
theorem primesSumsetAsymptoticLowerBound_of_atSqrt_split_log_upgrade_data
    (data : PathCAtSqrtSplitLogUpgradeData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
      data.finiteSieve)
    data.logUpgrade

/-- Asymptotic-density theorem from the uniform-lower-bound team data
bundle. -/
theorem primesSumsetAsymptoticLowerBound_of_atSqrt_split_uniformLowerBound_data
    (data : PathCAtSqrtSplitUniformLowerBoundData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_atSqrt_split_log_upgrade_data
    { finiteSieve := data.finiteSieve
      logUpgrade :=
        goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_uniformLowerBound
          data.uniformLowerBound }

/-- Asymptotic-density theorem from the positive-Schnirelmann-density team
data bundle. -/
theorem primesSumsetAsymptoticLowerBound_of_atSqrt_split_schnirelmannDensity_data
    (data : PathCAtSqrtSplitSchnirelmannDensityData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_atSqrt_split_log_upgrade_data
    { finiteSieve := data.finiteSieve
      logUpgrade :=
        goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_schnirelmannDensity_pos
          data.schnirelmannDensityPos }

/-- Asymptotic-density theorem from the unified counting-input team data. -/
theorem primesSumsetAsymptoticLowerBound_of_atSqrt_split_counting_data
    (data : PathCAtSqrtSplitCountingData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_atSqrt_split_log_upgrade_data
    { finiteSieve := data.finiteSieve
      logUpgrade :=
        goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_countingInput
          data.counting }

/-- Asymptotic-density theorem from split at-sqrt finite-sieve worker fields
plus any supported counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_countingInput
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hCounting : PathCCountingInput) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_atSqrt_split_counting_data
    { finiteSieve := { B := B, upperBound := hSift, errorBound := hErr }
      counting := hCounting }

/-- Asymptotic-density theorem from any supported finite-sieve worker output
plus any supported counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    (hFinite : PathCFiniteSieveInput)
    (hCounting : PathCCountingInput) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_refined_upper_atSqrt_with_error_constant_and_occupied_log_upgrade
    (goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_finiteSieveInput
      hFinite)
    (goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_countingInput
      hCounting)

/-- Asymptotic-density theorem from any supported finite-sieve worker output
plus an occupied-average counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_average
    (hFinite : PathCFiniteSieveInput)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.occupiedAverage hOcc)

/-- Asymptotic-density theorem from any supported finite-sieve worker output
plus the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_log_upgrade
    (hFinite : PathCFiniteSieveInput)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.logUpgrade hUpgrade)

/-- Asymptotic-density theorem from any supported finite-sieve worker output
plus a uniform lower bound counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_uniformLowerBound
    (hFinite : PathCFiniteSieveInput)
    (hUniform : PrimesSumsetUniformLowerBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.uniformLowerBound hUniform)

/-- Asymptotic-density theorem from any supported finite-sieve worker output
plus positive Schnirelmann density of `primesSumset`. -/
theorem primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_schnirelmannDensity_pos
    (hFinite : PathCFiniteSieveInput)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.schnirelmannDensityPos hσ)

/-- Asymptotic-density theorem from fully unified Path C input data. -/
theorem primesSumsetAsymptoticLowerBound_of_unified_input_data
    (data : PathCUnifiedInputData) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
    data.finiteSieve data.counting

/-- Final Path C theorem from the occupied-average team data bundle. -/
theorem pathC_kGoldbach_of_atSqrt_split_occupied_average_data
    (data : PathCAtSqrtSplitOccupiedAverageData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_atSqrt_split_occupied_average_data data)

/-- Final Path C theorem from the log-upgrade team data bundle. -/
theorem pathC_kGoldbach_of_atSqrt_split_log_upgrade_data
    (data : PathCAtSqrtSplitLogUpgradeData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_atSqrt_split_log_upgrade_data data)

/-- Final Path C theorem from the uniform-lower-bound team data bundle. -/
theorem pathC_kGoldbach_of_atSqrt_split_uniformLowerBound_data
    (data : PathCAtSqrtSplitUniformLowerBoundData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_atSqrt_split_uniformLowerBound_data
      data)

/-- Final Path C theorem from the positive-Schnirelmann-density team data
bundle. -/
theorem pathC_kGoldbach_of_atSqrt_split_schnirelmannDensity_data
    (data : PathCAtSqrtSplitSchnirelmannDensityData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_atSqrt_split_schnirelmannDensity_data
      data)

/-- Final Path C theorem from the unified counting-input team data. -/
theorem pathC_kGoldbach_of_atSqrt_split_counting_data
    (data : PathCAtSqrtSplitCountingData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_atSqrt_split_counting_data data)

/-- Final Path C theorem from split at-sqrt finite-sieve worker fields plus
any supported counting worker output.  This is the lowest-friction integrator
entry point for independent worker results. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_countingInput
      hSift hErr hCounting)

/-- Asymptotic-density theorem from raw split at-sqrt finite-sieve worker
fields plus a uniform lower bound counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_uniformLowerBound
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hUniform : PrimesSumsetUniformLowerBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_countingInput
    hSift hErr (PathCCountingInput.uniformLowerBound hUniform)

/-- Asymptotic-density theorem from raw split at-sqrt finite-sieve worker
fields plus positive Schnirelmann density of `primesSumset`. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_schnirelmannDensity_pos
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_error_bound_and_countingInput
    hSift hErr (PathCCountingInput.schnirelmannDensityPos hσ)

/-- Final Path C theorem from raw split at-sqrt finite-sieve worker fields
plus a uniform lower bound counting worker output. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_uniformLowerBound
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
    hSift hErr (PathCCountingInput.uniformLowerBound hUniform)

/-- Final Path C theorem from raw split at-sqrt finite-sieve worker fields
plus positive Schnirelmann density of `primesSumset`. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_schnirelmannDensity_pos
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
    hSift hErr (PathCCountingInput.schnirelmannDensityPos hσ)

/-- Final Path C theorem from any supported finite-sieve worker output plus
any supported counting worker output. -/
theorem pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    (hFinite : PathCFiniteSieveInput)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_primesSumsetAsymptoticLowerBound
    (primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_countingInput
      hFinite hCounting)

/-- Final Path C theorem from any supported finite-sieve worker output plus
an occupied-average counting worker output. -/
theorem pathC_kGoldbach_of_finiteSieveInput_and_occupied_average
    (hFinite : PathCFiniteSieveInput)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.occupiedAverage hOcc)

/-- Final Path C theorem from any supported finite-sieve worker output plus
the no-log-loss occupied-average upgrade. -/
theorem pathC_kGoldbach_of_finiteSieveInput_and_occupied_log_upgrade
    (hFinite : PathCFiniteSieveInput)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.logUpgrade hUpgrade)

/-- Final Path C theorem from any supported finite-sieve worker output plus
a uniform lower bound counting worker output. -/
theorem pathC_kGoldbach_of_finiteSieveInput_and_uniformLowerBound
    (hFinite : PathCFiniteSieveInput)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.uniformLowerBound hUniform)

/-- Final Path C theorem from any supported finite-sieve worker output plus
positive Schnirelmann density of `primesSumset`. -/
theorem pathC_kGoldbach_of_finiteSieveInput_and_schnirelmannDensity_pos
    (hFinite : PathCFiniteSieveInput)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    hFinite (PathCCountingInput.schnirelmannDensityPos hσ)

/-- Final Path C theorem from fully unified Path C input data. -/
theorem pathC_kGoldbach_of_unified_input_data
    (data : PathCUnifiedInputData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    data.finiteSieve data.counting

/-- Asymptotic-density theorem from the split at-sqrt finite-sieve data
bundle plus an occupied-average counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_average
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hOcc : GoldbachSingularMultiplierOccupiedAverageBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_average
    (PathCFiniteSieveInput.atSqrtData data) hOcc

/-- Asymptotic-density theorem from the split at-sqrt finite-sieve data
bundle plus the no-log-loss occupied-average upgrade. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_log_upgrade
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hUpgrade : GoldbachSingularMultiplierOccupiedLogToAverageUpgrade) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_occupied_log_upgrade
    (PathCFiniteSieveInput.atSqrtData data) hUpgrade

/-- Asymptotic-density theorem from the split at-sqrt finite-sieve data
bundle plus a uniform lower bound counting worker output. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_bounded_error_data_and_uniformLowerBound
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hUniform : PrimesSumsetUniformLowerBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_uniformLowerBound
    (PathCFiniteSieveInput.atSqrtData data) hUniform

/-- Asymptotic-density theorem from the split at-sqrt finite-sieve data
bundle plus positive Schnirelmann density of `primesSumset`. -/
theorem primesSumsetAsymptoticLowerBound_of_residue_sifted_atSqrt_bounded_error_data_and_schnirelmannDensity_pos
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_finiteSieveInput_and_schnirelmannDensity_pos
    (PathCFiniteSieveInput.atSqrtData data) hσ

/-- A uniform linear lower bound on `primesSumset` is a sufficient counting
worker output for the split at-sqrt finite-sieve data bundle. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_uniformLowerBound
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hUniform : PrimesSumsetUniformLowerBound) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_log_upgrade
    data (goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_uniformLowerBound
      hUniform)

/-- Positive Schnirelmann density of `primesSumset` is another sufficient
counting worker output for the split at-sqrt finite-sieve data bundle. -/
theorem pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_schnirelmannDensity_pos
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hσ : 0 < Gdbh.schnirelmannDensity primesSumset) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_bounded_error_data_and_occupied_log_upgrade
    data (goldbachSingularMultiplierOccupiedLogToAverageUpgrade_of_schnirelmannDensity_pos
      hσ)

end PathCSingularCountingInterface
end Gdbh
