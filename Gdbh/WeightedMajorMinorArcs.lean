import Gdbh.WeightedGoldbach

namespace Gdbh

structure WeightedMajorMinorArcEstimate where
  weight : PrimeSupportedWeight
  threshold : Nat
  mainTerm : Nat → Nat
  majorArcError : Nat → Nat
  minorArcError : Nat → Nat
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        WeightedGoldbachSum weight n + minorArcError n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n < mainTerm n

def WeightedMajorMinorArcEstimate.toWeightedGoldbachLowerBound
    (estimate : WeightedMajorMinorArcEstimate) :
    WeightedGoldbachLowerBound where
  weight := estimate.weight
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  errorTerm := fun n => estimate.majorArcError n + estimate.minorArcError n
  lowerBound := by
    intro n htn hEven
    have hcombined := estimate.combinedLowerBound n htn hEven
    omega
  errorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem weighted_positive_above_of_weighted_major_minor_arc_estimate
    (estimate : WeightedMajorMinorArcEstimate) :
    WeightedGoldbachPositiveAbove estimate.weight estimate.threshold := by
  simpa [WeightedMajorMinorArcEstimate.toWeightedGoldbachLowerBound] using
    weighted_positive_above_of_weighted_lower_bound
      estimate.toWeightedGoldbachLowerBound

theorem count_positive_above_of_weighted_major_minor_arc_estimate
    (estimate : WeightedMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_weighted_positive_above
    (weighted_positive_above_of_weighted_major_minor_arc_estimate estimate)

theorem explicit_lower_bound_of_weighted_major_minor_arc_estimate
    (estimate : WeightedMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_weighted_major_minor_arc_estimate estimate

theorem strongGoldbach_of_weighted_major_minor_arc_estimate_le100
    (estimate : WeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach := by
  exact strongGoldbach_of_weighted_lower_bound_le100
    estimate.toWeightedGoldbachLowerBound
    (by
      simpa [WeightedMajorMinorArcEstimate.toWeightedGoldbachLowerBound] using
        hthreshold)

end Gdbh
