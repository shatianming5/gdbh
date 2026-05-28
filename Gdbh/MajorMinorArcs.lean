import Gdbh.AnalyticBridge

namespace Gdbh

structure MajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → Nat
  majorArcError : Nat → Nat
  minorArcError : Nat → Nat
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤ GoldbachCount n + minorArcError n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n < mainTerm n

def MajorMinorArcEstimate.toCircleMethodLowerBound
    (estimate : MajorMinorArcEstimate) :
    CircleMethodLowerBound where
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

theorem count_positive_of_major_minor_arc_estimate
    (estimate : MajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold := by
  simpa [MajorMinorArcEstimate.toCircleMethodLowerBound] using
    count_positive_of_circle_method_lower_bound
      estimate.toCircleMethodLowerBound

theorem explicit_lower_bound_of_major_minor_arc_estimate
    (estimate : MajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_of_major_minor_arc_estimate estimate

theorem strongGoldbach_of_major_minor_arc_estimate_le100
    (estimate : MajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach := by
  exact strongGoldbach_of_circle_method_lower_bound_le100
    estimate.toCircleMethodLowerBound
    (by
      simpa [MajorMinorArcEstimate.toCircleMethodLowerBound] using hthreshold)

end Gdbh
