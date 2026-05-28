import Gdbh.VonMangoldtGoldbach
import TmpAnalyticCanonicalzj2kma3j.AnalyticMock

namespace Gdbh

noncomputable def examplePositiveLinearCanonicalMajorMinorHandoff :
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate where
  combinedThreshold := 100
  linearNetThreshold := 100
  coefficient := ((1 / 8) : ℝ)
  coefficient_pos := by norm_num
  mainTerm := exampleMajorMinorMainTerm
  majorArcError := exampleMajorArcError
  minorArcError := exampleMinorArcError
  combinedLowerBound := Gdbh.example_positive_linear_canonical_major_minor_combined_lower_bound
  linearNetLowerBound := Gdbh.example_positive_linear_canonical_major_minor_linear_net_lower_bound

theorem strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff_and_finite_certificate
    (finite : GoldbachUpTo 100)
    (hthreshold :
      examplePositiveLinearCanonicalMajorMinorHandoff.toDirectRawWeightSumLowerBound.threshold ≤
        100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate_le
    finite examplePositiveLinearCanonicalMajorMinorHandoff hthreshold

theorem strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff_and_finite_certificate_closed
    (finite : GoldbachUpTo 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate_le
    finite examplePositiveLinearCanonicalMajorMinorHandoff
    (examplePositiveLinearCanonicalMajorMinorHandoff.directRawWeightSumThreshold_le_of_components
      (by norm_num [examplePositiveLinearCanonicalMajorMinorHandoff])
      (by norm_num [examplePositiveLinearCanonicalMajorMinorHandoff])
      (Gdbh.example_positive_linear_canonical_major_minor_contamination_threshold_bound examplePositiveLinearCanonicalMajorMinorHandoff))

theorem strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff :
    StrongGoldbach :=
  strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff_and_finite_certificate_closed
    Gdbh.goldbachUpTo100

theorem explicitLowerBound_from_examplePositiveLinearCanonicalMajorMinorHandoff :
    ExplicitGoldbachLowerBound
      examplePositiveLinearCanonicalMajorMinorHandoff.toDirectRawWeightSumLowerBound.threshold :=
  explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate
    examplePositiveLinearCanonicalMajorMinorHandoff

theorem explicitLowerBound100_from_examplePositiveLinearCanonicalMajorMinorHandoff :
    ExplicitGoldbachLowerBound 100 :=
  strongGoldbach_iff_explicit_lower_bound100.mp
    strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff
end Gdbh
