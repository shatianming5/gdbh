import Gdbh.VonMangoldtGoldbach
import TmpAnalyticCanonicalzj2kma3j.AnalyticMock

namespace Gdbh

noncomputable def exampleQuarterCanonicalHandoff :
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold := 100
  relativeError := ((1 / 2) : ℝ)
  relativeError_lt_one := by norm_num
  rawNormalizedErrorBound := Gdbh.example_quarter_raw_normalized_error_bound

theorem strongGoldbach_from_exampleQuarterCanonicalHandoff_and_finite_certificate
    (finite : GoldbachUpTo 100)
    (hthreshold :
      exampleQuarterCanonicalHandoff.toDirectRawWeightSumLowerBound.threshold ≤
        100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite exampleQuarterCanonicalHandoff hthreshold

theorem strongGoldbach_from_exampleQuarterCanonicalHandoff_and_finite_certificate_closed
    (finite : GoldbachUpTo 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite exampleQuarterCanonicalHandoff
    (exampleQuarterCanonicalHandoff.directRawWeightSumThreshold_le
      (by norm_num [exampleQuarterCanonicalHandoff])
      (Gdbh.example_quarter_canonical_contamination_threshold_bound exampleQuarterCanonicalHandoff))

theorem strongGoldbach_from_exampleQuarterCanonicalHandoff :
    StrongGoldbach :=
  strongGoldbach_from_exampleQuarterCanonicalHandoff_and_finite_certificate_closed
    Gdbh.goldbachUpTo100

theorem explicitLowerBound_from_exampleQuarterCanonicalHandoff :
    ExplicitGoldbachLowerBound
      exampleQuarterCanonicalHandoff.toDirectRawWeightSumLowerBound.threshold :=
  explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    exampleQuarterCanonicalHandoff

theorem explicitLowerBound100_from_exampleQuarterCanonicalHandoff :
    ExplicitGoldbachLowerBound 100 :=
  strongGoldbach_iff_explicit_lower_bound100.mp
    strongGoldbach_from_exampleQuarterCanonicalHandoff
end Gdbh
