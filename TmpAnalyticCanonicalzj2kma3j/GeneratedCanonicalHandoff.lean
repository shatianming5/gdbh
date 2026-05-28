import Gdbh.VonMangoldtGoldbach
import TmpAnalyticCanonicalzj2kma3j.AnalyticMock

namespace Gdbh

noncomputable def exampleCanonicalHandoff :
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold := 100
  coefficient := ((1 / 4) : ℝ)
  relativeError := ((1 / 2) : ℝ)
  coefficient_pos := by norm_num
  relativeError_lt_one := by norm_num
  singularSeries := exampleSingularSeries
  singularSeriesLowerBound := Gdbh.example_singular_series_lower_bound
  rawNormalizedErrorBound := Gdbh.example_raw_normalized_error_bound

theorem strongGoldbach_from_exampleCanonicalHandoff_and_finite_certificate
    (finite : GoldbachUpTo 100)
    (hthreshold :
      exampleCanonicalHandoff.toDirectRawWeightSumLowerBound.threshold ≤
        100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite exampleCanonicalHandoff hthreshold

theorem strongGoldbach_from_exampleCanonicalHandoff_and_finite_certificate_closed
    (finite : GoldbachUpTo 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite exampleCanonicalHandoff
    (Gdbh.example_canonical_threshold_bound exampleCanonicalHandoff)

theorem strongGoldbach_from_exampleCanonicalHandoff :
    StrongGoldbach :=
  strongGoldbach_from_exampleCanonicalHandoff_and_finite_certificate_closed
    Gdbh.goldbachUpTo100

theorem explicitLowerBound_from_exampleCanonicalHandoff :
    ExplicitGoldbachLowerBound
      exampleCanonicalHandoff.toDirectRawWeightSumLowerBound.threshold :=
  explicit_lower_bound_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    exampleCanonicalHandoff

theorem explicitLowerBound100_from_exampleCanonicalHandoff :
    ExplicitGoldbachLowerBound 100 :=
  strongGoldbach_iff_explicit_lower_bound100.mp
    strongGoldbach_from_exampleCanonicalHandoff
end Gdbh
