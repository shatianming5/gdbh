import Gdbh.Round1Status
import Gdbh.DiscreteCircleMethod

namespace Gdbh
namespace GoalHandoff

/-!
# Exact goal handoff bridges

This module exposes the current finite-certificate handoff directly at the
statement from `goal.md`.  It does not prove a new analytic estimate; it
removes one layer of accounting between the analytic interfaces and the exact
binary Goldbach formulation.
-/

theorem binaryGoldbachConjecture_of_strongGoldbach
    (h : StrongGoldbach) :
    Round1Status.BinaryGoldbachConjecture :=
  Round1Status.binaryGoldbachConjecture_iff_strongGoldbach.mpr h

theorem binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    {B T : Nat}
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_of_finite_and_explicit_lower_bound_le
      finite hthreshold lower_bound)

theorem binaryGoldbachConjecture_from_currentFormalTarget50000
    (h : Round1Status.CurrentFormalTarget50000) :
    Round1Status.BinaryGoldbachConjecture :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mpr h

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_explicit_lower_bound
    {T : Nat}
    (hthreshold : T ≤ 50000)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_explicit_lower_bound
      hthreshold lower_bound)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_count_positive_above
    {T : Nat}
    (hthreshold : T ≤ 50000)
    (count_positive : GoldbachCountPositiveAbove T) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_count_positive_above
      hthreshold count_positive)

/-! ## Current-tail target handoff

The project status currently records `ExplicitGoldbachLowerBound 50000`, via
`Round1Status.CurrentFormalTarget50000`, as the remaining target.  The bridges
below let later analytic estimates close that target directly, instead of
first producing `StrongGoldbach` or the exact binary statement and then using
an equivalence in reverse.
-/

theorem currentFormalTarget50000_of_strongGoldbach
    (h : StrongGoldbach) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.strongGoldbach_iff_currentFormalTarget50000.mp h

theorem currentFormalTarget50000_from_explicit_lower_bound_le
    {T : Nat}
    (hthreshold : T ≤ 50000)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    Round1Status.CurrentFormalTarget50000 :=
  explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    (A := 50000) (B := 50000) (T := T)
    (by decide) goldbachUpTo50000_of_chunkedCertificate2To50000
    hthreshold lower_bound

theorem currentFormalTarget50000_from_count_positive_above_le
    {T : Nat}
    (hthreshold : T ≤ 50000)
    (count_positive : GoldbachCountPositiveAbove T) :
    Round1Status.CurrentFormalTarget50000 :=
  explicit_lower_bound_of_count_positive_above
    (count_positive_above_of_finite_and_count_positive_above_le
      (A := 50000) (B := 50000) (T := T)
      (by decide) goldbachUpTo50000_of_chunkedCertificate2To50000
      hthreshold count_positive)

theorem currentFormalTarget50000_from_circle_method_lower_bound
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ 50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_count_positive_above_le
    hthreshold (count_positive_of_circle_method_lower_bound bound)

theorem currentFormalTarget50000_from_major_minor_arc_estimate
    (estimate : MajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_count_positive_above_le
    hthreshold (count_positive_of_major_minor_arc_estimate estimate)

theorem currentFormalTarget50000_from_vonMangoldt_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtDirectRawWeightSumLowerBound)
    (hthreshold : bound.threshold ≤ 50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_count_positive_above_le
    hthreshold
    (count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound bound)

theorem currentFormalTarget50000_from_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_explicit_lower_bound_le hthreshold
    (explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
      estimate)

theorem currentFormalTarget50000_from_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_explicit_lower_bound_le hthreshold
    (explicit_lower_bound_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
      estimate)

theorem currentFormalTarget50000_from_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_explicit_lower_bound_le hthreshold
    (DiscreteCircleMethod.explicit_lower_bound_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
      estimate)

theorem currentFormalTarget50000_from_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_from_explicit_lower_bound_le hthreshold
    (DiscreteCircleMethod.explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
      estimate)

theorem currentFormalTarget50000_from_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
      estimate hthreshold)

theorem currentFormalTarget50000_from_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_circle_method_lower_bound
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ 50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_circle_method_lower_bound
      bound hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_major_minor_arc_estimate
    (estimate : MajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_major_minor_arc_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtDirectRawWeightSumLowerBound)
    (hthreshold : bound.threshold ≤ 50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_direct_raw_weight_sum_lower_bound
      bound hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
    (estimate : VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (explicit_lower_bound_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (DiscreteCircleMethod.explicit_lower_bound_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (DiscreteCircleMethod.explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_finite_and_explicit_lower_bound_le
    goldbachUpTo50000_of_chunkedCertificate2To50000 hthreshold
    (DiscreteCircleMethod.explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
      estimate)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤
      50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_from_chunkedCertificate2To50000_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
      estimate hthreshold)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_pathA_inner_bilinear
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ 50000 ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤
            50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
      content
      goldbachUpTo50000_of_chunkedCertificate2To50000
      threshold_covered)

theorem binaryGoldbachConjecture_from_chunkedCertificate2To50000_and_pathA_inner_pointwise
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ 50000 ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤
            50000) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_strongGoldbach
    (strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
      content
      goldbachUpTo50000_of_chunkedCertificate2To50000
      threshold_covered)

end GoalHandoff
end Gdbh
