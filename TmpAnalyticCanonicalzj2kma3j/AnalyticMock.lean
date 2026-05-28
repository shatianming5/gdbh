import Gdbh.VonMangoldtGoldbach

namespace Gdbh

noncomputable def exampleSingularSeries (_ : Nat) : ℝ := 1
noncomputable def exampleMajorMinorMainTerm (_ : Nat) : ℝ := 1
noncomputable def exampleMajorArcError (_ : Nat) : ℝ := 0
noncomputable def exampleMinorArcError (_ : Nat) : ℝ := 0

axiom example_singular_series_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      ((1 / 4) : ℝ) ≤ exampleSingularSeries n

axiom example_raw_normalized_error_bound :
    ∀ n : Nat, 100 < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          exampleSingularSeries n * (n : ℝ)) /
        (exampleSingularSeries n * (n : ℝ))| ≤
        ((1 / 2) : ℝ)

axiom example_quarter_raw_normalized_error_bound :
    ∀ n : Nat, 100 < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /
        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤
        ((1 / 2) : ℝ)

axiom example_quarter_explicit_contamination_canonical_raw_normalized_error_bound :
    ∀ n : Nat, 100 < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /
        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤
        ((1 / 2) : ℝ)

axiom example_quarter_explicit_contamination_canonical_contamination_dominated :
    ∀ n : Nat, 100 < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *
          (n : ℝ)

axiom example_quarter_lower_bound_explicit_contamination_canonical_raw_relative_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      (1 - ((1 / 2) : ℝ)) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
        RawVonMangoldtGoldbachSum n

axiom example_quarter_lower_bound_explicit_contamination_canonical_contamination_dominated :
    ∀ n : Nat, 100 < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *
          (n : ℝ)

axiom example_quarter_lower_bound_explicit_contamination_canonical_sqrt_log_model_bound :
    ∀ n : Nat, 100 < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) *
            Real.log (n : ℝ) ^ (3 : Nat)) <
        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *
          (n : ℝ)

axiom example_canonical_threshold_bound :
    ∀ estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate,
      estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100

axiom example_quarter_canonical_contamination_threshold_bound :
    ∀ estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate,
      estimate.canonicalContaminationThreshold ≤ 100

axiom example_positive_linear_raw_raw_linear_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      ((1 / 8) : ℝ) * (n : ℝ) ≤
        RawVonMangoldtGoldbachSum n

axiom example_positive_linear_raw_canonical_contamination_threshold_bound :
    ∀ estimate :
      VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound,
      estimate.canonicalContaminationThreshold ≤ 100

axiom example_positive_linear_raw_explicit_contamination_canonical_raw_linear_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      ((1 / 8) : ℝ) * (n : ℝ) ≤
        RawVonMangoldtGoldbachSum n

axiom example_positive_linear_raw_explicit_contamination_canonical_contamination_dominated :
    ∀ n : Nat, 100 < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 / 8) : ℝ) * (n : ℝ)

axiom example_positive_linear_canonical_major_minor_combined_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      exampleMajorMinorMainTerm n -
          exampleMajorArcError n ≤
        RawVonMangoldtGoldbachSum n +
          exampleMinorArcError n

axiom example_positive_linear_canonical_major_minor_linear_net_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      ((1 / 8) : ℝ) * (n : ℝ) +
          exampleMinorArcError n ≤
        exampleMajorMinorMainTerm n -
          exampleMajorArcError n

axiom example_positive_linear_canonical_major_minor_contamination_threshold_bound :
    ∀ estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate,
      estimate.canonicalContaminationThreshold ≤ 100

axiom example_positive_linear_explicit_contamination_canonical_major_minor_combined_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      exampleMajorMinorMainTerm n -
          exampleMajorArcError n ≤
        RawVonMangoldtGoldbachSum n +
          exampleMinorArcError n

axiom example_positive_linear_explicit_contamination_canonical_major_minor_linear_net_lower_bound :
    ∀ n : Nat, 100 < n → Even n →
      ((1 / 8) : ℝ) * (n : ℝ) +
          exampleMinorArcError n ≤
        exampleMajorMinorMainTerm n -
          exampleMajorArcError n

axiom example_positive_linear_explicit_contamination_canonical_major_minor_contamination_dominated :
    ∀ n : Nat, 100 < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 / 8) : ℝ) * (n : ℝ)

end Gdbh
