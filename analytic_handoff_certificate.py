#!/usr/bin/env python3
"""Validate analytic handoff metadata for HL weight-sum bridges.

This validator does not prove any analytic estimate.  It records the exact
machine-readable obligations needed to build a
Gdbh.VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate or
Gdbh.VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate or
Gdbh.VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate or
Gdbh.VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate or
Gdbh.VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate or
Gdbh.VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound or
Gdbh.VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound or
Gdbh.VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate or
Gdbh.VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate or
Gdbh.VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate or
Gdbh.VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate or
Gdbh.DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate or
Gdbh.DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate or
Gdbh.DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate or
Gdbh.DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound or
Gdbh.DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound or
Gdbh.DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate or
Gdbh.DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate
and reports whether the metadata is structurally valid and whether it claims
all obligations have formal Lean evidence.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any


CERTIFICATE_KIND = (
    "vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate"
)
WEIGHT_SUM_CERTIFICATE_KIND = CERTIFICATE_KIND
CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate"
)
QUARTER_CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_quarter_hardy_littlewood_normalized_"
    "canonical_weight_sum_estimate"
)
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_quarter_hardy_littlewood_normalized_explicit_"
    "contamination_canonical_weight_sum_estimate"
)
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_"
    "contamination_canonical_weight_sum_estimate"
)
POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound"
)
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND = (
    "vonMangoldt_positive_linear_raw_explicit_contamination_"
    "canonical_weight_sum_lower_bound"
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND = (
    "vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_"
    "major_minor_arc_estimate"
)
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND = (
    "vonMangoldt_split_threshold_positive_linear_explicit_contamination_"
    "canonical_weight_sum_major_minor_arc_estimate"
)
DECOMPOSITION_CERTIFICATE_KIND = (
    "vonMangoldt_quarter_split_threshold_hardy_littlewood_"
    "major_minor_decomposition_canonical_weight_sum_estimate"
)
LINEAR_DECOMPOSITION_CERTIFICATE_KIND = (
    "vonMangoldt_quarter_linear_error_decomposition_"
    "canonical_weight_sum_estimate"
)
DFT_MODEL_L2_CERTIFICATE_KIND = (
    "vonMangoldt_dft_model_l2_minor_quarter_linear_error_"
    "canonical_weight_sum_estimate"
)
DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND = (
    "vonMangoldt_dft_model_uniform_minor_quarter_linear_error_"
    "canonical_weight_sum_estimate"
)
DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND = (
    "vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_"
    "canonical_weight_sum_estimate"
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND = (
    "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_"
    "canonical_lower_bound"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND = (
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
    "explicit_contamination_canonical_lower_bound"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND = (
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_explicit_contamination_canonical_weight_sum_estimate"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND = (
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate"
)
CERTIFICATE_VERSION = 1
LEAN_OBJECT = "Gdbh.VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate"
CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate"
)
QUARTER_CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate"
)
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate"
)
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate"
)
POSITIVE_LINEAR_RAW_CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound"
)
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT = (
    "Gdbh.VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound"
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_OBJECT = (
    "Gdbh.VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate"
)
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_OBJECT = (
    "Gdbh.VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate"
)
DECOMPOSITION_LEAN_OBJECT = (
    "Gdbh.VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate"
)
LINEAR_DECOMPOSITION_LEAN_OBJECT = (
    "Gdbh.VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate"
)
DFT_MODEL_L2_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate"
)
DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate"
)
DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate"
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBound"
    "ExplicitContaminationCanonicalWeightSumEstimate"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_OBJECT = (
    "Gdbh.DiscreteCircleMethod."
    "VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBound"
    "SqrtLogContaminationCanonicalWeightSumEstimate"
)
LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_"
    "normalized_weight_sum_estimate_le"
)
LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_hardy_littlewood_"
    "normalized_weight_sum_estimate_le100"
)
CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_"
    "normalized_canonical_weight_sum_estimate_le"
)
CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_hardy_littlewood_"
    "normalized_canonical_weight_sum_estimate_le100"
)
QUARTER_CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
    "normalized_canonical_weight_sum_estimate_le"
)
QUARTER_CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_"
    "normalized_canonical_weight_sum_estimate_le100"
)
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
    "normalized_explicit_contamination_canonical_weight_sum_estimate_le"
)
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_"
    "normalized_explicit_contamination_canonical_weight_sum_estimate_le100"
)
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
    "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le"
)
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_"
    "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100"
)
POSITIVE_LINEAR_RAW_CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
    "canonical_weight_sum_lower_bound_le"
)
POSITIVE_LINEAR_RAW_CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_positive_linear_raw_canonical_"
    "weight_sum_lower_bound_le100"
)
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
    "explicit_contamination_canonical_weight_sum_lower_bound_le"
)
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_positive_linear_raw_explicit_"
    "contamination_canonical_weight_sum_lower_bound_le100"
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_split_threshold_"
    "positive_linear_canonical_weight_sum_major_minor_arc_estimate_le"
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_"
    "canonical_weight_sum_major_minor_arc_estimate_le100"
)
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_"
    "linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate_le"
)
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_"
    "explicit_contamination_canonical_weight_sum_major_minor_arc_estimate_le100"
)
DECOMPOSITION_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_"
    "hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le"
)
DECOMPOSITION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_quarter_split_threshold_"
    "hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le100"
)
LINEAR_DECOMPOSITION_LEAN_STRONG_THEOREM = (
    "Gdbh.strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_"
    "decomposition_canonical_weight_sum_estimate_le"
)
LINEAR_DECOMPOSITION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.strongGoldbach_of_vonMangoldt_quarter_linear_error_"
    "decomposition_canonical_weight_sum_estimate_le100"
)
DFT_MODEL_L2_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_finite_and_vonMangoldt_dft_model_l2_minor_quarter_"
    "linear_error_canonical_weight_sum_estimate_le"
)
DFT_MODEL_L2_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_"
    "canonical_weight_sum_estimate_le100"
)
DFT_MODEL_UNIFORM_MINOR_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_"
    "quarter_linear_error_canonical_weight_sum_estimate_le"
)
DFT_MODEL_UNIFORM_MINOR_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_vonMangoldt_dft_model_uniform_minor_quarter_linear_"
    "error_canonical_weight_sum_estimate_le100"
)
DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_sq_"
    "quarter_linear_error_canonical_weight_sum_estimate_le"
)
DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod."
    "strongGoldbach_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_"
    "error_canonical_weight_sum_estimate_le100"
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_finite_and_"
    "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_"
    "canonical_lower_bound_le"
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_"
    "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_"
    "canonical_lower_bound_le100"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_finite_and_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
    "explicit_contamination_canonical_lower_bound_le"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
    "explicit_contamination_canonical_lower_bound_le100"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_finite_and_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_STRONG_THEOREM = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_finite_and_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le"
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_STRONG_THEOREM_LE100 = (
    "Gdbh.DiscreteCircleMethod.strongGoldbach_of_"
    "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
    "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le100"
)

REQUIRED_OBLIGATIONS = {
    "singular_series_lower_bound": (
        "for all even n > threshold, coefficient <= singularSeries(n)"
    ),
    "raw_normalized_error_bound": (
        "for all even n > threshold, "
        "|((RawVonMangoldtGoldbachSum(n) - singularSeries(n) * n) / "
        "(singularSeries(n) * n))| <= relativeError"
    ),
    "non_prime_prime_power_weight_sum_bound": (
        "for all even n > threshold, "
        "NonPrimePrimePowerVonMangoldtWeightSum(n) <= weightSumBound(n)"
    ),
    "contamination_dominated": (
        "for all even n > threshold, "
        "2 * weightSumBound(n) * log n < "
        "(1 - relativeError) * coefficient * n"
    ),
}
CANONICAL_REQUIRED_OBLIGATIONS = {
    key: REQUIRED_OBLIGATIONS[key]
    for key in (
        "singular_series_lower_bound",
        "raw_normalized_error_bound",
    )
}
QUARTER_CANONICAL_REQUIRED_OBLIGATIONS = {
    "raw_normalized_error_bound": (
        "for all even n > threshold, "
        "|((RawVonMangoldtGoldbachSum(n) - "
        "goldbachSingularSeriesFromQuarter(n) * n) / "
        "(goldbachSingularSeriesFromQuarter(n) * n))| <= relativeError"
    )
}
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS = {
    "raw_normalized_error_bound": (
        "for all even n > threshold, "
        "|((RawVonMangoldtGoldbachSum(n) - "
        "goldbachSingularSeriesFromQuarter(n) * n) / "
        "(goldbachSingularSeriesFromQuarter(n) * n))| <= relativeError"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "(1 - relativeError) * (1/4) * n"
    ),
}
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS = {
    "raw_relative_lower_bound": (
        "for all even n > threshold, "
        "(1 - relativeError) * "
        "goldbachSingularSeriesFromQuarter(n) * n <= "
        "RawVonMangoldtGoldbachSum(n)"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "(1 - relativeError) * (1/4) * n"
    ),
}
POSITIVE_LINEAR_RAW_CANONICAL_REQUIRED_OBLIGATIONS = {
    "raw_linear_lower_bound": (
        "for all even n > threshold, "
        "coefficient * n <= RawVonMangoldtGoldbachSum(n)"
    )
}
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS = {
    "raw_linear_lower_bound": (
        "for all even n > rawThreshold, "
        "coefficient * n <= RawVonMangoldtGoldbachSum(n)"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "coefficient * n"
    ),
}
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS = {
    "combined_lower_bound": (
        "for all even n > combinedThreshold, "
        "mainTerm(n) - majorArcError(n) <= "
        "RawVonMangoldtGoldbachSum(n) + minorArcError(n)"
    ),
    "linear_net_lower_bound": (
        "for all even n > linearNetThreshold, "
        "coefficient * n + minorArcError(n) <= "
        "mainTerm(n) - majorArcError(n)"
    ),
}
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS = {
    **POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "coefficient * n"
    ),
}
DECOMPOSITION_REQUIRED_OBLIGATIONS = {
    "raw_decomposition": (
        "for all even n > decompositionThreshold, "
        "RawVonMangoldtGoldbachSum(n) = "
        "majorArcContribution(n) + minorArcContribution(n)"
    ),
    "major_arc_approximation_bound": (
        "for all even n > majorArcThreshold, "
        "|majorArcContribution(n) - "
        "goldbachSingularSeriesFromQuarter(n) * n| <= majorArcError(n)"
    ),
    "minor_arc_contribution_bound": (
        "for all even n > minorArcThreshold, "
        "|minorArcContribution(n)| <= minorArcError(n)"
    ),
    "total_analytic_error_bound": (
        "for all even n > totalAnalyticErrorThreshold, "
        "majorArcError(n) + minorArcError(n) <= relativeError * "
        "goldbachSingularSeriesFromQuarter(n) * n"
    ),
}
LINEAR_DECOMPOSITION_REQUIRED_OBLIGATIONS = {
    "raw_decomposition": DECOMPOSITION_REQUIRED_OBLIGATIONS[
        "raw_decomposition"
    ],
    "major_arc_approximation_bound": DECOMPOSITION_REQUIRED_OBLIGATIONS[
        "major_arc_approximation_bound"
    ],
    "minor_arc_contribution_bound": DECOMPOSITION_REQUIRED_OBLIGATIONS[
        "minor_arc_contribution_bound"
    ],
    "total_linear_error_bound": (
        "for all even n > totalLinearErrorThreshold, "
        "majorArcError(n) + minorArcError(n) <= "
        "analyticErrorCoefficient * n"
    ),
}
DFT_MODEL_L2_REQUIRED_OBLIGATIONS = {
    "major_arc_term_approximation_bound": (
        "for all even n > majorArcThreshold and k in majorArcs(n), "
        "|rawVonMangoldtDftSquareFourierTerm(n,k) - "
        "majorArcModelTerm(n,k)| <= majorArcTermError(n,k)"
    ),
    "major_arc_model_approximation_bound": (
        "for all even n > majorArcThreshold, "
        "|sum_{k in majorArcs(n)} majorArcModelTerm(n,k) - "
        "goldbachSingularSeriesFromQuarter(n) * n| <= "
        "majorArcModelError(n)"
    ),
    "major_arc_error_bound": (
        "for all even n > majorArcThreshold, "
        "sum_{k in majorArcs(n)} majorArcTermError(n,k) + "
        "majorArcModelError(n) <= majorArcError(n)"
    ),
    "minor_arc_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n,k)"
    ),
    "minor_arc_square_sum_bound": (
        "for all even n > minorArcThreshold, "
        "|(n+1)^-1| * sum_{k outside majorArcs(n)} "
        "minorArcDftBound(n,k)^2 <= minorArcError(n)"
    ),
    "total_linear_error_bound": (
        "for all even n > totalLinearErrorThreshold, "
        "majorArcError(n) + minorArcError(n) <= "
        "analyticErrorCoefficient * n"
    ),
}
DFT_MODEL_UNIFORM_MINOR_REQUIRED_OBLIGATIONS = {
    "major_arc_term_approximation_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_term_approximation_bound"
    ],
    "major_arc_model_approximation_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_model_approximation_bound"
    ],
    "major_arc_error_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_error_bound"
    ],
    "minor_arc_uniform_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "minor_arc_frequency_count_bound_valid": (
        "for all even n > minorArcThreshold, "
        "card({k outside majorArcs(n)}) <= "
        "minorArcFrequencyCountBound(n)"
    ),
    "minor_arc_square_sum_error_bound": (
        "for all even n > minorArcThreshold, "
        "minorArcFrequencyCountBound(n) * |(n+1)^-1| * "
        "minorArcDftBound(n)^2 <= minorArcError(n)"
    ),
    "total_linear_error_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "total_linear_error_bound"
    ],
}
DFT_MODEL_UNIFORM_MINOR_SQ_REQUIRED_OBLIGATIONS = {
    "major_arc_term_approximation_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_term_approximation_bound"
    ],
    "major_arc_model_approximation_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_model_approximation_bound"
    ],
    "major_arc_error_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "major_arc_error_bound"
    ],
    "minor_arc_uniform_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "minor_arc_dft_bound_sq_error_bound": (
        "for all even n > minorArcThreshold, "
        "minorArcDftBound(n)^2 <= minorArcError(n)"
    ),
    "total_linear_error_bound": DFT_MODEL_L2_REQUIRED_OBLIGATIONS[
        "total_linear_error_bound"
    ],
}
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS = {
    "major_arc_linear_lower_bound": (
        "for all even n > majorArcThreshold, "
        "coefficient * n + minorArcError(n) <= "
        "rawVonMangoldtFourierMajorArcContribution(majorArcs, n)"
    ),
    "minor_arc_uniform_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "minor_arc_dft_bound_sq_error_bound": (
        "for all even n > minorArcThreshold, "
        "minorArcDftBound(n)^2 <= minorArcError(n)"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "coefficient * n"
    ),
}
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS = {
    "major_arc_linear_lower_bound": (
        "for all even n > majorArcThreshold, "
        "coefficient * n + minorArcDftBound(n)^2 <= "
        "rawVonMangoldtFourierMajorArcContribution(majorArcs, n)"
    ),
    "minor_arc_uniform_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "coefficient * n"
    ),
}
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS = {
    "major_arc_lower_bound": (
        "for all even n > majorArcThreshold, "
        "(1 - relativeError) * goldbachSingularSeriesFromQuarter(n) * n + "
        "minorArcDftBound(n)^2 <= "
        "rawVonMangoldtFourierMajorArcContribution(majorArcs, n)"
    ),
    "minor_arc_uniform_dft_bound_valid": (
        "for all even n > minorArcThreshold and k outside majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "contamination_dominated": (
        "for all even n > contaminationThreshold, "
        "2 * vonMangoldtWeightSumContaminationBudget("
        "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound, n) < "
        "(1 - relativeError) * (1/4) * n"
    ),
}
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_REQUIRED_OBLIGATIONS = {
    "major_arc_lower_bound": (
        DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS[
            "major_arc_lower_bound"
        ]
    ),
    "minor_arc_uniform_dft_bound_valid": (
        DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS[
            "minor_arc_uniform_dft_bound_valid"
        ]
    ),
    "contamination_sqrt_log_model_bound": (
        "for all even n > contaminationThreshold, "
        "vonMangoldtSqrtLogBudgetComparisonConstant * "
        "sqrt(n) * log(n)^3 < (1 - relativeError) * (1/4) * n"
    ),
}
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS = {
    "minor_arc_uniform_dft_bound_off_major_arcs": (
        "for all even n > minorArcThreshold and k not in majorArcs(n), "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
    "zero_frequency_mem_major_arcs": (
        "for all even n > minorArcThreshold, 0 belongs to majorArcs(n)"
    ),
    "minor_arc_uniform_dft_bound_nonzero": (
        "for all even n > minorArcThreshold and nonzero k, "
        "|vonMangoldtZModDft(n,k)| <= minorArcDftBound(n)"
    ),
}
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS = {
    "contamination_sqrt_log_model_bound": (
        "for all even n > contaminationThreshold, "
        "vonMangoldtSqrtLogBudgetComparisonConstant * "
        "sqrt(n) * log(n)^3 < coefficient * n"
    )
}
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS = (
    DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS = {
    "contamination_sqrt_log_model_bound": (
        "for all even n > contaminationThreshold, "
        "vonMangoldtSqrtLogBudgetComparisonConstant * "
        "sqrt(n) * log(n)^3 < (1 - relativeError) * (1/4) * n"
    )
}
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS = {
    "contamination_sqrt_log_model_bound": (
        "for all even n > contaminationThreshold, "
        "vonMangoldtSqrtLogBudgetComparisonConstant * "
        "sqrt(n) * log(n)^3 < (1 - relativeError) * (1/4) * n"
    )
}
QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS = (
    QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS
)
CANONICAL_DERIVED_THRESHOLD_BOUND_KEY = "derived_threshold_bound"
CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT = (
    "estimate.toDirectRawWeightSumLowerBound.threshold <= "
    "finite_certificate_bound"
)
DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_KEY = (
    "canonical_contamination_threshold_bound"
)
DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT = (
    "estimate.canonicalContaminationThreshold <= finite_certificate_bound"
)
SINGULAR_SERIES_OBLIGATIONS = {
    "singular_series_lower_bound",
    "raw_normalized_error_bound",
}
WEIGHT_SUM_BOUND_OBLIGATIONS = {
    "non_prime_prime_power_weight_sum_bound",
    "contamination_dominated",
}
DECOMPOSITION_THRESHOLD_FIELDS = (
    "decompositionThreshold",
    "majorArcThreshold",
    "minorArcThreshold",
    "totalAnalyticErrorThreshold",
)
LINEAR_DECOMPOSITION_THRESHOLD_FIELDS = (
    "decompositionThreshold",
    "majorArcThreshold",
    "minorArcThreshold",
    "totalLinearErrorThreshold",
)
DFT_MODEL_L2_THRESHOLD_FIELDS = (
    "majorArcThreshold",
    "minorArcThreshold",
    "totalLinearErrorThreshold",
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_THRESHOLD_FIELDS = (
    "majorArcThreshold",
    "minorArcThreshold",
    "contaminationThreshold",
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_THRESHOLD_FIELDS = (
    "combinedThreshold",
    "linearNetThreshold",
)
QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_THRESHOLD_FIELDS = (
    "threshold",
    "contaminationThreshold",
)
POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_THRESHOLD_FIELDS = (
    "rawThreshold",
    "contaminationThreshold",
)
POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_THRESHOLD_FIELDS = (
    "combinedThreshold",
    "linearNetThreshold",
    "contaminationThreshold",
)
DECOMPOSITION_FUNCTION_FIELDS = (
    "majorArcContribution",
    "minorArcContribution",
    "majorArcError",
    "minorArcError",
)
POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_FUNCTION_FIELDS = (
    "mainTerm",
    "majorArcError",
    "minorArcError",
)
DFT_MODEL_L2_FUNCTION_FIELDS = (
    "majorArcs",
    "majorArcModelTerm",
    "majorArcTermError",
    "majorArcModelError",
    "majorArcError",
    "minorArcDftBound",
    "minorArcError",
)
DFT_MODEL_UNIFORM_MINOR_FUNCTION_FIELDS = (
    "majorArcs",
    "majorArcModelTerm",
    "majorArcTermError",
    "majorArcModelError",
    "majorArcError",
    "minorArcDftBound",
    "minorArcFrequencyCountBound",
    "minorArcError",
)
DFT_MODEL_UNIFORM_MINOR_SQ_FUNCTION_FIELDS = (
    "majorArcs",
    "majorArcModelTerm",
    "majorArcTermError",
    "majorArcModelError",
    "majorArcError",
    "minorArcDftBound",
    "minorArcError",
)
DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_FUNCTION_FIELDS = (
    "majorArcs",
    "minorArcDftBound",
    "minorArcError",
)
DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_FUNCTION_FIELDS = (
    "majorArcs",
    "minorArcDftBound",
)

FORMALIZED_STATUS = "formalized"
ALLOWED_CERTIFICATE_STATUSES = {"template", "candidate", "formalized"}
ALLOWED_OBLIGATION_STATUSES = {"missing", "paper", "checked", "formalized"}
LEAN_IDENTIFIER_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
LEAN_MODULE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$"
)


def _expect_mapping(value: Any, field: str, errors: list[str]) -> dict[str, Any]:
    if not isinstance(value, dict):
        errors.append(f"{field} must be an object")
        return {}
    return value


def _expect_string(value: Any, field: str, errors: list[str]) -> str:
    if not isinstance(value, str) or not value:
        errors.append(f"{field} must be a non-empty string")
        return ""
    return value


def _expect_nonnegative_int(value: Any, field: str, errors: list[str]) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{field} must be an integer")
        return None
    if value < 0:
        errors.append(f"{field} must be non-negative")
        return None
    return value


def _parse_fraction(value: Any, field: str, errors: list[str]) -> Fraction | None:
    if not isinstance(value, str):
        errors.append(f"{field} must be a rational string, e.g. '1/2'")
        return None
    try:
        return Fraction(value)
    except ValueError:
        errors.append(f"{field} must be a valid rational string")
        return None


def _validate_lean_identifier(value: str, field: str, errors: list[str]) -> None:
    if not LEAN_IDENTIFIER_RE.fullmatch(value):
        errors.append(f"{field} must be a Lean identifier")


def _validate_lean_module(value: str, field: str, errors: list[str]) -> None:
    if not LEAN_MODULE_RE.fullmatch(value):
        errors.append(f"{field} must be a Lean module name")


def _validate_imports(certificate: dict[str, Any], errors: list[str]) -> list[str]:
    raw_imports = certificate.get("imports", ["Gdbh.VonMangoldtGoldbach"])
    if not isinstance(raw_imports, list) or not raw_imports:
        errors.append("imports must be a non-empty list of Lean module names")
        return ["Gdbh.VonMangoldtGoldbach"]

    imports: list[str] = []
    for index, raw_import in enumerate(raw_imports):
        if not isinstance(raw_import, str) or not raw_import:
            errors.append(f"imports[{index}] must be a non-empty string")
            continue
        _validate_lean_module(raw_import, f"imports[{index}]", errors)
        imports.append(raw_import)

    if "Gdbh.VonMangoldtGoldbach" not in imports:
        errors.append("imports must include Gdbh.VonMangoldtGoldbach")
    return imports or ["Gdbh.VonMangoldtGoldbach"]


def _validate_obligations(
    obligations: dict[str, Any],
    required_obligations: dict[str, str],
    errors: list[str],
    incomplete_reasons: list[str],
) -> list[str]:
    formalized_obligations: list[str] = []
    for key, expected_statement in required_obligations.items():
        raw_obligation = obligations.get(key)
        if raw_obligation is None:
            errors.append(f"obligations.{key} is required")
            incomplete_reasons.append(f"missing obligation: {key}")
            continue
        obligation = _expect_mapping(raw_obligation, f"obligations.{key}", errors)
        status = obligation.get("status")
        if status not in ALLOWED_OBLIGATION_STATUSES:
            errors.append(
                f"obligations.{key}.status must be one of "
                f"{sorted(ALLOWED_OBLIGATION_STATUSES)}"
            )
        if obligation.get("statement") != expected_statement:
            errors.append(
                f"obligations.{key}.statement must equal the canonical statement"
            )
        if status != FORMALIZED_STATUS:
            incomplete_reasons.append(f"obligation not formalized: {key}")
        else:
            formalized_obligations.append(key)
        lean_declaration = obligation.get("lean_declaration")
        if status == FORMALIZED_STATUS:
            lean_name = _expect_string(
                lean_declaration,
                f"obligations.{key}.lean_declaration",
                errors,
            )
            if lean_name:
                _validate_lean_identifier(
                    lean_name,
                    f"obligations.{key}.lean_declaration",
                    errors,
                )
    return formalized_obligations


def _validate_optional_obligation(
    obligations: dict[str, Any],
    key: str,
    expected_statement: str,
    errors: list[str],
) -> bool:
    raw_obligation = obligations.get(key)
    if raw_obligation is None:
        return False
    obligation = _expect_mapping(raw_obligation, f"obligations.{key}", errors)
    status = obligation.get("status")
    if status not in ALLOWED_OBLIGATION_STATUSES:
        errors.append(
            f"obligations.{key}.status must be one of "
            f"{sorted(ALLOWED_OBLIGATION_STATUSES)}"
        )
    if obligation.get("statement") != expected_statement:
        errors.append(
            f"obligations.{key}.statement must equal the canonical statement"
        )
    if status != FORMALIZED_STATUS:
        return False
    lean_name = _expect_string(
        obligation.get("lean_declaration"),
        f"obligations.{key}.lean_declaration",
        errors,
    )
    if lean_name:
        _validate_lean_identifier(
            lean_name,
            f"obligations.{key}.lean_declaration",
            errors,
        )
    return bool(lean_name)


def _validate_final_handoff_term(
    certificate: dict[str, Any],
    *,
    json_field: str,
    statement: str,
    errors: list[str],
) -> tuple[bool, bool]:
    raw_threshold_bound = certificate.get(json_field)
    if raw_threshold_bound is None:
        return False, False

    threshold_bound = _expect_mapping(raw_threshold_bound, json_field, errors)
    status = threshold_bound.get("status")
    if status not in ALLOWED_OBLIGATION_STATUSES:
        errors.append(
            f"{json_field}.status must be one of "
            f"{sorted(ALLOWED_OBLIGATION_STATUSES)}"
        )
    if threshold_bound.get("statement") != statement:
        errors.append(
            f"{json_field}.statement must equal the canonical statement"
        )

    if status != FORMALIZED_STATUS:
        return True, False

    lean_term = _expect_string(
        threshold_bound.get("lean_term"),
        f"{json_field}.lean_term",
        errors,
    )
    return True, bool(lean_term)


def _validate_canonical_final_handoff(
    certificate: dict[str, Any],
    errors: list[str],
    final_handoff_reasons: list[str],
) -> list[str]:
    present, complete = _validate_final_handoff_term(
        certificate,
        json_field="derivedThresholdBound",
        statement=CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT,
        errors=errors,
    )
    if not present:
        final_handoff_reasons.append(
            "missing final handoff obligation: derived_threshold_bound"
        )
        return []
    if not complete:
        final_handoff_reasons.append(
            "final handoff obligation not formalized: derived_threshold_bound"
        )
        return []
    return [CANONICAL_DERIVED_THRESHOLD_BOUND_KEY]


def _validate_decomposition_final_handoff(
    certificate: dict[str, Any],
    errors: list[str],
    final_handoff_reasons: list[str],
) -> list[str]:
    direct_present, direct_complete = _validate_final_handoff_term(
        certificate,
        json_field="derivedThresholdBound",
        statement=CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT,
        errors=errors,
    )
    contamination_present, contamination_complete = (
        _validate_final_handoff_term(
            certificate,
            json_field="canonicalContaminationThresholdBound",
            statement=(
                DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
            ),
            errors=errors,
        )
    )

    formalized_keys: list[str] = []
    if direct_complete:
        formalized_keys.append(CANONICAL_DERIVED_THRESHOLD_BOUND_KEY)
    if contamination_complete:
        formalized_keys.append(
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_KEY
        )
    if formalized_keys:
        return formalized_keys

    if not direct_present and not contamination_present:
        final_handoff_reasons.append(
            "missing final handoff obligation: "
            "derived_threshold_bound or canonical_contamination_threshold_bound"
        )
        return []
    if direct_present and not direct_complete:
        final_handoff_reasons.append(
            "final handoff obligation not formalized: derived_threshold_bound"
        )
    if contamination_present and not contamination_complete:
        final_handoff_reasons.append(
            "final handoff obligation not formalized: "
            "canonical_contamination_threshold_bound"
        )
    return []


def _is_decomposition_certificate_kind(kind: Any) -> bool:
    return kind in {
        DECOMPOSITION_CERTIFICATE_KIND,
        LINEAR_DECOMPOSITION_CERTIFICATE_KIND,
    }


def _is_quarter_canonical_certificate_kind(kind: Any) -> bool:
    return kind == QUARTER_CANONICAL_CERTIFICATE_KIND


def _is_quarter_explicit_contamination_canonical_certificate_kind(
    kind: Any,
) -> bool:
    return kind == QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND


def _is_quarter_lower_bound_explicit_contamination_canonical_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
    )


def _is_quarter_explicit_contamination_family_certificate_kind(
    kind: Any,
) -> bool:
    return (
        _is_quarter_explicit_contamination_canonical_certificate_kind(kind)
        or _is_quarter_lower_bound_explicit_contamination_canonical_certificate_kind(
            kind
        )
    )


def _is_positive_linear_raw_canonical_certificate_kind(kind: Any) -> bool:
    return kind == POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND


def _is_positive_linear_raw_explicit_contamination_canonical_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
    )


def _is_positive_linear_canonical_major_minor_certificate_kind(
    kind: Any,
) -> bool:
    return kind == POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND


def _is_positive_linear_explicit_contamination_canonical_major_minor_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND
    )


def _is_dft_model_l2_certificate_kind(kind: Any) -> bool:
    return kind == DFT_MODEL_L2_CERTIFICATE_KIND


def _is_dft_model_uniform_minor_certificate_kind(kind: Any) -> bool:
    return kind == DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND


def _is_dft_model_uniform_minor_sq_certificate_kind(kind: Any) -> bool:
    return kind == DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND


def _is_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    )


def _is_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    )


def _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    )


def _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate_kind(
    kind: Any,
) -> bool:
    return (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND
    )


def _is_dft_model_certificate_kind(kind: Any) -> bool:
    return kind in {
        DFT_MODEL_L2_CERTIFICATE_KIND,
        DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND,
        DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND,
    }


def _certificate_spec(
    kind: Any,
) -> tuple[str, str, str, dict[str, str], bool]:
    if kind == CANONICAL_CERTIFICATE_KIND:
        return (
            CANONICAL_LEAN_OBJECT,
            CANONICAL_LEAN_STRONG_THEOREM,
            CANONICAL_LEAN_STRONG_THEOREM_LE100,
            CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == QUARTER_CANONICAL_CERTIFICATE_KIND:
        return (
            QUARTER_CANONICAL_LEAN_OBJECT,
            QUARTER_CANONICAL_LEAN_STRONG_THEOREM,
            QUARTER_CANONICAL_LEAN_STRONG_THEOREM_LE100,
            QUARTER_CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND:
        return (
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM,
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100,
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND:
        return (
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM,
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100,
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND:
        return (
            POSITIVE_LINEAR_RAW_CANONICAL_LEAN_OBJECT,
            POSITIVE_LINEAR_RAW_CANONICAL_LEAN_STRONG_THEOREM,
            POSITIVE_LINEAR_RAW_CANONICAL_LEAN_STRONG_THEOREM_LE100,
            POSITIVE_LINEAR_RAW_CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND:
        return (
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM,
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_STRONG_THEOREM_LE100,
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND:
        return (
            POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
            POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM,
            POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM_LE100,
            POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
            False,
        )
    if (
        kind
        == POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND
    ):
        return (
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM,
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_STRONG_THEOREM_LE100,
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == DECOMPOSITION_CERTIFICATE_KIND:
        return (
            DECOMPOSITION_LEAN_OBJECT,
            DECOMPOSITION_LEAN_STRONG_THEOREM,
            DECOMPOSITION_LEAN_STRONG_THEOREM_LE100,
            DECOMPOSITION_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == LINEAR_DECOMPOSITION_CERTIFICATE_KIND:
        return (
            LINEAR_DECOMPOSITION_LEAN_OBJECT,
            LINEAR_DECOMPOSITION_LEAN_STRONG_THEOREM,
            LINEAR_DECOMPOSITION_LEAN_STRONG_THEOREM_LE100,
            LINEAR_DECOMPOSITION_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == DFT_MODEL_L2_CERTIFICATE_KIND:
        return (
            DFT_MODEL_L2_LEAN_OBJECT,
            DFT_MODEL_L2_LEAN_STRONG_THEOREM,
            DFT_MODEL_L2_LEAN_STRONG_THEOREM_LE100,
            DFT_MODEL_L2_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND:
        return (
            DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT,
            DFT_MODEL_UNIFORM_MINOR_LEAN_STRONG_THEOREM,
            DFT_MODEL_UNIFORM_MINOR_LEAN_STRONG_THEOREM_LE100,
            DFT_MODEL_UNIFORM_MINOR_REQUIRED_OBLIGATIONS,
            False,
        )
    if kind == DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND:
        return (
            DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT,
            DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_STRONG_THEOREM,
            DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_STRONG_THEOREM_LE100,
            DFT_MODEL_UNIFORM_MINOR_SQ_REQUIRED_OBLIGATIONS,
            False,
        )
    if (
        kind
        == DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        return (
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM,
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100,
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
            False,
        )
    if (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        return (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
            False,
        )
    if (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        return (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_STRONG_THEOREM_LE100,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
            False,
        )
    if (
        kind
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND
    ):
        return (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_OBJECT,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_STRONG_THEOREM,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_STRONG_THEOREM_LE100,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_REQUIRED_OBLIGATIONS,
            False,
        )
    return (
        LEAN_OBJECT,
        LEAN_STRONG_THEOREM,
        LEAN_STRONG_THEOREM_LE100,
        REQUIRED_OBLIGATIONS,
        True,
    )


def _allowed_certificate_kinds() -> set[str]:
    return {
        CERTIFICATE_KIND,
        CANONICAL_CERTIFICATE_KIND,
        QUARTER_CANONICAL_CERTIFICATE_KIND,
        QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND,
        POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
        POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
        DECOMPOSITION_CERTIFICATE_KIND,
        LINEAR_DECOMPOSITION_CERTIFICATE_KIND,
        DFT_MODEL_L2_CERTIFICATE_KIND,
        DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND,
        DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND,
        DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND,
    }


def validate_certificate(certificate: dict[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    incomplete_reasons: list[str] = []

    kind = certificate.get("kind")
    if kind not in _allowed_certificate_kinds():
        errors.append(
            f"kind must be one of {sorted(_allowed_certificate_kinds())!r}"
        )
    (
        lean_object,
        lean_strong_theorem,
        lean_strong_theorem_le100,
        required_obligations,
        requires_weight_sum_bound,
    ) = _certificate_spec(kind)
    if certificate.get("version") != CERTIFICATE_VERSION:
        errors.append(f"version must be {CERTIFICATE_VERSION}")
    if certificate.get("lean_object") != lean_object:
        errors.append(f"lean_object must be {lean_object!r}")
    imports = _validate_imports(certificate, errors)
    finite_certificate_theorem = certificate.get("finiteCertificateTheorem")
    if finite_certificate_theorem is not None:
        finite_certificate_name = _expect_string(
            finite_certificate_theorem,
            "finiteCertificateTheorem",
            errors,
        )
        if finite_certificate_name:
            _validate_lean_identifier(
                finite_certificate_name,
                "finiteCertificateTheorem",
                errors,
            )

    status = certificate.get("status")
    if status not in ALLOWED_CERTIFICATE_STATUSES:
        errors.append(
            f"status must be one of {sorted(ALLOWED_CERTIFICATE_STATUSES)}"
        )
    if status != FORMALIZED_STATUS:
        incomplete_reasons.append("certificate status is not formalized")

    finite_bound = _expect_nonnegative_int(
        certificate.get("finite_certificate_bound"),
        "finite_certificate_bound",
        errors,
    )

    if _is_quarter_explicit_contamination_family_certificate_kind(kind):
        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_THRESHOLD_FIELDS
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        relative_error = _parse_fraction(
            certificate.get("relativeError"), "relativeError", errors
        )
        if relative_error is not None:
            if relative_error < 0:
                errors.append("relativeError must be non-negative")
            if relative_error >= 1:
                errors.append("relativeError must be less than 1")

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )
        derived_obligations: list[str] = []
        model_key = "contamination_sqrt_log_model_bound"
        model_statement = (
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS[
                model_key
            ]
            if _is_quarter_lower_bound_explicit_contamination_canonical_certificate_kind(
                kind
            )
            else QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS[
                model_key
            ]
        )
        model_formalized = _validate_optional_obligation(
            obligations,
            model_key,
            model_statement,
            errors,
        )
        if (
            "contamination_dominated" not in formalized_obligations
            and model_formalized
        ):
            contamination_threshold = threshold_values.get(
                "contaminationThreshold"
            )
            if (
                contamination_threshold is not None
                and 2 <= contamination_threshold
            ):
                derived_obligations.append(model_key)
                formalized_obligations.append("contamination_dominated")
                reason = "obligation not formalized: contamination_dominated"
                if reason in incomplete_reasons:
                    incomplete_reasons.remove(reason)
            else:
                incomplete_reasons.append(
                    "contamination_sqrt_log_model_bound requires "
                    "contaminationThreshold >= 2"
                )

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_derived_obligations": derived_obligations,
            "formalized_final_handoff_obligations": [],
            "threshold_components": threshold_values,
            "relative_error": (
                str(relative_error) if relative_error is not None else None
            ),
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": [],
        }

    if (
        _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate_kind(
            kind
        )
        or _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate_kind(
            kind
        )
    ):
        if "Gdbh.DiscreteCircleMethod" not in imports:
            errors.append("imports must include Gdbh.DiscreteCircleMethod")

        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in (
                DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_THRESHOLD_FIELDS
            )
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        relative_error = _parse_fraction(
            certificate.get("relativeError"), "relativeError", errors
        )
        if relative_error is not None:
            if relative_error < 0:
                errors.append("relativeError must be non-negative")
            if relative_error >= 1:
                errors.append("relativeError must be less than 1")

        function_names: dict[str, str] = {}
        for field in DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_FUNCTION_FIELDS:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )
        derived_obligations: list[str] = []
        off_major_key = "minor_arc_uniform_dft_bound_off_major_arcs"
        off_major_formalized = _validate_optional_obligation(
            obligations,
            off_major_key,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                off_major_key
            ],
            errors,
        )
        if (
            "minor_arc_uniform_dft_bound_valid"
            not in formalized_obligations
            and off_major_formalized
        ):
            derived_obligations.append(off_major_key)
            formalized_obligations.append("minor_arc_uniform_dft_bound_valid")
            reason = (
                "obligation not formalized: "
                "minor_arc_uniform_dft_bound_valid"
            )
            if reason in incomplete_reasons:
                incomplete_reasons.remove(reason)
        zero_major_key = "zero_frequency_mem_major_arcs"
        nonzero_key = "minor_arc_uniform_dft_bound_nonzero"
        zero_major_formalized = _validate_optional_obligation(
            obligations,
            zero_major_key,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                zero_major_key
            ],
            errors,
        )
        nonzero_formalized = _validate_optional_obligation(
            obligations,
            nonzero_key,
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                nonzero_key
            ],
            errors,
        )
        if (
            "minor_arc_uniform_dft_bound_valid"
            not in formalized_obligations
            and zero_major_formalized
            and nonzero_formalized
        ):
            derived_obligations.extend([zero_major_key, nonzero_key])
            formalized_obligations.append("minor_arc_uniform_dft_bound_valid")
            reason = (
                "obligation not formalized: "
                "minor_arc_uniform_dft_bound_valid"
            )
            if reason in incomplete_reasons:
                incomplete_reasons.remove(reason)
        if _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate_kind(
            kind
        ):
            contamination_threshold = threshold_values.get(
                "contaminationThreshold"
            )
            if contamination_threshold is not None and contamination_threshold < 2:
                incomplete_reasons.append(
                    "contamination_sqrt_log_model_bound requires "
                    "contaminationThreshold >= 2"
                )
        else:
            model_key = "contamination_sqrt_log_model_bound"
            model_formalized = _validate_optional_obligation(
                obligations,
                model_key,
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS[
                    model_key
                ],
                errors,
            )
            if (
                "contamination_dominated" not in formalized_obligations
                and model_formalized
            ):
                contamination_threshold = threshold_values.get(
                    "contaminationThreshold"
                )
                if (
                    contamination_threshold is not None
                    and 2 <= contamination_threshold
                ):
                    derived_obligations.append(model_key)
                    formalized_obligations.append("contamination_dominated")
                    reason = "obligation not formalized: contamination_dominated"
                    if reason in incomplete_reasons:
                        incomplete_reasons.remove(reason)
                else:
                    incomplete_reasons.append(
                        "contamination_sqrt_log_model_bound requires "
                        "contaminationThreshold >= 2"
                    )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_derived_obligations": derived_obligations,
            "formalized_final_handoff_obligations": [],
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "relative_error": (
                str(relative_error) if relative_error is not None else None
            ),
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": [],
        }

    if (
        _is_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate_kind(
            kind
        )
        or _is_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate_kind(
            kind
        )
    ):
        if "Gdbh.DiscreteCircleMethod" not in imports:
            errors.append("imports must include Gdbh.DiscreteCircleMethod")

        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in (
                DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_THRESHOLD_FIELDS
            )
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        coefficient = _parse_fraction(
            certificate.get("coefficient"), "coefficient", errors
        )
        if coefficient is not None and coefficient <= 0:
            errors.append("coefficient must be positive")

        function_fields = (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_FUNCTION_FIELDS
            if _is_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate_kind(
                kind
            )
            else DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_FUNCTION_FIELDS
        )
        function_names: dict[str, str] = {}
        for field in function_fields:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )
        derived_obligations: list[str] = []
        model_key = "contamination_sqrt_log_model_bound"
        model_statement = (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS[
                model_key
            ]
        )
        model_formalized = _validate_optional_obligation(
            obligations,
            model_key,
            model_statement,
            errors,
        )
        if (
            "contamination_dominated" not in formalized_obligations
            and model_formalized
        ):
            contamination_threshold = threshold_values.get(
                "contaminationThreshold"
            )
            if (
                contamination_threshold is not None
                and 2 <= contamination_threshold
            ):
                derived_obligations.append(model_key)
                formalized_obligations.append("contamination_dominated")
                reason = "obligation not formalized: contamination_dominated"
                if reason in incomplete_reasons:
                    incomplete_reasons.remove(reason)
            else:
                incomplete_reasons.append(
                    "contamination_sqrt_log_model_bound requires "
                    "contaminationThreshold >= 2"
                )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_derived_obligations": derived_obligations,
            "formalized_final_handoff_obligations": [],
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "coefficient": str(coefficient) if coefficient is not None else None,
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": [],
        }

    if _is_dft_model_certificate_kind(kind):
        if "Gdbh.DiscreteCircleMethod" not in imports:
            errors.append("imports must include Gdbh.DiscreteCircleMethod")

        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in DFT_MODEL_L2_THRESHOLD_FIELDS
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        relative_error = _parse_fraction(
            certificate.get("relativeError"), "relativeError", errors
        )
        if relative_error is not None:
            if relative_error < 0:
                errors.append("relativeError must be non-negative")
            if relative_error >= 1:
                errors.append("relativeError must be less than 1")

        analytic_error_coefficient = _parse_fraction(
            certificate.get("analyticErrorCoefficient"),
            "analyticErrorCoefficient",
            errors,
        )
        if (
            analytic_error_coefficient is not None
            and relative_error is not None
            and analytic_error_coefficient > relative_error * Fraction(1, 4)
        ):
            incomplete_reasons.append(
                "analyticErrorCoefficient is above relativeError / 4"
            )

        function_names: dict[str, str] = {}
        if _is_dft_model_uniform_minor_sq_certificate_kind(kind):
            function_fields = DFT_MODEL_UNIFORM_MINOR_SQ_FUNCTION_FIELDS
        elif _is_dft_model_uniform_minor_certificate_kind(kind):
            function_fields = DFT_MODEL_UNIFORM_MINOR_FUNCTION_FIELDS
        else:
            function_fields = DFT_MODEL_L2_FUNCTION_FIELDS
        for field in function_fields:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        final_handoff_reasons: list[str] = []
        formalized_final_handoff_obligations = (
            _validate_decomposition_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete and not final_handoff_reasons
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": (
                kind if isinstance(kind, str) else CERTIFICATE_KIND
            ),
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": (
                formalized_final_handoff_obligations
            ),
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "analytic_error_coefficient": (
                str(analytic_error_coefficient)
                if analytic_error_coefficient is not None
                else None
            ),
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": final_handoff_reasons,
        }

    if _is_decomposition_certificate_kind(kind):
        threshold_fields = (
            LINEAR_DECOMPOSITION_THRESHOLD_FIELDS
            if kind == LINEAR_DECOMPOSITION_CERTIFICATE_KIND
            else DECOMPOSITION_THRESHOLD_FIELDS
        )
        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in threshold_fields
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        relative_error = _parse_fraction(
            certificate.get("relativeError"), "relativeError", errors
        )
        if relative_error is not None:
            if relative_error < 0:
                errors.append("relativeError must be non-negative")
            if relative_error >= 1:
                errors.append("relativeError must be less than 1")

        analytic_error_coefficient: Fraction | None = None
        if kind == LINEAR_DECOMPOSITION_CERTIFICATE_KIND:
            analytic_error_coefficient = _parse_fraction(
                certificate.get("analyticErrorCoefficient"),
                "analyticErrorCoefficient",
                errors,
            )
            if (
                analytic_error_coefficient is not None
                and relative_error is not None
                and analytic_error_coefficient
                > relative_error * Fraction(1, 4)
            ):
                incomplete_reasons.append(
                    "analyticErrorCoefficient is above relativeError / 4"
                )

        function_names: dict[str, str] = {}
        for field in DECOMPOSITION_FUNCTION_FIELDS:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        final_handoff_reasons: list[str] = []
        formalized_final_handoff_obligations = (
            _validate_decomposition_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete and not final_handoff_reasons
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": (
                kind if isinstance(kind, str) else CERTIFICATE_KIND
            ),
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": (
                formalized_final_handoff_obligations
            ),
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "analytic_error_coefficient": (
                str(analytic_error_coefficient)
                if analytic_error_coefficient is not None
                else None
            ),
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": final_handoff_reasons,
        }

    if _is_positive_linear_canonical_major_minor_certificate_kind(kind):
        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_THRESHOLD_FIELDS
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        coefficient = _parse_fraction(
            certificate.get("coefficient"), "coefficient", errors
        )
        if coefficient is not None and coefficient <= 0:
            errors.append("coefficient must be positive")

        function_names: dict[str, str] = {}
        for field in POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_FUNCTION_FIELDS:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        final_handoff_reasons: list[str] = []
        formalized_final_handoff_obligations = (
            _validate_decomposition_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete and not final_handoff_reasons
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": (
                formalized_final_handoff_obligations
            ),
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "coefficient": str(coefficient) if coefficient is not None else None,
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": final_handoff_reasons,
        }

    if (
        _is_positive_linear_explicit_contamination_canonical_major_minor_certificate_kind(
            kind
        )
    ):
        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in (
                POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_THRESHOLD_FIELDS
            )
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        coefficient = _parse_fraction(
            certificate.get("coefficient"), "coefficient", errors
        )
        if coefficient is not None and coefficient <= 0:
            errors.append("coefficient must be positive")

        function_names: dict[str, str] = {}
        for field in POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_FUNCTION_FIELDS:
            function_names[field] = _expect_string(
                certificate.get(field), field, errors
            )

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        if status == FORMALIZED_STATUS or formalized_obligations:
            for field, function_name in function_names.items():
                if function_name:
                    _validate_lean_identifier(function_name, field, errors)

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": [],
            "threshold_components": threshold_values,
            "function_fields": function_names,
            "coefficient": str(coefficient) if coefficient is not None else None,
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": [],
        }

    if _is_quarter_canonical_certificate_kind(kind):
        threshold = _expect_nonnegative_int(
            certificate.get("threshold"), "threshold", errors
        )
        if (
            threshold is not None
            and finite_bound is not None
            and threshold > finite_bound
        ):
            incomplete_reasons.append(
                "threshold is above the finite certificate bound"
            )

        relative_error = _parse_fraction(
            certificate.get("relativeError"), "relativeError", errors
        )
        if relative_error is not None:
            if relative_error < 0:
                errors.append("relativeError must be non-negative")
            if relative_error >= 1:
                errors.append("relativeError must be less than 1")

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        final_handoff_reasons: list[str] = []
        formalized_final_handoff_obligations = (
            _validate_decomposition_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete and not final_handoff_reasons
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": (
                formalized_final_handoff_obligations
            ),
            "threshold_components": {"threshold": threshold},
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": final_handoff_reasons,
        }

    if _is_positive_linear_raw_canonical_certificate_kind(kind):
        threshold = _expect_nonnegative_int(
            certificate.get("threshold"), "threshold", errors
        )
        if (
            threshold is not None
            and finite_bound is not None
            and threshold > finite_bound
        ):
            incomplete_reasons.append(
                "threshold is above the finite certificate bound"
            )

        coefficient = _parse_fraction(
            certificate.get("coefficient"), "coefficient", errors
        )
        if coefficient is not None and coefficient <= 0:
            errors.append("coefficient must be positive")

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        final_handoff_reasons: list[str] = []
        formalized_final_handoff_obligations = (
            _validate_decomposition_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete and not final_handoff_reasons
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": (
                formalized_final_handoff_obligations
            ),
            "threshold_components": {"threshold": threshold},
            "coefficient": str(coefficient) if coefficient is not None else None,
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": final_handoff_reasons,
        }

    if (
        _is_positive_linear_raw_explicit_contamination_canonical_certificate_kind(
            kind
        )
    ):
        threshold_values: dict[str, int | None] = {
            field: _expect_nonnegative_int(
                certificate.get(field), field, errors
            )
            for field in (
                POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_THRESHOLD_FIELDS
            )
        }
        if finite_bound is not None:
            for field, value in threshold_values.items():
                if value is not None and value > finite_bound:
                    incomplete_reasons.append(
                        f"{field} is above the finite certificate bound"
                    )

        coefficient = _parse_fraction(
            certificate.get("coefficient"), "coefficient", errors
        )
        if coefficient is not None and coefficient <= 0:
            errors.append("coefficient must be positive")

        obligations = _expect_mapping(
            certificate.get("obligations"), "obligations", errors
        )
        formalized_obligations = _validate_obligations(
            obligations,
            required_obligations,
            errors,
            incomplete_reasons,
        )

        valid = not errors
        estimate_complete = valid and not incomplete_reasons
        complete = estimate_complete
        return {
            "valid": valid,
            "complete": complete,
            "estimate_complete": estimate_complete,
            "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
            "lean_object": lean_object,
            "lean_strong_theorem": lean_strong_theorem,
            "lean_strong_theorem_le100": lean_strong_theorem_le100,
            "required_obligations": required_obligations,
            "imports": imports,
            "finite_certificate_theorem": (
                finite_certificate_theorem
                if isinstance(finite_certificate_theorem, str)
                else None
            ),
            "formalized_obligations": formalized_obligations,
            "formalized_final_handoff_obligations": [],
            "threshold_components": threshold_values,
            "coefficient": str(coefficient) if coefficient is not None else None,
            "errors": errors,
            "incomplete_reasons": incomplete_reasons,
            "final_handoff_reasons": [],
        }

    threshold = _expect_nonnegative_int(
        certificate.get("threshold"), "threshold", errors
    )
    if threshold is not None and finite_bound is not None and threshold > finite_bound:
        incomplete_reasons.append(
            "threshold is above the finite certificate bound"
        )

    coefficient = _parse_fraction(certificate.get("coefficient"), "coefficient", errors)
    if coefficient is not None and coefficient <= 0:
        errors.append("coefficient must be positive")

    relative_error = _parse_fraction(
        certificate.get("relativeError"), "relativeError", errors
    )
    if relative_error is not None:
        if relative_error < 0:
            errors.append("relativeError must be non-negative")
        if relative_error >= 1:
            errors.append("relativeError must be less than 1")

    singular_series = _expect_string(
        certificate.get("singularSeries"), "singularSeries", errors
    )
    weight_sum_bound = ""
    if requires_weight_sum_bound:
        weight_sum_bound = _expect_string(
            certificate.get("weightSumBound"), "weightSumBound", errors
        )

    obligations = _expect_mapping(
        certificate.get("obligations"), "obligations", errors
    )
    formalized_obligations = _validate_obligations(
        obligations, required_obligations, errors, incomplete_reasons
    )

    if status == FORMALIZED_STATUS or any(
        key in formalized_obligations for key in SINGULAR_SERIES_OBLIGATIONS
    ):
        if singular_series:
            _validate_lean_identifier(singular_series, "singularSeries", errors)
    if status == FORMALIZED_STATUS or any(
        key in formalized_obligations for key in WEIGHT_SUM_BOUND_OBLIGATIONS
    ):
        if weight_sum_bound:
            _validate_lean_identifier(weight_sum_bound, "weightSumBound", errors)

    valid = not errors
    estimate_complete = valid and not incomplete_reasons
    final_handoff_reasons: list[str] = []
    formalized_final_handoff_obligations: list[str] = []
    if kind == CANONICAL_CERTIFICATE_KIND:
        formalized_final_handoff_obligations = (
            _validate_canonical_final_handoff(
                certificate, errors, final_handoff_reasons
            )
        )
        valid = not errors
        estimate_complete = valid and not incomplete_reasons
    complete = estimate_complete and not final_handoff_reasons
    return {
        "valid": valid,
        "complete": complete,
        "estimate_complete": estimate_complete,
        "kind": kind if isinstance(kind, str) else CERTIFICATE_KIND,
        "lean_object": lean_object,
        "lean_strong_theorem": lean_strong_theorem,
        "lean_strong_theorem_le100": lean_strong_theorem_le100,
        "required_obligations": required_obligations,
        "imports": imports,
        "finite_certificate_theorem": (
            finite_certificate_theorem
            if isinstance(finite_certificate_theorem, str)
            else None
        ),
        "formalized_obligations": formalized_obligations,
        "formalized_final_handoff_obligations": (
            formalized_final_handoff_obligations
        ),
        "errors": errors,
        "incomplete_reasons": incomplete_reasons,
        "final_handoff_reasons": final_handoff_reasons,
    }


def _fraction_to_lean(value: str) -> str:
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return str(fraction.numerator)
    return f"({fraction.numerator} / {fraction.denominator})"


def _require_complete(certificate: dict[str, Any]) -> dict[str, Any]:
    status = validate_certificate(certificate)
    if not status["valid"] or not status["complete"]:
        raise ValueError(json.dumps(status, indent=2))
    return status


def _require_estimate_complete(certificate: dict[str, Any]) -> dict[str, Any]:
    status = validate_certificate(certificate)
    if not status["valid"] or not status["estimate_complete"]:
        raise ValueError(json.dumps(status, indent=2))
    return status


def _formalized_lean_term(
    certificate: dict[str, Any],
    json_field: str,
) -> str | None:
    raw_bound = certificate.get(json_field)
    if not isinstance(raw_bound, dict):
        return None
    if raw_bound.get("status") != FORMALIZED_STATUS:
        return None
    lean_term = raw_bound.get("lean_term")
    if isinstance(lean_term, str) and lean_term:
        return lean_term
    return None


def _decomposition_threshold_term(
    certificate: dict[str, Any],
    definition_name: str,
) -> str | None:
    direct_term = _formalized_lean_term(certificate, "derivedThresholdBound")
    if direct_term is not None:
        return direct_term

    contamination_term = _formalized_lean_term(
        certificate, "canonicalContaminationThresholdBound"
    )
    if contamination_term is None:
        return None
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      ({contamination_term})",
        ]
    )


def _quarter_canonical_threshold_term(
    certificate: dict[str, Any],
    definition_name: str,
) -> str | None:
    direct_term = _formalized_lean_term(certificate, "derivedThresholdBound")
    if direct_term is not None:
        return direct_term

    contamination_term = _formalized_lean_term(
        certificate, "canonicalContaminationThresholdBound"
    )
    if contamination_term is None:
        return None
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le",
            f"      (by norm_num [{definition_name}])",
            f"      ({contamination_term})",
        ]
    )


def _positive_linear_raw_canonical_threshold_term(
    certificate: dict[str, Any],
    definition_name: str,
) -> str | None:
    direct_term = _formalized_lean_term(certificate, "derivedThresholdBound")
    if direct_term is not None:
        return direct_term

    contamination_term = _formalized_lean_term(
        certificate, "canonicalContaminationThresholdBound"
    )
    if contamination_term is None:
        return None
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le",
            f"      (by norm_num [{definition_name}])",
            f"      ({contamination_term})",
        ]
    )


def _quarter_explicit_contamination_canonical_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _positive_linear_raw_explicit_contamination_canonical_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _positive_linear_canonical_major_minor_threshold_term(
    certificate: dict[str, Any],
    definition_name: str,
) -> str | None:
    direct_term = _formalized_lean_term(certificate, "derivedThresholdBound")
    if direct_term is not None:
        return direct_term

    contamination_term = _formalized_lean_term(
        certificate, "canonicalContaminationThresholdBound"
    )
    if contamination_term is None:
        return None
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      ({contamination_term})",
        ]
    )


def _positive_linear_explicit_contamination_canonical_major_minor_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _dft_uniform_minor_sq_positive_linear_explicit_contamination_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_threshold_term(
    definition_name: str,
) -> str:
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
        ]
    )


def _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_minor_dft_bound_term(
    certificate: dict[str, Any],
) -> str:
    obligations = certificate["obligations"]
    direct = obligations["minor_arc_uniform_dft_bound_valid"].get(
        "lean_declaration"
    )
    if isinstance(direct, str) and direct:
        return direct
    off_major_obligation = obligations.get(
        "minor_arc_uniform_dft_bound_off_major_arcs"
    )
    if isinstance(off_major_obligation, dict):
        off_major = off_major_obligation.get("lean_declaration")
        if isinstance(off_major, str) and off_major:
            return "\n".join(
                [
                    "Gdbh.DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs",
                    f"    (majorArcs := {certificate['majorArcs']})",
                    f"    (minorArcDftBound := {certificate['minorArcDftBound']})",
                    f"    {off_major}",
                ]
            )
    zero_major = obligations["zero_frequency_mem_major_arcs"][
        "lean_declaration"
    ]
    nonzero = obligations["minor_arc_uniform_dft_bound_nonzero"][
        "lean_declaration"
    ]
    return "\n".join(
        [
            "Gdbh.DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs",
            f"    (majorArcs := {certificate['majorArcs']})",
            f"    (minorArcDftBound := {certificate['minorArcDftBound']})",
            f"    {zero_major}",
            f"    {nonzero}",
        ]
    )


def _quarter_explicit_contamination_canonical_contamination_term(
    certificate: dict[str, Any],
) -> str:
    obligations = certificate["obligations"]
    direct = obligations["contamination_dominated"].get("lean_declaration")
    if isinstance(direct, str) and direct:
        return direct
    model_key = "contamination_sqrt_log_model_bound"
    model = obligations.get(model_key, {})
    if isinstance(model, dict):
        model_decl = model.get("lean_declaration")
        if isinstance(model_decl, str) and model_decl:
            relative_error = _fraction_to_lean(certificate["relativeError"])
            return "\n".join(
                [
                    "quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_"
                    "contamination_dominated_of_sqrt_log_model_ge_two_threshold",
                    f"      (threshold := {certificate['contaminationThreshold']})",
                    f"      (relativeError := ({relative_error} : ℝ))",
                    "      (by norm_num)",
                    f"      {model_decl}",
                ]
            )
    raise ValueError("contamination_dominated is not formalized or derived")


def _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
    certificate: dict[str, Any],
) -> str:
    obligations = certificate["obligations"]
    direct = obligations["contamination_dominated"].get("lean_declaration")
    if isinstance(direct, str) and direct:
        return direct
    model_key = "contamination_sqrt_log_model_bound"
    model = obligations.get(model_key, {})
    if isinstance(model, dict):
        model_decl = model.get("lean_declaration")
        if isinstance(model_decl, str) and model_decl:
            coefficient = _fraction_to_lean(certificate["coefficient"])
            return "\n".join(
                [
                    "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_"
                    "contamination_lt_const_mul_linear_of_sqrt_log_model_"
                    "ge_two_threshold",
                    f"      (threshold := {certificate['contaminationThreshold']})",
                    f"      (c := ({coefficient} : ℝ))",
                    "      (by norm_num)",
                    f"      {model_decl}",
                ]
            )
    raise ValueError("contamination_dominated is not formalized or derived")


def _dft_model_l2_threshold_term(
    certificate: dict[str, Any],
    definition_name: str,
) -> str | None:
    direct_term = _formalized_lean_term(certificate, "derivedThresholdBound")
    if direct_term is not None:
        return direct_term

    contamination_term = _formalized_lean_term(
        certificate, "canonicalContaminationThresholdBound"
    )
    if contamination_term is None:
        return None
    return "\n".join(
        [
            f"{definition_name}.directRawWeightSumThreshold_le_of_components",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      (by norm_num [{definition_name}])",
            f"      ({contamination_term})",
        ]
    )


def _add_explicit_lower_bound_100_alias(
    lean: str,
    definition_name: str,
) -> str:
    strong_name = f"strongGoldbach_from_{definition_name}"
    theorem_header = f"theorem {strong_name} :"
    alias_header = f"theorem explicitLowerBound100_from_{definition_name} :"
    if theorem_header not in lean or alias_header in lean:
        return lean
    marker = "end Gdbh\n"
    if marker not in lean:
        return lean
    alias = "\n".join(
        [
            f"theorem explicitLowerBound100_from_{definition_name} :",
            "    ExplicitGoldbachLowerBound 100 :=",
            "  strongGoldbach_iff_explicit_lower_bound100.mp",
            f"    {strong_name}",
            "",
        ]
    )
    return lean.replace(marker, alias + marker, 1)


def render_lean_handoff(
    certificate: dict[str, Any],
    *,
    definition_name: str = "analyticHandoffEstimate",
) -> str:
    status = _require_estimate_complete(certificate)
    _validate_lean_identifier(definition_name, "definition_name", errors := [])
    if errors:
        raise ValueError(errors[0])

    obligations = certificate["obligations"]
    imports = _validate_imports(certificate, errors := [])
    if errors:
        raise ValueError(errors[0])
    finite_bound = certificate["finite_certificate_bound"]
    finite_certificate_theorem = certificate.get("finiteCertificateTheorem")
    relative_error = (
        _fraction_to_lean(certificate["relativeError"])
        if "relativeError" in certificate
        else ""
    )

    if (
        status["kind"]
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND
    ):
        major_lower = obligations["major_arc_lower_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = (
            _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_minor_dft_bound_term(
                certificate
            )
        )
        contamination_model = obligations[
            "contamination_sqrt_log_model_bound"
        ]["lean_declaration"]
        threshold_term = (
            _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            "  contaminationThreshold_ge_two := by norm_num",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  majorArcLowerBound := {major_lower}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  contaminationSqrtLogModelBound := {contamination_model}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
            "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
            "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
                "lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        major_lower = obligations["major_arc_lower_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = (
            _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_minor_dft_bound_term(
                certificate
            )
        )
        contamination = (
            _quarter_explicit_contamination_canonical_contamination_term(
                certificate
            )
        )
        threshold_term = (
            _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  majorArcLowerBound := {major_lower}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
            "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
            "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_"
                "lower_bound_explicit_contamination_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        coefficient = _fraction_to_lean(certificate["coefficient"])
        major_linear = obligations["major_arc_linear_lower_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = obligations["minor_arc_uniform_dft_bound_valid"][
            "lean_declaration"
        ]
        contamination = (
            _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
                certificate
            )
        )
        threshold_term = (
            _dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  majorArcLinearLowerBound := {major_linear}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
            "explicit_contamination_canonical_lower_bound_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
            "explicit_contamination_canonical_lower_bound_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_"
                "explicit_contamination_canonical_lower_bound",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
    ):
        coefficient = _fraction_to_lean(certificate["coefficient"])
        major_linear = obligations["major_arc_linear_lower_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = obligations["minor_arc_uniform_dft_bound_valid"][
            "lean_declaration"
        ]
        minor_sq_error_bound = obligations[
            "minor_arc_dft_bound_sq_error_bound"
        ]["lean_declaration"]
        contamination = (
            _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
                certificate
            )
        )
        threshold_term = (
            _dft_uniform_minor_sq_positive_linear_explicit_contamination_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  majorArcLinearLowerBound := {major_linear}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  minorArcDftBoundSqErrorBound := {minor_sq_error_bound}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_"
            "contamination_canonical_lower_bound_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_"
            "contamination_canonical_lower_bound_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_"
                "contamination_canonical_lower_bound",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND:
        major_term_bound = obligations["major_arc_term_approximation_bound"][
            "lean_declaration"
        ]
        major_model_bound = obligations[
            "major_arc_model_approximation_bound"
        ]["lean_declaration"]
        major_error_bound = obligations["major_arc_error_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = obligations["minor_arc_uniform_dft_bound_valid"][
            "lean_declaration"
        ]
        minor_sq_error_bound = obligations[
            "minor_arc_dft_bound_sq_error_bound"
        ]["lean_declaration"]
        total_bound = obligations["total_linear_error_bound"][
            "lean_declaration"
        ]
        analytic_error_coefficient = _fraction_to_lean(
            certificate["analyticErrorCoefficient"]
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  totalLinearErrorThreshold := {certificate['totalLinearErrorThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_nonneg := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  analyticErrorCoefficient := ({analytic_error_coefficient} : ℝ)",
            "  analyticErrorCoefficient_le_quarter := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  majorArcModelTerm := {certificate['majorArcModelTerm']}",
            f"  majorArcTermError := {certificate['majorArcTermError']}",
            f"  majorArcModelError := {certificate['majorArcModelError']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  majorArcTermApproximationBound := {major_term_bound}",
            f"  majorArcModelApproximationBound := {major_model_bound}",
            f"  majorArcErrorBound := {major_error_bound}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  minorArcDftBoundSqErrorBound := {minor_sq_error_bound}",
            f"  totalLinearErrorBound := {total_bound}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_"
            "canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _dft_model_l2_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
                    "vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_"
                    "canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_"
                "canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND:
        major_term_bound = obligations["major_arc_term_approximation_bound"][
            "lean_declaration"
        ]
        major_model_bound = obligations[
            "major_arc_model_approximation_bound"
        ]["lean_declaration"]
        major_error_bound = obligations["major_arc_error_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = obligations["minor_arc_uniform_dft_bound_valid"][
            "lean_declaration"
        ]
        minor_frequency_count_bound = obligations[
            "minor_arc_frequency_count_bound_valid"
        ]["lean_declaration"]
        minor_square_error_bound = obligations[
            "minor_arc_square_sum_error_bound"
        ]["lean_declaration"]
        total_bound = obligations["total_linear_error_bound"][
            "lean_declaration"
        ]
        analytic_error_coefficient = _fraction_to_lean(
            certificate["analyticErrorCoefficient"]
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  totalLinearErrorThreshold := {certificate['totalLinearErrorThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_nonneg := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  analyticErrorCoefficient := ({analytic_error_coefficient} : ℝ)",
            "  analyticErrorCoefficient_le_quarter := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  majorArcModelTerm := {certificate['majorArcModelTerm']}",
            f"  majorArcTermError := {certificate['majorArcTermError']}",
            f"  majorArcModelError := {certificate['majorArcModelError']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  minorArcFrequencyCountBound := {certificate['minorArcFrequencyCountBound']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  majorArcTermApproximationBound := {major_term_bound}",
            f"  majorArcModelApproximationBound := {major_model_bound}",
            f"  majorArcErrorBound := {major_error_bound}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  minorArcFrequencyCountBoundValid := {minor_frequency_count_bound}",
            f"  minorArcSquareSumErrorBound := {minor_square_error_bound}",
            f"  totalLinearErrorBound := {total_bound}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_model_uniform_minor_quarter_linear_error_"
            "canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _dft_model_l2_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
                    "vonMangoldt_dft_model_uniform_minor_quarter_linear_error_"
                    "canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_model_uniform_minor_quarter_linear_error_"
                "canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == DFT_MODEL_L2_CERTIFICATE_KIND:
        major_term_bound = obligations["major_arc_term_approximation_bound"][
            "lean_declaration"
        ]
        major_model_bound = obligations[
            "major_arc_model_approximation_bound"
        ]["lean_declaration"]
        major_error_bound = obligations["major_arc_error_bound"][
            "lean_declaration"
        ]
        minor_dft_bound = obligations["minor_arc_dft_bound_valid"][
            "lean_declaration"
        ]
        minor_square_bound = obligations["minor_arc_square_sum_bound"][
            "lean_declaration"
        ]
        total_bound = obligations["total_linear_error_bound"][
            "lean_declaration"
        ]
        analytic_error_coefficient = _fraction_to_lean(
            certificate["analyticErrorCoefficient"]
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate where",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  totalLinearErrorThreshold := {certificate['totalLinearErrorThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_nonneg := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  analyticErrorCoefficient := ({analytic_error_coefficient} : ℝ)",
            "  analyticErrorCoefficient_le_quarter := by norm_num",
            f"  majorArcs := {certificate['majorArcs']}",
            f"  majorArcModelTerm := {certificate['majorArcModelTerm']}",
            f"  majorArcTermError := {certificate['majorArcTermError']}",
            f"  majorArcModelError := {certificate['majorArcModelError']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcDftBound := {certificate['minorArcDftBound']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  majorArcTermApproximationBound := {major_term_bound}",
            f"  majorArcModelApproximationBound := {major_model_bound}",
            f"  majorArcErrorBound := {major_error_bound}",
            f"  minorArcDftBoundValid := {minor_dft_bound}",
            f"  minorArcSquareSumBound := {minor_square_bound}",
            f"  totalLinearErrorBound := {total_bound}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
            "vonMangoldt_dft_model_l2_minor_quarter_linear_error_"
            "canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _dft_model_l2_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  DiscreteCircleMethod.strongGoldbach_of_finite_and_"
                    "vonMangoldt_dft_model_l2_minor_quarter_linear_error_"
                    "canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  DiscreteCircleMethod.explicit_lower_bound_of_"
                "vonMangoldt_dft_model_l2_minor_quarter_linear_error_"
                "canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == LINEAR_DECOMPOSITION_CERTIFICATE_KIND:
        raw_decomposition = obligations["raw_decomposition"]["lean_declaration"]
        major_bound = obligations["major_arc_approximation_bound"][
            "lean_declaration"
        ]
        minor_bound = obligations["minor_arc_contribution_bound"][
            "lean_declaration"
        ]
        total_bound = obligations["total_linear_error_bound"][
            "lean_declaration"
        ]
        analytic_error_coefficient = _fraction_to_lean(
            certificate["analyticErrorCoefficient"]
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate where",
            f"  decompositionThreshold := {certificate['decompositionThreshold']}",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  totalLinearErrorThreshold := {certificate['totalLinearErrorThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_nonneg := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  analyticErrorCoefficient := ({analytic_error_coefficient} : ℝ)",
            "  analyticErrorCoefficient_le_quarter := by norm_num",
            f"  majorArcContribution := {certificate['majorArcContribution']}",
            f"  minorArcContribution := {certificate['minorArcContribution']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  rawDecomposition := {raw_decomposition}",
            f"  majorArcApproximationBound := {major_bound}",
            f"  minorArcContributionBound := {minor_bound}",
            f"  totalLinearErrorBound := {total_bound}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_"
            "decomposition_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _decomposition_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_"
                    "decomposition_canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_quarter_linear_error_"
                "decomposition_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == DECOMPOSITION_CERTIFICATE_KIND:
        raw_decomposition = obligations["raw_decomposition"]["lean_declaration"]
        major_bound = obligations["major_arc_approximation_bound"][
            "lean_declaration"
        ]
        minor_bound = obligations["minor_arc_contribution_bound"][
            "lean_declaration"
        ]
        total_bound = obligations["total_analytic_error_bound"][
            "lean_declaration"
        ]
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate where",
            f"  decompositionThreshold := {certificate['decompositionThreshold']}",
            f"  majorArcThreshold := {certificate['majorArcThreshold']}",
            f"  minorArcThreshold := {certificate['minorArcThreshold']}",
            f"  totalAnalyticErrorThreshold := {certificate['totalAnalyticErrorThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  majorArcContribution := {certificate['majorArcContribution']}",
            f"  minorArcContribution := {certificate['minorArcContribution']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  rawDecomposition := {raw_decomposition}",
            f"  majorArcApproximationBound := {major_bound}",
            f"  minorArcContributionBound := {minor_bound}",
            f"  totalAnalyticErrorBound := {total_bound}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_"
            "hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _decomposition_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_"
                    "hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_quarter_split_threshold_"
                "hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND:
        coefficient = _fraction_to_lean(certificate["coefficient"])
        combined_lower = obligations["combined_lower_bound"][
            "lean_declaration"
        ]
        linear_net = obligations["linear_net_lower_bound"][
            "lean_declaration"
        ]
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate where",
            f"  combinedThreshold := {certificate['combinedThreshold']}",
            f"  linearNetThreshold := {certificate['linearNetThreshold']}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  mainTerm := {certificate['mainTerm']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  combinedLowerBound := {combined_lower}",
            f"  linearNetLowerBound := {linear_net}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_"
            "positive_linear_canonical_weight_sum_major_minor_arc_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = (
            _positive_linear_canonical_major_minor_threshold_term(
                certificate, definition_name
            )
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_"
                    "positive_linear_canonical_weight_sum_major_minor_arc_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_"
                "canonical_weight_sum_major_minor_arc_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND
    ):
        coefficient = _fraction_to_lean(certificate["coefficient"])
        combined_lower = obligations["combined_lower_bound"][
            "lean_declaration"
        ]
        linear_net = obligations["linear_net_lower_bound"][
            "lean_declaration"
        ]
        contamination = obligations["contamination_dominated"][
            "lean_declaration"
        ]
        threshold_term = (
            _positive_linear_explicit_contamination_canonical_major_minor_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate where",
            f"  combinedThreshold := {certificate['combinedThreshold']}",
            f"  linearNetThreshold := {certificate['linearNetThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  mainTerm := {certificate['mainTerm']}",
            f"  majorArcError := {certificate['majorArcError']}",
            f"  minorArcError := {certificate['minorArcError']}",
            f"  combinedLowerBound := {combined_lower}",
            f"  linearNetLowerBound := {linear_net}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_"
            "positive_linear_explicit_contamination_canonical_weight_sum_"
            "major_minor_arc_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_"
            "positive_linear_explicit_contamination_canonical_weight_sum_"
            "major_minor_arc_estimate_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_"
                "explicit_contamination_canonical_weight_sum_major_minor_arc_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
    ):
        coefficient = _fraction_to_lean(certificate["coefficient"])
        raw_lower = obligations["raw_linear_lower_bound"][
            "lean_declaration"
        ]
        contamination = obligations["contamination_dominated"][
            "lean_declaration"
        ]
        threshold_term = (
            _positive_linear_raw_explicit_contamination_canonical_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where",
            f"  rawThreshold := {certificate['rawThreshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  rawLinearLowerBound := {raw_lower}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
            "explicit_contamination_canonical_weight_sum_lower_bound_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
            "explicit_contamination_canonical_weight_sum_lower_bound_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_positive_linear_raw_"
                "explicit_contamination_canonical_weight_sum_lower_bound",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND:
        threshold = certificate["threshold"]
        coefficient = _fraction_to_lean(certificate["coefficient"])
        raw_lower = obligations["raw_linear_lower_bound"][
            "lean_declaration"
        ]
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound where",
            f"  threshold := {threshold}",
            f"  coefficient := ({coefficient} : ℝ)",
            "  coefficient_pos := by norm_num",
            f"  rawLinearLowerBound := {raw_lower}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
            "canonical_weight_sum_lower_bound_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _positive_linear_raw_canonical_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_"
                    "canonical_weight_sum_lower_bound_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_positive_linear_raw_"
                "canonical_weight_sum_lower_bound",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
    ):
        relative_error = _fraction_to_lean(certificate["relativeError"])
        raw_error = obligations["raw_normalized_error_bound"][
            "lean_declaration"
        ]
        contamination = (
            _quarter_explicit_contamination_canonical_contamination_term(
                certificate
            )
        )
        threshold_term = (
            _quarter_explicit_contamination_canonical_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate where",
            f"  threshold := {certificate['threshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  rawNormalizedErrorBound := {raw_error}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
            "normalized_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
            "normalized_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_"
                "normalized_explicit_contamination_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if (
        status["kind"]
        == QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
    ):
        relative_error = _fraction_to_lean(certificate["relativeError"])
        raw_lower = obligations["raw_relative_lower_bound"][
            "lean_declaration"
        ]
        contamination = (
            _quarter_explicit_contamination_canonical_contamination_term(
                certificate
            )
        )
        threshold_term = (
            _quarter_explicit_contamination_canonical_threshold_term(
                definition_name
            )
        )
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate where",
            f"  threshold := {certificate['threshold']}",
            f"  contaminationThreshold := {certificate['contaminationThreshold']}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  rawRelativeLowerBound := {raw_lower}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
            "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
            f"    (finite : GoldbachUpTo {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
            "lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            f"    finite {definition_name}",
            f"    ({threshold_term})",
            "",
        ]
        if isinstance(finite_certificate_theorem, str):
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    {finite_certificate_theorem}",
                    "",
                ]
            )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_"
                "lower_bound_explicit_contamination_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    if status["kind"] == QUARTER_CANONICAL_CERTIFICATE_KIND:
        threshold = certificate["threshold"]
        raw_error = obligations["raw_normalized_error_bound"][
            "lean_declaration"
        ]
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate where",
            f"  threshold := {threshold}",
            f"  relativeError := ({relative_error} : ℝ)",
            "  relativeError_lt_one := by norm_num",
            f"  rawNormalizedErrorBound := {raw_error}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
            "normalized_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_term = _quarter_canonical_threshold_term(
            certificate, definition_name
        )
        if threshold_term is not None:
            lines.extend(
                [
                    f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                    f"    (finite : GoldbachUpTo {finite_bound}) :",
                    "    StrongGoldbach :=",
                    "  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_"
                    "normalized_canonical_weight_sum_estimate_le",
                    f"    finite {definition_name}",
                    f"    ({threshold_term})",
                    "",
                ]
            )
            if isinstance(finite_certificate_theorem, str):
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name} :",
                        "    StrongGoldbach :=",
                        f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    {finite_certificate_theorem}",
                        "",
                    ]
                )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_"
                "normalized_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    threshold = certificate["threshold"]
    coefficient = _fraction_to_lean(certificate["coefficient"])
    singular_series = certificate["singularSeries"]
    singular_lower = obligations["singular_series_lower_bound"]["lean_declaration"]
    raw_error = obligations["raw_normalized_error_bound"]["lean_declaration"]

    if status["kind"] == CANONICAL_CERTIFICATE_KIND:
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where",
            f"  threshold := {threshold}",
            f"  coefficient := ({coefficient} : ℝ)",
            f"  relativeError := ({relative_error} : ℝ)",
            "  coefficient_pos := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  singularSeries := {singular_series}",
            f"  singularSeriesLowerBound := {singular_lower}",
            f"  rawNormalizedErrorBound := {raw_error}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            "    (hthreshold :",
            f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold ≤",
            f"        {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_"
            "normalized_canonical_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
        ]
        threshold_bound = certificate.get("derivedThresholdBound")
        if isinstance(threshold_bound, dict):
            threshold_term = threshold_bound.get("lean_term")
            if isinstance(threshold_term, str) and threshold_term:
                lines.extend(
                    [
                        f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                        f"    (finite : GoldbachUpTo {finite_bound}) :",
                        "    StrongGoldbach :=",
                        "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_"
                        "normalized_canonical_weight_sum_estimate_le",
                        f"    finite {definition_name}",
                        f"    ({threshold_term})",
                        "",
                    ]
                )
                if isinstance(finite_certificate_theorem, str):
                    lines.extend(
                        [
                            f"theorem strongGoldbach_from_{definition_name} :",
                            "    StrongGoldbach :=",
                            f"  strongGoldbach_from_{definition_name}_and_finite_certificate_closed",
                            f"    {finite_certificate_theorem}",
                            "",
                        ]
                    )
        lines.extend(
            [
                f"theorem explicitLowerBound_from_{definition_name} :",
                "    ExplicitGoldbachLowerBound",
                f"      {definition_name}.toDirectRawWeightSumLowerBound.threshold :=",
                "  explicit_lower_bound_of_vonMangoldt_hardy_littlewood_"
                "normalized_canonical_weight_sum_estimate",
                f"    {definition_name}",
                "",
                "end Gdbh",
                "",
            ]
        )
        return _add_explicit_lower_bound_100_alias(
            "\n".join(lines), definition_name
        )

    weight_sum_bound = certificate["weightSumBound"]
    weight_bound = obligations["non_prime_prime_power_weight_sum_bound"][
        "lean_declaration"
    ]
    contamination = obligations["contamination_dominated"]["lean_declaration"]

    lean = "\n".join(
        (
            [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
            f"noncomputable def {definition_name} :",
            "    VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate where",
            f"  threshold := {threshold}",
            f"  coefficient := ({coefficient} : ℝ)",
            f"  relativeError := ({relative_error} : ℝ)",
            "  coefficient_pos := by norm_num",
            "  relativeError_lt_one := by norm_num",
            f"  singularSeries := {singular_series}",
            f"  nonPrimePrimePowerWeightSumBound := {weight_sum_bound}",
            f"  singularSeriesLowerBound := {singular_lower}",
            f"  rawNormalizedErrorBound := {raw_error}",
            f"  nonPrimePrimePowerWeightSumBoundValid := {weight_bound}",
            f"  contaminationDominated := {contamination}",
            "",
            f"theorem strongGoldbach_from_{definition_name}_and_finite_certificate",
            f"    (finite : GoldbachUpTo {finite_bound})",
            f"    (hthreshold : {definition_name}.threshold ≤ {finite_bound}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_"
            "normalized_weight_sum_estimate_le",
            f"    finite {definition_name} hthreshold",
            "",
            f"theorem explicitLowerBound_from_{definition_name} :",
            f"    ExplicitGoldbachLowerBound {definition_name}.threshold :=",
            "  explicit_lower_bound_of_vonMangoldt_hardy_littlewood_"
            "normalized_weight_sum_estimate",
            f"    {definition_name}",
            "",
            ]
            + (
                [
                    f"theorem strongGoldbach_from_{definition_name} :",
                    "    StrongGoldbach :=",
                    f"  strongGoldbach_from_{definition_name}_and_finite_certificate",
                    f"    {finite_certificate_theorem}",
                    f"    (by norm_num [{definition_name}])",
                    "",
                ]
                if isinstance(finite_certificate_theorem, str)
                else []
            )
            + [
            "end Gdbh",
            "",
            ]
        )
    )
    return _add_explicit_lower_bound_100_alias(lean, definition_name)


def _require_valid(certificate: dict[str, Any]) -> dict[str, Any]:
    status = validate_certificate(certificate)
    if not status["valid"]:
        raise ValueError(json.dumps(status, indent=2))
    return status


def _render_lean_obligation_probe_for_keys(
    certificate: dict[str, Any],
    obligation_keys: list[str],
) -> str:
    if not obligation_keys:
        raise ValueError("no formalized obligations to check")
    obligations = certificate["obligations"]
    imports = _validate_imports(certificate, errors := [])
    if errors:
        raise ValueError(errors[0])
    if _is_quarter_explicit_contamination_family_certificate_kind(
        certificate.get("kind")
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        relative_error = _fraction_to_lean(certificate["relativeError"])
        if "raw_normalized_error_bound" in obligation_keys:
            raw_error = obligations["raw_normalized_error_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    f"    ∀ n : Nat, {certificate['threshold']} < n → Even n →",
                    "      |(RawVonMangoldtGoldbachSum n -",
                    "          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /",
                    "        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤",
                    f"        ({relative_error} : ℝ) :=",
                    f"  {raw_error}",
                    "",
                ]
            )
        if "raw_relative_lower_bound" in obligation_keys:
            raw_lower = obligations["raw_relative_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    f"    ∀ n : Nat, {certificate['threshold']} < n → Even n →",
                    f"      (1 - ({relative_error} : ℝ)) *",
                    "          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤",
                    "        RawVonMangoldtGoldbachSum n :=",
                    f"  {raw_lower}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = (
                _quarter_explicit_contamination_canonical_contamination_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        (1 - ({relative_error} : ℝ)) * (1 / 4 : ℝ) * (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        if "contamination_sqrt_log_model_bound" in obligation_keys:
            model_bound = obligations["contamination_sqrt_log_model_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                    "          (Real.sqrt (n : ℝ) *",
                    "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                    f"        ((1 - ({relative_error} : ℝ)) * (1 / 4 : ℝ)) *",
                    "          (n : ℝ) :=",
                    f"  {model_bound}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_quarter_canonical_certificate_kind(certificate.get("kind")):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        if "raw_normalized_error_bound" in obligation_keys:
            raw_error = obligations["raw_normalized_error_bound"][
                "lean_declaration"
            ]
            relative_error = _fraction_to_lean(certificate["relativeError"])
            lines.extend(
                [
                    "example :",
                    f"    ∀ n : Nat, {certificate['threshold']} < n → Even n →",
                    "      |(RawVonMangoldtGoldbachSum n -",
                    "          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /",
                    "        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤",
                    f"        ({relative_error} : ℝ) :=",
                    f"  {raw_error}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_positive_linear_canonical_major_minor_certificate_kind(
        certificate.get("kind")
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        if "combined_lower_bound" in obligation_keys:
            combined_lower = obligations["combined_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['combinedThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['mainTerm']} n -",
                    f"          {certificate['majorArcError']} n ≤",
                    "        RawVonMangoldtGoldbachSum n +",
                    f"          {certificate['minorArcError']} n :=",
                    f"  {combined_lower}",
                    "",
                ]
            )
        if "linear_net_lower_bound" in obligation_keys:
            linear_net = obligations["linear_net_lower_bound"][
                "lean_declaration"
            ]
            coefficient = _fraction_to_lean(certificate["coefficient"])
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['linearNetThreshold']} < n →",
                    "      Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        {certificate['mainTerm']} n -",
                    f"          {certificate['majorArcError']} n :=",
                    f"  {linear_net}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if (
        _is_positive_linear_explicit_contamination_canonical_major_minor_certificate_kind(
            certificate.get("kind")
        )
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        if "combined_lower_bound" in obligation_keys:
            combined_lower = obligations["combined_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['combinedThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['mainTerm']} n -",
                    f"          {certificate['majorArcError']} n ≤",
                    "        RawVonMangoldtGoldbachSum n +",
                    f"          {certificate['minorArcError']} n :=",
                    f"  {combined_lower}",
                    "",
                ]
            )
        if "linear_net_lower_bound" in obligation_keys:
            linear_net = obligations["linear_net_lower_bound"][
                "lean_declaration"
            ]
            coefficient = _fraction_to_lean(certificate["coefficient"])
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['linearNetThreshold']} < n →",
                    "      Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        {certificate['mainTerm']} n -",
                    f"          {certificate['majorArcError']} n :=",
                    f"  {linear_net}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = obligations["contamination_dominated"][
                "lean_declaration"
            ]
            coefficient = _fraction_to_lean(certificate["coefficient"])
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        ({coefficient} : ℝ) * (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if (
        _is_positive_linear_raw_explicit_contamination_canonical_certificate_kind(
            certificate.get("kind")
        )
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        coefficient = _fraction_to_lean(certificate["coefficient"])
        if "raw_linear_lower_bound" in obligation_keys:
            raw_lower = obligations["raw_linear_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['rawThreshold']} < n →",
                    "      Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) ≤",
                    "        RawVonMangoldtGoldbachSum n :=",
                    f"  {raw_lower}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = (
                _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        ({coefficient} : ℝ) * (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_positive_linear_raw_canonical_certificate_kind(
        certificate.get("kind")
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        if "raw_linear_lower_bound" in obligation_keys:
            raw_lower = obligations["raw_linear_lower_bound"][
                "lean_declaration"
            ]
            coefficient = _fraction_to_lean(certificate["coefficient"])
            lines.extend(
                [
                    "example :",
                    f"    ∀ n : Nat, {certificate['threshold']} < n → Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) ≤",
                    "        RawVonMangoldtGoldbachSum n :=",
                    f"  {raw_lower}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if (
        _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate_kind(
            certificate.get("kind")
        )
        or _is_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate_kind(
            certificate.get("kind")
        )
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        relative_error = _fraction_to_lean(certificate["relativeError"])
        if "major_arc_lower_bound" in obligation_keys:
            major_lower = obligations["major_arc_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      (1 - ({relative_error} : ℝ)) *",
                    "          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +",
                    f"          {certificate['minorArcDftBound']} n ^ 2 ≤",
                    "        DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                    f"          {certificate['majorArcs']} n :=",
                    f"  {major_lower}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_valid" in obligation_keys:
            minor_dft_bound = (
                _dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_minor_dft_bound_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = (
                _quarter_explicit_contamination_canonical_contamination_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        ((1 - ({relative_error} : ℝ)) * (1 / 4 : ℝ)) *",
                    "          (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        if "contamination_sqrt_log_model_bound" in obligation_keys:
            contamination_model = obligations[
                "contamination_sqrt_log_model_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                    "          (Real.sqrt (n : ℝ) *",
                    "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                    f"        ((1 - ({relative_error} : ℝ)) * (1 / 4 : ℝ)) *",
                    "          (n : ℝ) :=",
                    f"  {contamination_model}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if (
        _is_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate_kind(
            certificate.get("kind")
        )
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        coefficient = _fraction_to_lean(certificate["coefficient"])
        if "major_arc_linear_lower_bound" in obligation_keys:
            major_linear = obligations["major_arc_linear_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) +",
                    f"          {certificate['minorArcDftBound']} n ^ 2 ≤",
                    "        DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                    f"          {certificate['majorArcs']} n :=",
                    f"  {major_linear}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_valid" in obligation_keys:
            minor_dft_bound = obligations[
                "minor_arc_uniform_dft_bound_valid"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = (
                _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        ({coefficient} : ℝ) * (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if (
        _is_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate_kind(
            certificate.get("kind")
        )
    ):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        coefficient = _fraction_to_lean(certificate["coefficient"])
        if "major_arc_linear_lower_bound" in obligation_keys:
            major_linear = obligations["major_arc_linear_lower_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ({coefficient} : ℝ) * (n : ℝ) +",
                    f"          {certificate['minorArcError']} n ≤",
                    "        DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                    f"          {certificate['majorArcs']} n :=",
                    f"  {major_linear}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_valid" in obligation_keys:
            minor_dft_bound = obligations[
                "minor_arc_uniform_dft_bound_valid"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "minor_arc_dft_bound_sq_error_bound" in obligation_keys:
            square_error_bound = obligations[
                "minor_arc_dft_bound_sq_error_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['minorArcDftBound']} n ^ 2 ≤",
                    f"          {certificate['minorArcError']} n :=",
                    f"  {square_error_bound}",
                    "",
                ]
            )
        if "contamination_dominated" in obligation_keys:
            contamination = (
                _dft_uniform_minor_sq_positive_linear_explicit_contamination_term(
                    certificate
                )
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['contaminationThreshold']} < n →",
                    "      Even n →",
                    "      2 * vonMangoldtWeightSumContaminationBudget",
                    "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                    f"        ({coefficient} : ℝ) * (n : ℝ) :=",
                    f"  {contamination}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_dft_model_uniform_minor_sq_certificate_kind(certificate.get("kind")):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        if "major_arc_term_approximation_bound" in obligation_keys:
            major_term_bound = obligations[
                "major_arc_term_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ∀ k ∈ {certificate['majorArcs']} n,",
                    "        ‖DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k -",
                    f"            {certificate['majorArcModelTerm']} n k‖ ≤",
                    f"          {certificate['majorArcTermError']} n k :=",
                    f"  {major_term_bound}",
                    "",
                ]
            )
        if "major_arc_model_approximation_bound" in obligation_keys:
            major_model_bound = obligations[
                "major_arc_model_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ‖(∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcModelTerm']} n k) -",
                    "          (goldbachSingularSeriesFromQuarter n *",
                    "            (n : ℝ) : ℂ)‖ ≤",
                    f"        {certificate['majorArcModelError']} n :=",
                    f"  {major_model_bound}",
                    "",
                ]
            )
        if "major_arc_error_bound" in obligation_keys:
            major_error_bound = obligations["major_arc_error_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      (∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcTermError']} n k) +",
                    f"        {certificate['majorArcModelError']} n ≤",
                    f"          {certificate['majorArcError']} n :=",
                    f"  {major_error_bound}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_nonneg" in obligation_keys:
            minor_nonneg = obligations[
                "minor_arc_uniform_dft_bound_nonneg"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    f"      0 ≤ {certificate['minorArcDftBound']} n :=",
                    f"  {minor_nonneg}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_valid" in obligation_keys:
            minor_dft_bound = obligations[
                "minor_arc_uniform_dft_bound_valid"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "minor_arc_dft_bound_sq_error_bound" in obligation_keys:
            square_error_bound = obligations[
                "minor_arc_dft_bound_sq_error_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['minorArcDftBound']} n ^ 2 ≤",
                    f"          {certificate['minorArcError']} n :=",
                    f"  {square_error_bound}",
                    "",
                ]
            )
        if "total_linear_error_bound" in obligation_keys:
            total_bound = obligations["total_linear_error_bound"][
                "lean_declaration"
            ]
            analytic_error_coefficient = _fraction_to_lean(
                certificate["analyticErrorCoefficient"]
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['totalLinearErrorThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['majorArcError']} n +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        ({analytic_error_coefficient} : ℝ) *",
                    "          (n : ℝ) :=",
                    f"  {total_bound}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_dft_model_uniform_minor_certificate_kind(certificate.get("kind")):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        if "major_arc_term_approximation_bound" in obligation_keys:
            major_term_bound = obligations[
                "major_arc_term_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ∀ k ∈ {certificate['majorArcs']} n,",
                    "        ‖DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k -",
                    f"            {certificate['majorArcModelTerm']} n k‖ ≤",
                    f"          {certificate['majorArcTermError']} n k :=",
                    f"  {major_term_bound}",
                    "",
                ]
            )
        if "major_arc_model_approximation_bound" in obligation_keys:
            major_model_bound = obligations[
                "major_arc_model_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ‖(∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcModelTerm']} n k) -",
                    "          (goldbachSingularSeriesFromQuarter n *",
                    "            (n : ℝ) : ℂ)‖ ≤",
                    f"        {certificate['majorArcModelError']} n :=",
                    f"  {major_model_bound}",
                    "",
                ]
            )
        if "major_arc_error_bound" in obligation_keys:
            major_error_bound = obligations["major_arc_error_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      (∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcTermError']} n k) +",
                    f"        {certificate['majorArcModelError']} n ≤",
                    f"          {certificate['majorArcError']} n :=",
                    f"  {major_error_bound}",
                    "",
                ]
            )
        if "minor_arc_uniform_dft_bound_valid" in obligation_keys:
            minor_dft_bound = obligations[
                "minor_arc_uniform_dft_bound_valid"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "minor_arc_frequency_count_bound_valid" in obligation_keys:
            count_bound = obligations[
                "minor_arc_frequency_count_bound_valid"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ((DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n)).card : ℝ) ≤",
                    f"        {certificate['minorArcFrequencyCountBound']} n :=",
                    f"  {count_bound}",
                    "",
                ]
            )
        if "minor_arc_square_sum_error_bound" in obligation_keys:
            square_error_bound = obligations[
                "minor_arc_square_sum_error_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['minorArcFrequencyCountBound']} n *",
                    f"        (‖((n.succ : ℂ)⁻¹)‖ * {certificate['minorArcDftBound']} n ^ 2) ≤",
                    f"          {certificate['minorArcError']} n :=",
                    f"  {square_error_bound}",
                    "",
                ]
            )
        if "total_linear_error_bound" in obligation_keys:
            total_bound = obligations["total_linear_error_bound"][
                "lean_declaration"
            ]
            analytic_error_coefficient = _fraction_to_lean(
                certificate["analyticErrorCoefficient"]
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['totalLinearErrorThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['majorArcError']} n +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        ({analytic_error_coefficient} : ℝ) *",
                    "          (n : ℝ) :=",
                    f"  {total_bound}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_dft_model_l2_certificate_kind(certificate.get("kind")):
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "open scoped BigOperators",
            "",
            "namespace Gdbh",
            "",
        ]
        if "major_arc_term_approximation_bound" in obligation_keys:
            major_term_bound = obligations[
                "major_arc_term_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ∀ k ∈ {certificate['majorArcs']} n,",
                    "        ‖DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k -",
                    f"            {certificate['majorArcModelTerm']} n k‖ ≤",
                    f"          {certificate['majorArcTermError']} n k :=",
                    f"  {major_term_bound}",
                    "",
                ]
            )
        if "major_arc_model_approximation_bound" in obligation_keys:
            major_model_bound = obligations[
                "major_arc_model_approximation_bound"
            ]["lean_declaration"]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      ‖(∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcModelTerm']} n k) -",
                    "          (goldbachSingularSeriesFromQuarter n *",
                    "            (n : ℝ) : ℂ)‖ ≤",
                    f"        {certificate['majorArcModelError']} n :=",
                    f"  {major_model_bound}",
                    "",
                ]
            )
        if "major_arc_error_bound" in obligation_keys:
            major_error_bound = obligations["major_arc_error_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      (∑ k ∈ {certificate['majorArcs']} n,",
                    f"          {certificate['majorArcTermError']} n k) +",
                    f"        {certificate['majorArcModelError']} n ≤",
                    f"          {certificate['majorArcError']} n :=",
                    f"  {major_error_bound}",
                    "",
                ]
            )
        if "minor_arc_dft_bound_valid" in obligation_keys:
            minor_dft_bound = obligations["minor_arc_dft_bound_valid"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                    f"          {certificate['minorArcDftBound']} n k :=",
                    f"  {minor_dft_bound}",
                    "",
                ]
            )
        if "minor_arc_square_sum_bound" in obligation_keys:
            minor_square_bound = obligations["minor_arc_square_sum_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    "      ‖((n.succ : ℂ)⁻¹)‖ *",
                    "        (∑ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                    f"          ({certificate['majorArcs']} n),",
                    f"          {certificate['minorArcDftBound']} n k ^ 2) ≤",
                    f"        {certificate['minorArcError']} n :=",
                    f"  {minor_square_bound}",
                    "",
                ]
            )
        if "total_linear_error_bound" in obligation_keys:
            total_bound = obligations["total_linear_error_bound"][
                "lean_declaration"
            ]
            analytic_error_coefficient = _fraction_to_lean(
                certificate["analyticErrorCoefficient"]
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['totalLinearErrorThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['majorArcError']} n +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        ({analytic_error_coefficient} : ℝ) *",
                    "          (n : ℝ) :=",
                    f"  {total_bound}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    if _is_decomposition_certificate_kind(certificate.get("kind")):
        relative_error = _fraction_to_lean(certificate["relativeError"])
        lines = [
            *[f"import {module}" for module in imports],
            "",
            "namespace Gdbh",
            "",
        ]
        if "raw_decomposition" in obligation_keys:
            raw_decomposition = obligations["raw_decomposition"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['decompositionThreshold']} < n →",
                    "      Even n →",
                    "      RawVonMangoldtGoldbachSum n =",
                    f"        {certificate['majorArcContribution']} n +",
                    f"          {certificate['minorArcContribution']} n :=",
                    f"  {raw_decomposition}",
                    "",
                ]
            )
        if "major_arc_approximation_bound" in obligation_keys:
            major_bound = obligations["major_arc_approximation_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['majorArcThreshold']} < n →",
                    "      Even n →",
                    f"      |{certificate['majorArcContribution']} n -",
                    "          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤",
                    f"        {certificate['majorArcError']} n :=",
                    f"  {major_bound}",
                    "",
                ]
            )
        if "minor_arc_contribution_bound" in obligation_keys:
            minor_bound = obligations["minor_arc_contribution_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['minorArcThreshold']} < n →",
                    "      Even n →",
                    f"      |{certificate['minorArcContribution']} n| ≤",
                    f"        {certificate['minorArcError']} n :=",
                    f"  {minor_bound}",
                    "",
                ]
            )
        if "total_analytic_error_bound" in obligation_keys:
            total_bound = obligations["total_analytic_error_bound"][
                "lean_declaration"
            ]
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['totalAnalyticErrorThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['majorArcError']} n +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        ({relative_error} : ℝ) *",
                    "          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) :=",
                    f"  {total_bound}",
                    "",
                ]
            )
        if "total_linear_error_bound" in obligation_keys:
            total_bound = obligations["total_linear_error_bound"][
                "lean_declaration"
            ]
            analytic_error_coefficient = _fraction_to_lean(
                certificate["analyticErrorCoefficient"]
            )
            lines.extend(
                [
                    "example :",
                    "    ∀ n : Nat,",
                    f"      {certificate['totalLinearErrorThreshold']} < n →",
                    "      Even n →",
                    f"      {certificate['majorArcError']} n +",
                    f"          {certificate['minorArcError']} n ≤",
                    f"        ({analytic_error_coefficient} : ℝ) *",
                    "          (n : ℝ) :=",
                    f"  {total_bound}",
                    "",
                ]
            )
        lines.extend(["end Gdbh", ""])
        return "\n".join(lines)

    threshold = certificate["threshold"]
    coefficient = _fraction_to_lean(certificate["coefficient"])
    relative_error = _fraction_to_lean(certificate["relativeError"])
    singular_series = certificate["singularSeries"]

    lines = [
        *[f"import {module}" for module in imports],
        "",
        "namespace Gdbh",
        "",
    ]
    if "singular_series_lower_bound" in obligation_keys:
        singular_lower = obligations["singular_series_lower_bound"][
            "lean_declaration"
        ]
        lines.extend(
            [
                "example :",
                f"    ∀ n : Nat, {threshold} < n → Even n →",
                f"      ({coefficient} : ℝ) ≤ {singular_series} n :=",
                f"  {singular_lower}",
                "",
            ]
        )
    if "raw_normalized_error_bound" in obligation_keys:
        raw_error = obligations["raw_normalized_error_bound"]["lean_declaration"]
        lines.extend(
            [
                "example :",
                f"    ∀ n : Nat, {threshold} < n → Even n →",
                "      |(RawVonMangoldtGoldbachSum n -",
                f"          {singular_series} n * (n : ℝ)) /",
                f"        ({singular_series} n * (n : ℝ))| ≤",
                f"        ({relative_error} : ℝ) :=",
                f"  {raw_error}",
                "",
            ]
        )
    if "non_prime_prime_power_weight_sum_bound" in obligation_keys:
        weight_sum_bound = certificate["weightSumBound"]
        weight_bound = obligations["non_prime_prime_power_weight_sum_bound"][
            "lean_declaration"
        ]
        lines.extend(
            [
                "example :",
                f"    ∀ n : Nat, {threshold} < n → Even n →",
                "      NonPrimePrimePowerVonMangoldtWeightSum n ≤",
                f"        {weight_sum_bound} n :=",
                f"  {weight_bound}",
                "",
            ]
        )
    if "contamination_dominated" in obligation_keys:
        weight_sum_bound = certificate["weightSumBound"]
        contamination = obligations["contamination_dominated"][
            "lean_declaration"
        ]
        lines.extend(
            [
                "example :",
                f"    ∀ n : Nat, {threshold} < n → Even n →",
                "      2 * vonMangoldtWeightSumContaminationBudget",
                f"        {weight_sum_bound} n <",
                f"        ((1 - ({relative_error} : ℝ)) * ({coefficient} : ℝ)) *",
                "          (n : ℝ) :=",
                f"  {contamination}",
                "",
            ]
        )
    lines.extend(["end Gdbh", ""])
    return "\n".join(lines)


def render_lean_obligation_probe(certificate: dict[str, Any]) -> str:
    status = _require_estimate_complete(certificate)
    return _render_lean_obligation_probe_for_keys(
        certificate, list(status["required_obligations"])
    )


def render_lean_formalized_obligation_probe(certificate: dict[str, Any]) -> str:
    status = _require_valid(certificate)
    return _render_lean_obligation_probe_for_keys(
        certificate, list(status["formalized_obligations"])
    )


def _check_lean_probe(
    probe: str,
    *,
    workdir: Path,
) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as tmpdir:
        probe_path = Path(tmpdir) / "AnalyticHandoffProbe.lean"
        probe_path.write_text(probe)
        env = os.environ.copy()
        existing_lean_path = env.get("LEAN_PATH")
        env["LEAN_PATH"] = (
            str(workdir)
            if not existing_lean_path
            else f"{workdir}{os.pathsep}{existing_lean_path}"
        )
        return subprocess.run(
            [*_lake_command(), str(probe_path)],
            cwd=workdir,
            env=env,
            text=True,
            capture_output=True,
            check=False,
        )


def _lake_command() -> list[str]:
    lake = shutil.which("lake")
    if lake is None:
        fallback = Path.home() / ".elan" / "bin" / "lake"
        if fallback.exists():
            lake = str(fallback)
    if lake is None:
        raise FileNotFoundError("lake was not found in PATH or ~/.elan/bin")
    return [lake, "env", "lean"]


def check_lean_obligations(
    certificate: dict[str, Any],
    *,
    workdir: Path,
) -> subprocess.CompletedProcess[str]:
    return _check_lean_probe(
        render_lean_obligation_probe(certificate), workdir=workdir
    )


def check_lean_handoff(
    certificate: dict[str, Any],
    *,
    workdir: Path,
    definition_name: str = "analyticHandoffEstimate",
) -> subprocess.CompletedProcess[str]:
    return _check_lean_probe(
        render_lean_handoff(certificate, definition_name=definition_name),
        workdir=workdir,
    )


def check_formalized_lean_obligations(
    certificate: dict[str, Any],
    *,
    workdir: Path,
) -> subprocess.CompletedProcess[str]:
    return _check_lean_probe(
        render_lean_formalized_obligation_probe(certificate), workdir=workdir
    )


def export_lean_handoff(
    certificate: dict[str, Any],
    output_path: Path,
    *,
    definition_name: str = "analyticHandoffEstimate",
) -> None:
    output_path.write_text(
        render_lean_handoff(certificate, definition_name=definition_name)
    )


def load_certificate(path: Path) -> dict[str, Any]:
    return _expect_mapping(json.loads(path.read_text()), str(path), [])


def render_validation_status(path: Path) -> str:
    certificate = load_certificate(path)
    return json.dumps(validate_certificate(certificate), indent=2) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="validate analytic handoff certificate metadata"
    )
    parser.add_argument("certificate", type=Path)
    parser.add_argument(
        "--require-complete",
        action="store_true",
        help=(
            "exit with failure unless the certificate is final-handoff "
            "complete"
        ),
    )
    parser.add_argument(
        "--export-lean",
        type=Path,
        help=(
            "write a Lean wrapper for an estimate-complete analytic handoff "
            "certificate"
        ),
    )
    parser.add_argument(
        "--check-lean",
        action="store_true",
        help=(
            "type-check the formalized obligation declarations and generated "
            "handoff wrapper with Lean"
        ),
    )
    parser.add_argument(
        "--check-formalized-lean",
        action="store_true",
        help=(
            "type-check only the obligations already marked formalized, even "
            "when the certificate is incomplete"
        ),
    )
    parser.add_argument(
        "--definition-name",
        default="analyticHandoffEstimate",
        help="Lean definition name to use with --export-lean",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    certificate = load_certificate(args.certificate)
    status = validate_certificate(certificate)
    if not status["valid"]:
        print(json.dumps(status, indent=2))
        return 1
    if args.check_lean:
        if not status["estimate_complete"]:
            status["lean_checked"] = False
            status["lean_check_error"] = "certificate estimate is not complete"
            print(json.dumps(status, indent=2))
            return 1
        result = check_lean_obligations(certificate, workdir=Path.cwd())
        status["lean_checked"] = result.returncode == 0
        if result.returncode != 0:
            status["lean_check_error"] = result.stderr or result.stdout
            print(json.dumps(status, indent=2))
            return 1
        handoff_result = check_lean_handoff(
            certificate,
            workdir=Path.cwd(),
            definition_name=args.definition_name,
        )
        status["lean_handoff_checked"] = handoff_result.returncode == 0
        if handoff_result.returncode != 0:
            status["lean_handoff_check_error"] = (
                handoff_result.stderr or handoff_result.stdout
            )
            print(json.dumps(status, indent=2))
            return 1
    if args.check_formalized_lean:
        try:
            result = check_formalized_lean_obligations(
                certificate, workdir=Path.cwd()
            )
        except ValueError as error:
            status["formalized_lean_checked"] = False
            status["formalized_lean_check_error"] = str(error)
            print(json.dumps(status, indent=2))
            return 1
        status["formalized_lean_checked"] = result.returncode == 0
        if result.returncode != 0:
            status["formalized_lean_check_error"] = result.stderr or result.stdout
            print(json.dumps(status, indent=2))
            return 1
    if args.export_lean is not None:
        if not status["estimate_complete"]:
            print(json.dumps(status, indent=2))
            return 1
        export_lean_handoff(
            certificate,
            args.export_lean,
            definition_name=args.definition_name,
        )
    if args.require_complete and not status["complete"]:
        print(json.dumps(status, indent=2))
        return 1
    print(json.dumps(status, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
