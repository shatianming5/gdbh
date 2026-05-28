from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from analytic_handoff_certificate import (
    CANONICAL_CERTIFICATE_KIND,
    CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT,
    CANONICAL_LEAN_OBJECT,
    CANONICAL_REQUIRED_OBLIGATIONS,
    CERTIFICATE_KIND,
    CERTIFICATE_VERSION,
    DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT,
    DECOMPOSITION_CERTIFICATE_KIND,
    DECOMPOSITION_LEAN_OBJECT,
    DECOMPOSITION_REQUIRED_OBLIGATIONS,
    DFT_MODEL_L2_CERTIFICATE_KIND,
    DFT_MODEL_L2_LEAN_OBJECT,
    DFT_MODEL_L2_REQUIRED_OBLIGATIONS,
    DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND,
    DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT,
    DFT_MODEL_UNIFORM_MINOR_REQUIRED_OBLIGATIONS,
    DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND,
    DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT,
    DFT_MODEL_UNIFORM_MINOR_SQ_REQUIRED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_OBJECT,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_REQUIRED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
    DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
    DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS,
    DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
    DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS,
    LEAN_OBJECT,
    LINEAR_DECOMPOSITION_CERTIFICATE_KIND,
    LINEAR_DECOMPOSITION_LEAN_OBJECT,
    LINEAR_DECOMPOSITION_REQUIRED_OBLIGATIONS,
    POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
    POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
    POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
    POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
    POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
    POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
    QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
    QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS,
    QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
    QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
    QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
    QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS,
    QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
    QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
    POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
    POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
    POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
    POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND,
    POSITIVE_LINEAR_RAW_CANONICAL_LEAN_OBJECT,
    POSITIVE_LINEAR_RAW_CANONICAL_REQUIRED_OBLIGATIONS,
    QUARTER_CANONICAL_CERTIFICATE_KIND,
    QUARTER_CANONICAL_LEAN_OBJECT,
    QUARTER_CANONICAL_REQUIRED_OBLIGATIONS,
    REQUIRED_OBLIGATIONS,
    check_formalized_lean_obligations,
    check_lean_handoff,
    check_lean_obligations,
    render_lean_formalized_obligation_probe,
    render_lean_obligation_probe,
    render_lean_handoff,
    validate_certificate,
)


PROJECT_ROOT = Path(__file__).parent


def lake_command() -> list[str] | None:
    lake = shutil.which("lake")
    if lake is None:
        fallback = Path.home() / ".elan" / "bin" / "lake"
        if fallback.exists():
            lake = str(fallback)
    if lake is None:
        return None
    return [lake, "env", "lean"]


def formalized_certificate() -> dict[str, object]:
    return {
        "kind": CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "coefficient": "1/4",
        "relativeError": "1/2",
        "singularSeries": "exampleSingularSeries",
        "weightSumBound": "exampleWeightSumBound",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in REQUIRED_OBLIGATIONS.items()
        },
    }


def canonical_formalized_certificate() -> dict[str, object]:
    return {
        "kind": CANONICAL_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": CANONICAL_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "coefficient": "1/4",
        "relativeError": "1/2",
        "singularSeries": "exampleSingularSeries",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in CANONICAL_REQUIRED_OBLIGATIONS.items()
        },
    }


def canonical_final_certificate() -> dict[str, object]:
    certificate = canonical_formalized_certificate()
    certificate["derivedThresholdBound"] = {
        "status": "formalized",
        "statement": CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT,
        "lean_term": (
            "Gdbh.example_canonical_threshold_bound exampleCanonicalHandoff"
        ),
    }
    return certificate


def quarter_canonical_formalized_certificate() -> dict[str, object]:
    return {
        "kind": QUARTER_CANONICAL_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": QUARTER_CANONICAL_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "relativeError": "1/2",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_quarter_{key}",
            }
            for key, statement in (
                QUARTER_CANONICAL_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def quarter_explicit_contamination_canonical_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "contaminationThreshold": 100,
        "relativeError": "1/2",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_quarter_explicit_contamination_"
                    f"canonical_{key}"
                ),
            }
            for key, statement in (
                QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def quarter_lower_bound_explicit_contamination_canonical_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT
        ),
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "contaminationThreshold": 100,
        "relativeError": "1/2",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_quarter_lower_bound_explicit_"
                    f"contamination_canonical_{key}"
                ),
            }
            for key, statement in (
                QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def quarter_lower_bound_explicit_contamination_canonical_with_derived_model_certificate(
) -> dict[str, object]:
    certificate = (
        quarter_lower_bound_explicit_contamination_canonical_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    contamination = obligations["contamination_dominated"]
    assert isinstance(contamination, dict)
    contamination["status"] = "missing"
    contamination["lean_declaration"] = ""
    obligations["contamination_sqrt_log_model_bound"] = {
        "status": "formalized",
        "statement": (
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_DERIVED_OBLIGATIONS[
                "contamination_sqrt_log_model_bound"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_quarter_lower_bound_explicit_contamination_"
            "canonical_sqrt_log_model_bound"
        ),
    }
    return certificate


def quarter_canonical_structured_final_certificate() -> dict[str, object]:
    certificate = quarter_canonical_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_quarter_canonical_contamination_threshold_bound "
            "exampleQuarterCanonicalHandoff"
        ),
    }
    return certificate


def positive_linear_raw_canonical_formalized_certificate() -> dict[str, object]:
    return {
        "kind": POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": POSITIVE_LINEAR_RAW_CANONICAL_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "threshold": 100,
        "coefficient": "1/8",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_positive_linear_raw_{key}",
            }
            for key, statement in (
                POSITIVE_LINEAR_RAW_CANONICAL_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def positive_linear_raw_canonical_structured_final_certificate(
) -> dict[str, object]:
    certificate = positive_linear_raw_canonical_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_positive_linear_raw_canonical_contamination_threshold_bound "
            "examplePositiveLinearRawCanonicalHandoff"
        ),
    }
    return certificate


def positive_linear_raw_explicit_contamination_canonical_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT
        ),
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "rawThreshold": 100,
        "contaminationThreshold": 100,
        "coefficient": "1/8",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_positive_linear_raw_explicit_contamination_"
                    f"canonical_{key}"
                ),
            }
            for key, statement in (
                POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def positive_linear_canonical_major_minor_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "combinedThreshold": 100,
        "linearNetThreshold": 100,
        "coefficient": "1/8",
        "mainTerm": "exampleMajorMinorMainTerm",
        "majorArcError": "exampleMajorArcError",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    f"Gdbh.example_positive_linear_canonical_major_minor_{key}"
                ),
            }
            for key, statement in (
                POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def positive_linear_canonical_major_minor_structured_final_certificate(
) -> dict[str, object]:
    certificate = positive_linear_canonical_major_minor_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_positive_linear_canonical_major_minor_contamination_threshold_bound "
            "examplePositiveLinearCanonicalMajorMinorHandoff"
        ),
    }
    return certificate


def positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_OBJECT
        ),
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "combinedThreshold": 100,
        "linearNetThreshold": 100,
        "contaminationThreshold": 100,
        "coefficient": "1/8",
        "mainTerm": "exampleMajorMinorMainTerm",
        "majorArcError": "exampleMajorArcError",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_positive_linear_explicit_contamination_"
                    f"canonical_major_minor_{key}"
                ),
            }
            for key, statement in (
                POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def decomposition_formalized_certificate() -> dict[str, object]:
    return {
        "kind": DECOMPOSITION_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": DECOMPOSITION_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "decompositionThreshold": 100,
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "totalAnalyticErrorThreshold": 100,
        "relativeError": "1/2",
        "majorArcContribution": "exampleMajorArcContribution",
        "minorArcContribution": "exampleMinorArcContribution",
        "majorArcError": "exampleMajorArcError",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in DECOMPOSITION_REQUIRED_OBLIGATIONS.items()
        },
    }


def decomposition_final_certificate() -> dict[str, object]:
    certificate = decomposition_formalized_certificate()
    certificate["derivedThresholdBound"] = {
        "status": "formalized",
        "statement": CANONICAL_DERIVED_THRESHOLD_BOUND_STATEMENT,
        "lean_term": (
            "Gdbh.example_decomposition_threshold_bound "
            "exampleDecompositionHandoff"
        ),
    }
    return certificate


def decomposition_structured_final_certificate() -> dict[str, object]:
    certificate = decomposition_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_decomposition_contamination_threshold_bound "
            "exampleDecompositionHandoff"
        ),
    }
    return certificate


def linear_decomposition_formalized_certificate() -> dict[str, object]:
    return {
        "kind": LINEAR_DECOMPOSITION_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": LINEAR_DECOMPOSITION_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "decompositionThreshold": 100,
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "totalLinearErrorThreshold": 100,
        "relativeError": "1/2",
        "analyticErrorCoefficient": "1/8",
        "majorArcContribution": "exampleMajorArcContribution",
        "minorArcContribution": "exampleMinorArcContribution",
        "majorArcError": "exampleMajorArcError",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in LINEAR_DECOMPOSITION_REQUIRED_OBLIGATIONS.items()
        },
    }


def linear_decomposition_structured_final_certificate() -> dict[str, object]:
    certificate = linear_decomposition_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_linear_decomposition_contamination_threshold_bound "
            "exampleLinearDecompositionHandoff"
        ),
    }
    return certificate


def dft_model_l2_formalized_certificate() -> dict[str, object]:
    return {
        "kind": DFT_MODEL_L2_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": DFT_MODEL_L2_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach", "Gdbh.DiscreteCircleMethod"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "totalLinearErrorThreshold": 100,
        "relativeError": "1/2",
        "analyticErrorCoefficient": "1/8",
        "majorArcs": "exampleMajorArcs",
        "majorArcModelTerm": "exampleMajorArcModelTerm",
        "majorArcTermError": "exampleMajorArcTermError",
        "majorArcModelError": "exampleMajorArcModelError",
        "majorArcError": "exampleMajorArcError",
        "minorArcDftBound": "exampleMinorArcDftBound",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in DFT_MODEL_L2_REQUIRED_OBLIGATIONS.items()
        },
    }


def dft_model_l2_structured_final_certificate() -> dict[str, object]:
    certificate = dft_model_l2_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_dft_model_l2_contamination_threshold_bound "
            "exampleDftModelL2Handoff"
        ),
    }
    return certificate


def dft_model_uniform_minor_formalized_certificate() -> dict[str, object]:
    return {
        "kind": DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach", "Gdbh.DiscreteCircleMethod"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "totalLinearErrorThreshold": 100,
        "relativeError": "1/2",
        "analyticErrorCoefficient": "1/8",
        "majorArcs": "exampleMajorArcs",
        "majorArcModelTerm": "exampleMajorArcModelTerm",
        "majorArcTermError": "exampleMajorArcTermError",
        "majorArcModelError": "exampleMajorArcModelError",
        "majorArcError": "exampleMajorArcError",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "minorArcFrequencyCountBound": "exampleMinorArcFrequencyCountBound",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in (
                DFT_MODEL_UNIFORM_MINOR_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_model_uniform_minor_structured_final_certificate() -> dict[str, object]:
    certificate = dft_model_uniform_minor_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_dft_model_uniform_minor_contamination_threshold_bound "
            "exampleDftModelUniformMinorHandoff"
        ),
    }
    return certificate


def dft_model_uniform_minor_sq_formalized_certificate() -> dict[str, object]:
    return {
        "kind": DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND,
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT,
        "imports": ["Gdbh.VonMangoldtGoldbach", "Gdbh.DiscreteCircleMethod"],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "totalLinearErrorThreshold": 100,
        "relativeError": "1/2",
        "analyticErrorCoefficient": "1/8",
        "majorArcs": "exampleMajorArcs",
        "majorArcModelTerm": "exampleMajorArcModelTerm",
        "majorArcTermError": "exampleMajorArcTermError",
        "majorArcModelError": "exampleMajorArcModelError",
        "majorArcError": "exampleMajorArcError",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": f"Gdbh.example_{key}",
            }
            for key, statement in (
                DFT_MODEL_UNIFORM_MINOR_SQ_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_model_uniform_minor_sq_structured_final_certificate() -> dict[str, object]:
    certificate = dft_model_uniform_minor_sq_formalized_certificate()
    certificate["canonicalContaminationThresholdBound"] = {
        "status": "formalized",
        "statement": (
            DECOMPOSITION_CANONICAL_CONTAMINATION_THRESHOLD_BOUND_STATEMENT
        ),
        "lean_term": (
            "Gdbh.example_dft_model_uniform_minor_sq_contamination_threshold_bound "
            "exampleDftModelUniformMinorSqHandoff"
        ),
    }
    return certificate


def dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT
        ),
        "imports": [
            "Gdbh.VonMangoldtGoldbach",
            "Gdbh.DiscreteCircleMethod",
        ],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "contaminationThreshold": 100,
        "coefficient": "1/8",
        "majorArcs": "exampleMajorArcs",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "minorArcError": "exampleMinorArcError",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_dft_uniform_minor_sq_positive_linear_"
                    f"explicit_contamination_{key}"
                ),
            }
            for key, statement in (
                DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate(
) -> dict[str, object]:
    certificate = (
        dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    contamination = obligations["contamination_dominated"]
    assert isinstance(contamination, dict)
    contamination["status"] = "missing"
    contamination["lean_declaration"] = ""
    obligations["contamination_sqrt_log_model_bound"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS[
                "contamination_sqrt_log_model_bound"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_positive_linear_"
            "explicit_contamination_sqrt_log_model_bound"
        ),
    }
    return certificate


def dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT
        ),
        "imports": [
            "Gdbh.VonMangoldtGoldbach",
            "Gdbh.DiscreteCircleMethod",
        ],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "contaminationThreshold": 100,
        "coefficient": "1/8",
        "majorArcs": "exampleMajorArcs",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_"
                    f"explicit_contamination_{key}"
                ),
            }
            for key, statement in (
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate(
) -> dict[str, object]:
    certificate = (
        dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    contamination = obligations["contamination_dominated"]
    assert isinstance(contamination, dict)
    contamination["status"] = "missing"
    contamination["lean_declaration"] = ""
    obligations["contamination_sqrt_log_model_bound"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS[
                "contamination_sqrt_log_model_bound"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_"
            "explicit_contamination_sqrt_log_model_bound"
        ),
    }
    return certificate


def dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_OBJECT
        ),
        "imports": [
            "Gdbh.VonMangoldtGoldbach",
            "Gdbh.DiscreteCircleMethod",
        ],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "contaminationThreshold": 100,
        "relativeError": "1/2",
        "majorArcs": "exampleMajorArcs",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_"
                    f"major_minor_lower_bound_explicit_contamination_{key}"
                ),
            }
            for key, statement in (
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_with_derived_model_certificate(
) -> dict[str, object]:
    certificate = (
        dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    contamination = obligations["contamination_dominated"]
    assert isinstance(contamination, dict)
    contamination["status"] = "missing"
    contamination["lean_declaration"] = ""
    obligations["contamination_sqrt_log_model_bound"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_DERIVED_OBLIGATIONS[
                "contamination_sqrt_log_model_bound"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_"
            "minor_lower_bound_explicit_contamination_sqrt_log_model_bound"
        ),
    }
    return certificate


def dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate(
) -> dict[str, object]:
    return {
        "kind": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND
        ),
        "version": CERTIFICATE_VERSION,
        "status": "formalized",
        "lean_object": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_OBJECT
        ),
        "imports": [
            "Gdbh.VonMangoldtGoldbach",
            "Gdbh.DiscreteCircleMethod",
        ],
        "finite_certificate_bound": 100,
        "finiteCertificateTheorem": "Gdbh.goldbachUpTo100",
        "majorArcThreshold": 100,
        "minorArcThreshold": 100,
        "contaminationThreshold": 100,
        "relativeError": "1/2",
        "majorArcs": "exampleMajorArcs",
        "minorArcDftBound": "exampleMinorArcUniformDftBound",
        "obligations": {
            key: {
                "status": "formalized",
                "statement": statement,
                "lean_declaration": (
                    "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_"
                    f"major_minor_lower_bound_sqrt_log_contamination_{key}"
                ),
            }
            for key, statement in (
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_REQUIRED_OBLIGATIONS.items()
            )
        },
    }


def dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_off_major_minor_certificate(
) -> dict[str, object]:
    certificate = (
        dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    minor_bound = obligations["minor_arc_uniform_dft_bound_valid"]
    assert isinstance(minor_bound, dict)
    minor_bound["status"] = "missing"
    minor_bound["lean_declaration"] = ""
    obligations["minor_arc_uniform_dft_bound_off_major_arcs"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                "minor_arc_uniform_dft_bound_off_major_arcs"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_"
            "minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_"
            "dft_bound_off_major_arcs"
        ),
    }
    return certificate


def dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_nonzero_minor_certificate(
) -> dict[str, object]:
    certificate = (
        dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
    )
    obligations = certificate["obligations"]
    assert isinstance(obligations, dict)
    minor_bound = obligations["minor_arc_uniform_dft_bound_valid"]
    assert isinstance(minor_bound, dict)
    minor_bound["status"] = "missing"
    minor_bound["lean_declaration"] = ""
    obligations["zero_frequency_mem_major_arcs"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                "zero_frequency_mem_major_arcs"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_"
            "minor_lower_bound_sqrt_log_contamination_zero_frequency_"
            "mem_major_arcs"
        ),
    }
    obligations["minor_arc_uniform_dft_bound_nonzero"] = {
        "status": "formalized",
        "statement": (
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_DERIVED_MINOR_OBLIGATIONS[
                "minor_arc_uniform_dft_bound_nonzero"
            ]
        ),
        "lean_declaration": (
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_"
            "minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_"
            "dft_bound_nonzero"
        ),
    }
    return certificate


class AnalyticHandoffCertificateTests(unittest.TestCase):
    def test_example_certificate_is_valid_but_incomplete(self) -> None:
        certificate = json.loads(
            (PROJECT_ROOT / "analytic_handoff_certificate.example.json").read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "certificate status is not formalized",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "obligation not formalized: raw_normalized_error_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "non_prime_prime_power_weight_sum_bound",
            status["formalized_obligations"],
        )
        self.assertNotIn(
            "obligation not formalized: non_prime_prime_power_weight_sum_bound",
            status["incomplete_reasons"],
        )

    def test_canonical_example_certificate_is_valid_but_incomplete(self) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], CANONICAL_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], CANONICAL_LEAN_OBJECT)
        self.assertIn(
            "certificate status is not formalized",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "obligation not formalized: raw_normalized_error_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "final handoff obligation not formalized: derived_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_quarter_canonical_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_quarter_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], QUARTER_CANONICAL_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], QUARTER_CANONICAL_LEAN_OBJECT)
        self.assertEqual(
            set(status["required_obligations"]),
            {"raw_normalized_error_bound"},
        )
        self.assertIn(
            "certificate status is not formalized",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "obligation not formalized: raw_normalized_error_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "final handoff obligation not formalized: "
            "canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )
        self.assertNotIn(
            "singular_series_lower_bound",
            status["required_obligations"],
        )

    def test_quarter_explicit_contamination_canonical_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_quarter_explicit_contamination_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {"raw_normalized_error_bound", "contamination_dominated"},
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["final_handoff_reasons"], [])
        self.assertIn(
            "obligation not formalized: contamination_dominated",
            status["incomplete_reasons"],
        )

    def test_quarter_lower_bound_explicit_contamination_canonical_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_quarter_lower_bound_explicit_contamination_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {"raw_relative_lower_bound", "contamination_dominated"},
        )
        self.assertNotIn(
            "raw_normalized_error_bound",
            status["required_obligations"],
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["final_handoff_reasons"], [])
        self.assertIn(
            "obligation not formalized: raw_relative_lower_bound",
            status["incomplete_reasons"],
        )

    def test_positive_linear_raw_canonical_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_positive_linear_raw_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"], POSITIVE_LINEAR_RAW_CANONICAL_CERTIFICATE_KIND
        )
        self.assertEqual(
            status["lean_object"], POSITIVE_LINEAR_RAW_CANONICAL_LEAN_OBJECT
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {"raw_linear_lower_bound"},
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertIn(
            "obligation not formalized: raw_linear_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "final handoff obligation not formalized: "
            "canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_positive_linear_raw_explicit_contamination_canonical_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_positive_linear_raw_explicit_contamination_canonical_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_LEAN_OBJECT,
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {"raw_linear_lower_bound", "contamination_dominated"},
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertIn(
            "obligation not formalized: contamination_dominated",
            status["incomplete_reasons"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_positive_linear_canonical_major_minor_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_positive_linear_canonical_major_minor_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"], POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND
        )
        self.assertEqual(
            status["lean_object"], POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_LEAN_OBJECT
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {"combined_lower_bound", "linear_net_lower_bound"},
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertIn("mainTerm", status["function_fields"])
        self.assertIn(
            "obligation not formalized: combined_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "final handoff obligation not formalized: "
            "canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_positive_linear_explicit_contamination_canonical_major_minor_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_positive_linear_explicit_contamination_canonical_major_minor_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_LEAN_OBJECT,
        )
        self.assertEqual(
            set(status["required_obligations"]),
            {
                "combined_lower_bound",
                "linear_net_lower_bound",
                "contamination_dominated",
            },
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertIn(
            "obligation not formalized: contamination_dominated",
            status["incomplete_reasons"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_decomposition_example_certificate_is_valid_but_incomplete(self) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_decomposition_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], DECOMPOSITION_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DECOMPOSITION_LEAN_OBJECT)
        self.assertIn(
            "certificate status is not formalized",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "obligation not formalized: minor_arc_contribution_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "final handoff obligation not formalized: canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_linear_decomposition_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_linear_decomposition_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], LINEAR_DECOMPOSITION_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], LINEAR_DECOMPOSITION_LEAN_OBJECT)
        self.assertIn(
            "obligation not formalized: total_linear_error_bound",
            status["incomplete_reasons"],
        )
        self.assertEqual(
            status["analytic_error_coefficient"],
            "1/8",
        )
        self.assertIn(
            "final handoff obligation not formalized: canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_model_l2_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_model_l2_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], DFT_MODEL_L2_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_L2_LEAN_OBJECT)
        self.assertIn(
            "obligation not formalized: minor_arc_square_sum_bound",
            status["incomplete_reasons"],
        )
        self.assertEqual(
            status["analytic_error_coefficient"],
            "1/8",
        )
        self.assertIn(
            "final handoff obligation not formalized: canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_model_uniform_minor_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_model_uniform_minor_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT)
        self.assertIn(
            "obligation not formalized: minor_arc_uniform_dft_bound_valid",
            status["incomplete_reasons"],
        )

    def test_dft_model_uniform_minor_sq_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_model_uniform_minor_sq_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(status["kind"], DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT)
        self.assertIn(
            "obligation not formalized: minor_arc_dft_bound_sq_error_bound",
            status["incomplete_reasons"],
        )
        self.assertNotIn(
            "minorArcFrequencyCountBound",
            status["function_fields"],
        )
        self.assertIn(
            "final handoff obligation not formalized: canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_uniform_minor_sq_positive_linear_explicit_contamination_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_uniform_minor_sq_positive_linear_explicit_contamination_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
        )
        self.assertIn(
            "obligation not formalized: major_arc_linear_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "contamination_dominated",
            status["required_obligations"],
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
        )
        self.assertIn(
            "obligation not formalized: major_arc_linear_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "contamination_dominated",
            status["required_obligations"],
        )
        self.assertNotIn(
            "minor_arc_dft_bound_sq_error_bound",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "analyticMajorArcs",
                "minorArcDftBound": "analyticMinorArcDftBound",
            },
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_LEAN_OBJECT,
        )
        self.assertIn(
            "obligation not formalized: major_arc_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "contamination_dominated",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "analyticMajorArcs",
                "minorArcDftBound": "analyticMinorArcDftBound",
            },
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_example_certificate_is_valid_but_incomplete(
        self,
    ) -> None:
        certificate = json.loads(
            (
                PROJECT_ROOT
                / "analytic_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_handoff_certificate.example.json"
            ).read_text()
        )
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertFalse(status["estimate_complete"])
        self.assertEqual(
            status["kind"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_CERTIFICATE_KIND,
        )
        self.assertEqual(
            status["lean_object"],
            DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_LEAN_OBJECT,
        )
        self.assertIn(
            "obligation not formalized: major_arc_lower_bound",
            status["incomplete_reasons"],
        )
        self.assertIn(
            "contamination_sqrt_log_model_bound",
            status["required_obligations"],
        )
        self.assertNotIn(
            "contamination_dominated",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "analyticMajorArcs",
                "minorArcDftBound": "analyticMinorArcDftBound",
            },
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_formalized_certificate_can_be_complete(self) -> None:
        status = validate_certificate(formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["complete"])
        self.assertTrue(status["estimate_complete"])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])
        self.assertEqual(
            status["finite_certificate_theorem"],
            "Gdbh.goldbachUpTo100",
        )

    def test_canonical_formalized_certificate_estimate_can_be_complete(self) -> None:
        status = validate_certificate(canonical_formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["required_obligations"], CANONICAL_REQUIRED_OBLIGATIONS)
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_canonical_final_certificate_can_be_complete(self) -> None:
        status = validate_certificate(canonical_final_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["formalized_final_handoff_obligations"],
            ["derived_threshold_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_quarter_canonical_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(quarter_canonical_formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            QUARTER_CANONICAL_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            status["formalized_obligations"],
            ["raw_normalized_error_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertIn(
            "missing final handoff obligation: "
            "derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_quarter_canonical_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            quarter_canonical_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["formalized_final_handoff_obligations"],
            ["canonical_contamination_threshold_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_quarter_explicit_contamination_canonical_formalized_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            quarter_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            QUARTER_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            set(status["formalized_obligations"]),
            {"raw_normalized_error_bound", "contamination_dominated"},
        )
        self.assertEqual(status["threshold_components"]["threshold"], 100)
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"], 100
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_quarter_lower_bound_explicit_contamination_canonical_formalized_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            quarter_lower_bound_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            QUARTER_LOWER_BOUND_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            set(status["formalized_obligations"]),
            {"raw_relative_lower_bound", "contamination_dominated"},
        )
        self.assertEqual(status["threshold_components"]["threshold"], 100)
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"], 100
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_quarter_lower_bound_explicit_contamination_can_derive_contamination_from_sqrt_log_model(
        self,
    ) -> None:
        status = validate_certificate(
            quarter_lower_bound_explicit_contamination_canonical_with_derived_model_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "contamination_dominated",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            ["contamination_sqrt_log_model_bound"],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_quarter_lower_bound_derived_contamination_requires_ge_two_threshold(
        self,
    ) -> None:
        certificate = (
            quarter_lower_bound_explicit_contamination_canonical_with_derived_model_certificate()
        )
        certificate["contaminationThreshold"] = 1

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "contamination_sqrt_log_model_bound requires contaminationThreshold >= 2",
            status["incomplete_reasons"],
        )

    def test_positive_linear_raw_canonical_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_raw_canonical_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            POSITIVE_LINEAR_RAW_CANONICAL_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            status["formalized_obligations"],
            ["raw_linear_lower_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertIn(
            "missing final handoff obligation: "
            "derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_positive_linear_raw_canonical_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_raw_canonical_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["formalized_final_handoff_obligations"],
            ["canonical_contamination_threshold_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_positive_linear_raw_explicit_contamination_canonical_formalized_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_raw_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            POSITIVE_LINEAR_RAW_EXPLICIT_CONTAMINATION_CANONICAL_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            set(status["formalized_obligations"]),
            {"raw_linear_lower_bound", "contamination_dominated"},
        )
        self.assertEqual(status["threshold_components"]["rawThreshold"], 100)
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"], 100
        )
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_positive_linear_canonical_major_minor_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_canonical_major_minor_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            POSITIVE_LINEAR_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            set(status["formalized_obligations"]),
            {"combined_lower_bound", "linear_net_lower_bound"},
        )
        self.assertEqual(
            status["threshold_components"]["combinedThreshold"],
            100,
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertIn(
            "missing final handoff obligation: "
            "derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_positive_linear_canonical_major_minor_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_canonical_major_minor_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["formalized_final_handoff_obligations"],
            ["canonical_contamination_threshold_bound"],
        )
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            status["required_obligations"],
            POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_CANONICAL_MAJOR_MINOR_REQUIRED_OBLIGATIONS,
        )
        self.assertEqual(
            set(status["formalized_obligations"]),
            {
                "combined_lower_bound",
                "linear_net_lower_bound",
                "contamination_dominated",
            },
        )
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"],
            100,
        )
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_decomposition_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(decomposition_formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["kind"], DECOMPOSITION_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DECOMPOSITION_LEAN_OBJECT)
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(DECOMPOSITION_REQUIRED_OBLIGATIONS),
        )
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_decomposition_final_certificate_can_be_complete(self) -> None:
        status = validate_certificate(decomposition_final_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["derived_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_decomposition_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(decomposition_structured_final_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["canonical_contamination_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_linear_decomposition_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(linear_decomposition_formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["kind"], LINEAR_DECOMPOSITION_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], LINEAR_DECOMPOSITION_LEAN_OBJECT)
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(LINEAR_DECOMPOSITION_REQUIRED_OBLIGATIONS),
        )
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_linear_decomposition_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            linear_decomposition_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["canonical_contamination_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_model_l2_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(dft_model_l2_formalized_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["kind"], DFT_MODEL_L2_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_L2_LEAN_OBJECT)
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(DFT_MODEL_L2_REQUIRED_OBLIGATIONS),
        )
        self.assertEqual(
            status["threshold_components"]["majorArcThreshold"],
            100,
        )
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_model_l2_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(dft_model_l2_structured_final_certificate())

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["canonical_contamination_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_model_uniform_minor_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_model_uniform_minor_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["kind"], DFT_MODEL_UNIFORM_MINOR_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_UNIFORM_MINOR_LEAN_OBJECT)
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(DFT_MODEL_UNIFORM_MINOR_REQUIRED_OBLIGATIONS),
        )
        self.assertIn(
            "minorArcFrequencyCountBound",
            status["function_fields"],
        )
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_model_uniform_minor_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_model_uniform_minor_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["canonical_contamination_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_model_uniform_minor_sq_formalized_certificate_estimate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_model_uniform_minor_sq_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertFalse(status["complete"])
        self.assertEqual(status["kind"], DFT_MODEL_UNIFORM_MINOR_SQ_CERTIFICATE_KIND)
        self.assertEqual(status["lean_object"], DFT_MODEL_UNIFORM_MINOR_SQ_LEAN_OBJECT)
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(DFT_MODEL_UNIFORM_MINOR_SQ_REQUIRED_OBLIGATIONS),
        )
        self.assertNotIn(
            "minor_arc_uniform_dft_bound_nonneg",
            status["required_obligations"],
        )
        self.assertNotIn(
            "minorArcFrequencyCountBound",
            status["function_fields"],
        )
        self.assertIn(
            "minorArcDftBound",
            status["function_fields"],
        )
        self.assertIn(
            "missing final handoff obligation: derived_threshold_bound or canonical_contamination_threshold_bound",
            status["final_handoff_reasons"],
        )

    def test_dft_model_uniform_minor_sq_structured_final_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_model_uniform_minor_sq_structured_final_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            ["canonical_contamination_threshold_bound"],
            status["formalized_final_handoff_obligations"],
        )
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(
                DFT_UNIFORM_MINOR_SQ_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS
            ),
        )
        self.assertNotIn(
            "minor_arc_uniform_dft_bound_nonneg",
            status["required_obligations"],
        )
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"],
            100,
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_POSITIVE_LINEAR_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS
            ),
        )
        self.assertNotIn(
            "minor_arc_dft_bound_sq_error_bound",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "exampleMajorArcs",
                "minorArcDftBound": "exampleMinorArcUniformDftBound",
            },
        )
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"],
            100,
        )
        self.assertEqual(status["coefficient"], "1/8")
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_EXPLICIT_CONTAMINATION_REQUIRED_OBLIGATIONS
            ),
        )
        self.assertNotIn(
            "minor_arc_dft_bound_sq_error_bound",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "exampleMajorArcs",
                "minorArcDftBound": "exampleMinorArcUniformDftBound",
            },
        )
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"],
            100,
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["formalized_final_handoff_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate_can_be_complete(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertEqual(
            set(status["formalized_obligations"]),
            set(
                DFT_UNIFORM_MINOR_SQ_FIXED_ERROR_QUARTER_MAJOR_MINOR_LOWER_BOUND_SQRT_LOG_CONTAMINATION_REQUIRED_OBLIGATIONS
            ),
        )
        self.assertNotIn(
            "contamination_dominated",
            status["required_obligations"],
        )
        self.assertEqual(
            status["function_fields"],
            {
                "majorArcs": "exampleMajorArcs",
                "minorArcDftBound": "exampleMinorArcUniformDftBound",
            },
        )
        self.assertEqual(
            status["threshold_components"]["contaminationThreshold"],
            100,
        )
        self.assertEqual(status["relative_error"], "1/2")
        self.assertEqual(status["formalized_derived_obligations"], [])
        self.assertEqual(status["errors"], [])
        self.assertEqual(status["incomplete_reasons"], [])
        self.assertEqual(status["final_handoff_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_requires_threshold_at_least_two(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
        )
        certificate["contaminationThreshold"] = 1
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "contamination_sqrt_log_model_bound requires contaminationThreshold >= 2",
            status["incomplete_reasons"],
        )

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_can_derive_minor_from_off_major_bound(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_off_major_minor_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "minor_arc_uniform_dft_bound_valid",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            ["minor_arc_uniform_dft_bound_off_major_arcs"],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_can_derive_minor_from_nonzero_bound(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_nonzero_minor_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "minor_arc_uniform_dft_bound_valid",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            [
                "zero_frequency_mem_major_arcs",
                "minor_arc_uniform_dft_bound_nonzero",
            ],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_dft_uniform_minor_sq_positive_linear_explicit_contamination_can_derive_contamination_from_sqrt_log_model(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "contamination_dominated",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            ["contamination_sqrt_log_model_bound"],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_can_derive_contamination_from_sqrt_log_model(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "contamination_dominated",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            ["contamination_sqrt_log_model_bound"],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_can_derive_contamination_from_sqrt_log_model(
        self,
    ) -> None:
        status = validate_certificate(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_with_derived_model_certificate()
        )

        self.assertTrue(status["valid"])
        self.assertTrue(status["estimate_complete"])
        self.assertTrue(status["complete"])
        self.assertIn(
            "contamination_dominated",
            status["formalized_obligations"],
        )
        self.assertEqual(
            status["formalized_derived_obligations"],
            ["contamination_sqrt_log_model_bound"],
        )
        self.assertEqual(status["incomplete_reasons"], [])

    def test_dft_uniform_minor_sq_positive_linear_derived_contamination_requires_ge_two_threshold(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate()
        )
        certificate["contaminationThreshold"] = 1

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "contamination_sqrt_log_model_bound requires contaminationThreshold >= 2",
            status["incomplete_reasons"],
        )

    def test_dft_uniform_minor_sq_fixed_error_positive_linear_derived_contamination_requires_ge_two_threshold(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate()
        )
        certificate["contaminationThreshold"] = 1

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "contamination_sqrt_log_model_bound requires contaminationThreshold >= 2",
            status["incomplete_reasons"],
        )

    def test_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_derived_contamination_requires_ge_two_threshold(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_with_derived_model_certificate()
        )
        certificate["contaminationThreshold"] = 1

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "contamination_sqrt_log_model_bound requires contaminationThreshold >= 2",
            status["incomplete_reasons"],
        )

    def test_linear_decomposition_error_coefficient_must_fit_relative_error(
        self,
    ) -> None:
        certificate = linear_decomposition_formalized_certificate()
        certificate["analyticErrorCoefficient"] = "1/4"

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "analyticErrorCoefficient is above relativeError / 4",
            status["incomplete_reasons"],
        )

    def test_dft_model_l2_error_coefficient_must_fit_relative_error(
        self,
    ) -> None:
        certificate = dft_model_l2_formalized_certificate()
        certificate["analyticErrorCoefficient"] = "1/4"

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "analyticErrorCoefficient is above relativeError / 4",
            status["incomplete_reasons"],
        )

    def test_dft_model_uniform_minor_error_coefficient_must_fit_relative_error(
        self,
    ) -> None:
        certificate = dft_model_uniform_minor_formalized_certificate()
        certificate["analyticErrorCoefficient"] = "1/4"

        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["estimate_complete"])
        self.assertIn(
            "analyticErrorCoefficient is above relativeError / 4",
            status["incomplete_reasons"],
        )

    def test_dft_model_l2_requires_discrete_circle_method_import(self) -> None:
        certificate = dft_model_l2_formalized_certificate()
        certificate["imports"] = ["Gdbh.VonMangoldtGoldbach"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "imports must include Gdbh.DiscreteCircleMethod",
            status["errors"],
        )

    def test_dft_model_uniform_minor_requires_discrete_circle_method_import(
        self,
    ) -> None:
        certificate = dft_model_uniform_minor_formalized_certificate()
        certificate["imports"] = ["Gdbh.VonMangoldtGoldbach"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "imports must include Gdbh.DiscreteCircleMethod",
            status["errors"],
        )

    def test_dft_uniform_minor_sq_positive_linear_requires_discrete_circle_method_import(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate()
        )
        certificate["imports"] = ["Gdbh.VonMangoldtGoldbach"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "imports must include Gdbh.DiscreteCircleMethod",
            status["errors"],
        )

    def test_dft_uniform_minor_sq_fixed_error_positive_linear_requires_discrete_circle_method_import(
        self,
    ) -> None:
        certificate = (
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate()
        )
        certificate["imports"] = ["Gdbh.VonMangoldtGoldbach"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "imports must include Gdbh.DiscreteCircleMethod",
            status["errors"],
        )

    def test_threshold_above_finite_bound_is_not_complete(self) -> None:
        certificate = formalized_certificate()
        certificate["threshold"] = 101
        status = validate_certificate(certificate)

        self.assertTrue(status["valid"])
        self.assertFalse(status["complete"])
        self.assertIn(
            "threshold is above the finite certificate bound",
            status["incomplete_reasons"],
        )

    def test_bad_rational_constants_are_rejected(self) -> None:
        certificate = formalized_certificate()
        certificate["coefficient"] = "-1/3"
        certificate["relativeError"] = "1"
        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn("coefficient must be positive", status["errors"])
        self.assertIn("relativeError must be less than 1", status["errors"])

    def test_obligation_statement_must_be_canonical(self) -> None:
        certificate = formalized_certificate()
        obligations = certificate["obligations"]
        assert isinstance(obligations, dict)
        raw = obligations["raw_normalized_error_bound"]
        assert isinstance(raw, dict)
        raw["statement"] = "we proved something close enough"

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "obligations.raw_normalized_error_bound.statement must equal the canonical statement",
            status["errors"],
        )

    def test_formalized_names_must_be_lean_identifiers(self) -> None:
        certificate = formalized_certificate()
        certificate["singularSeries"] = "not a Lean expression with spaces"

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn("singularSeries must be a Lean identifier", status["errors"])

    def test_imports_must_include_base_module(self) -> None:
        certificate = formalized_certificate()
        certificate["imports"] = ["Other.Module"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn(
            "imports must include Gdbh.VonMangoldtGoldbach",
            status["errors"],
        )

    def test_imports_must_be_module_names(self) -> None:
        certificate = formalized_certificate()
        certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", "not a module"]

        status = validate_certificate(certificate)

        self.assertFalse(status["valid"])
        self.assertIn("imports[1] must be a Lean module name", status["errors"])

    def test_render_lean_handoff_from_complete_certificate(self) -> None:
        lean = render_lean_handoff(
            formalized_certificate(),
            definition_name="exampleAnalyticHandoff",
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def exampleAnalyticHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertIn("coefficient := ((1 / 4) : ℝ)", lean)
        self.assertIn("relativeError := ((1 / 2) : ℝ)", lean)
        self.assertIn(
            "singularSeriesLowerBound := Gdbh.example_singular_series_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleAnalyticHandoff_and_finite_certificate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleAnalyticHandoff :",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleAnalyticHandoff :",
            lean,
        )
        self.assertIn("Gdbh.goldbachUpTo100", lean)

    def test_render_lean_handoff_from_complete_canonical_certificate(self) -> None:
        lean = render_lean_handoff(
            canonical_formalized_certificate(),
            definition_name="exampleCanonicalHandoff",
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def exampleCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertIn(
            "singularSeriesLowerBound := Gdbh.example_singular_series_lower_bound",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate",
            lean,
        )
        self.assertNotIn(
            "strongGoldbach_from_exampleCanonicalHandoff_and_finite_certificate_closed",
            lean,
        )

    def test_render_lean_handoff_from_final_canonical_certificate(self) -> None:
        lean = render_lean_handoff(
            canonical_final_certificate(),
            definition_name="exampleCanonicalHandoff",
        )

        self.assertIn(
            "theorem strongGoldbach_from_exampleCanonicalHandoff_and_finite_certificate_closed",
            lean,
        )
        self.assertIn(
            "Gdbh.example_canonical_threshold_bound exampleCanonicalHandoff",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleCanonicalHandoff :",
            lean,
        )
        self.assertIn("Gdbh.goldbachUpTo100", lean)

    def test_render_lean_handoff_from_structured_final_quarter_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            quarter_canonical_structured_final_certificate(),
            definition_name="exampleQuarterCanonicalHandoff",
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def exampleQuarterCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertNotIn("singularSeriesLowerBound :=", lean)
        self.assertIn(
            "rawNormalizedErrorBound := Gdbh.example_quarter_raw_normalized_error_bound",
            lean,
        )
        self.assertIn(
            "exampleQuarterCanonicalHandoff.directRawWeightSumThreshold_le",
            lean,
        )
        self.assertIn(
            "Gdbh.example_quarter_canonical_contamination_threshold_bound "
            "exampleQuarterCanonicalHandoff",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleQuarterCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleQuarterCanonicalHandoff :",
            lean,
        )
        self.assertIn("Gdbh.goldbachUpTo100", lean)

    def test_render_lean_handoff_from_quarter_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            quarter_explicit_contamination_canonical_formalized_certificate(),
            definition_name=(
                "exampleQuarterExplicitContaminationCanonicalHandoff"
            ),
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def exampleQuarterExplicitContaminationCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("relativeError := ((1 / 2) : ℝ)", lean)
        self.assertIn(
            "rawNormalizedErrorBound := Gdbh.example_quarter_explicit_contamination_canonical_raw_normalized_error_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated := Gdbh.example_quarter_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertIn(
            "exampleQuarterExplicitContaminationCanonicalHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleQuarterExplicitContaminationCanonicalHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_positive_linear_raw_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            positive_linear_raw_canonical_structured_final_certificate(),
            definition_name="examplePositiveLinearRawCanonicalHandoff",
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def examplePositiveLinearRawCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertIn("coefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "rawLinearLowerBound := Gdbh.example_positive_linear_raw_raw_linear_lower_bound",
            lean,
        )
        self.assertIn(
            "examplePositiveLinearRawCanonicalHandoff.directRawWeightSumThreshold_le",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_raw_canonical_contamination_threshold_bound "
            "examplePositiveLinearRawCanonicalHandoff",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_examplePositiveLinearRawCanonicalHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_positive_linear_raw_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            positive_linear_raw_explicit_contamination_canonical_formalized_certificate(),
            definition_name=(
                "examplePositiveLinearRawExplicitContaminationCanonicalHandoff"
            ),
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def examplePositiveLinearRawExplicitContaminationCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where",
            lean,
        )
        self.assertIn("rawThreshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("coefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "rawLinearLowerBound := Gdbh.example_positive_linear_raw_explicit_contamination_canonical_raw_linear_lower_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated := Gdbh.example_positive_linear_raw_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertIn(
            "examplePositiveLinearRawExplicitContaminationCanonicalHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_examplePositiveLinearRawExplicitContaminationCanonicalHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_positive_linear_canonical_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            positive_linear_canonical_major_minor_structured_final_certificate(),
            definition_name="examplePositiveLinearCanonicalMajorMinorHandoff",
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def examplePositiveLinearCanonicalMajorMinorHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate where",
            lean,
        )
        self.assertIn("combinedThreshold := 100", lean)
        self.assertIn("linearNetThreshold := 100", lean)
        self.assertIn("coefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn("mainTerm := exampleMajorMinorMainTerm", lean)
        self.assertIn(
            "combinedLowerBound := Gdbh.example_positive_linear_canonical_major_minor_combined_lower_bound",
            lean,
        )
        self.assertIn(
            "linearNetLowerBound := Gdbh.example_positive_linear_canonical_major_minor_linear_net_lower_bound",
            lean,
        )
        self.assertIn(
            "examplePositiveLinearCanonicalMajorMinorHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_canonical_major_minor_contamination_threshold_bound "
            "examplePositiveLinearCanonicalMajorMinorHandoff",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_examplePositiveLinearCanonicalMajorMinorHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_positive_linear_explicit_contamination_canonical_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate(),
            definition_name=(
                "examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff"
            ),
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate where",
            lean,
        )
        self.assertIn("combinedThreshold := 100", lean)
        self.assertIn("linearNetThreshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn(
            "contaminationDominated := Gdbh.example_positive_linear_explicit_contamination_canonical_major_minor_contamination_dominated",
            lean,
        )
        self.assertIn(
            "examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_final_decomposition_certificate(self) -> None:
        lean = render_lean_handoff(
            decomposition_final_certificate(),
            definition_name="exampleDecompositionHandoff",
        )

        self.assertIn(
            "VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("decompositionThreshold := 100", lean)
        self.assertIn(
            "majorArcContribution := exampleMajorArcContribution",
            lean,
        )
        self.assertIn(
            "rawDecomposition := Gdbh.example_raw_decomposition",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "Gdbh.example_decomposition_threshold_bound exampleDecompositionHandoff",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleDecompositionHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_decomposition_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            decomposition_structured_final_certificate(),
            definition_name="exampleDecompositionHandoff",
        )

        self.assertIn(
            "exampleDecompositionHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "by norm_num [exampleDecompositionHandoff]",
            lean,
        )
        self.assertIn(
            "Gdbh.example_decomposition_contamination_threshold_bound exampleDecompositionHandoff",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleDecompositionHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_linear_decomposition_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            linear_decomposition_structured_final_certificate(),
            definition_name="exampleLinearDecompositionHandoff",
        )

        self.assertIn(
            "VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("totalLinearErrorThreshold := 100", lean)
        self.assertIn("analyticErrorCoefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "analyticErrorCoefficient_le_quarter := by norm_num",
            lean,
        )
        self.assertIn(
            "totalLinearErrorBound := Gdbh.example_total_linear_error_bound",
            lean,
        )
        self.assertIn(
            "exampleLinearDecompositionHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "Gdbh.example_linear_decomposition_contamination_threshold_bound exampleLinearDecompositionHandoff",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleLinearDecompositionHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_dft_model_l2_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_model_l2_structured_final_certificate(),
            definition_name="exampleDftModelL2Handoff",
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("majorArcThreshold := 100", lean)
        self.assertIn("analyticErrorCoefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "majorArcTermApproximationBound := Gdbh.example_major_arc_term_approximation_bound",
            lean,
        )
        self.assertIn(
            "minorArcSquareSumBound := Gdbh.example_minor_arc_square_sum_bound",
            lean,
        )
        self.assertIn(
            "exampleDftModelL2Handoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_model_l2_contamination_threshold_bound exampleDftModelL2Handoff",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleDftModelL2Handoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_dft_model_uniform_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_model_uniform_minor_structured_final_certificate(),
            definition_name="exampleDftModelUniformMinorHandoff",
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn(
            "minorArcDftBound := exampleMinorArcUniformDftBound",
            lean,
        )
        self.assertIn(
            "minorArcFrequencyCountBound := exampleMinorArcFrequencyCountBound",
            lean,
        )
        self.assertIn(
            "minorArcDftBoundValid := Gdbh.example_minor_arc_uniform_dft_bound_valid",
            lean,
        )
        self.assertIn(
            "minorArcSquareSumErrorBound := Gdbh.example_minor_arc_square_sum_error_bound",
            lean,
        )
        self.assertIn(
            "exampleDftModelUniformMinorHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_model_uniform_minor_contamination_threshold_bound exampleDftModelUniformMinorHandoff",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleDftModelUniformMinorHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_structured_final_dft_model_uniform_minor_sq_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_model_uniform_minor_sq_structured_final_certificate(),
            definition_name="exampleDftModelUniformMinorSqHandoff",
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn(
            "minorArcDftBound := exampleMinorArcUniformDftBound",
            lean,
        )
        self.assertNotIn("minorArcFrequencyCountBound :=", lean)
        self.assertNotIn("minorArcDftBound_nonneg", lean)
        self.assertIn(
            "minorArcDftBoundSqErrorBound := Gdbh.example_minor_arc_dft_bound_sq_error_bound",
            lean,
        )
        self.assertIn(
            "exampleDftModelUniformMinorSqHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_model_uniform_minor_sq_contamination_threshold_bound exampleDftModelUniformMinorSqHandoff",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_exampleDftModelUniformMinorSqHandoff :",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleDftModelUniformMinorSqHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqPositiveLinearExplicitContaminationHandoff"
            ),
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound where",
            lean,
        )
        self.assertIn("majorArcThreshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("coefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "majorArcLinearLowerBound := Gdbh.example_dft_uniform_minor_sq_positive_linear_explicit_contamination_major_arc_linear_lower_bound",
            lean,
        )
        self.assertNotIn("minorArcDftBound_nonneg", lean)
        self.assertIn(
            "minorArcDftBoundSqErrorBound := Gdbh.example_dft_uniform_minor_sq_positive_linear_explicit_contamination_minor_arc_dft_bound_sq_error_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated := Gdbh.example_dft_uniform_minor_sq_positive_linear_explicit_contamination_contamination_dominated",
            lean,
        )
        self.assertIn(
            "exampleDftUniformMinorSqPositiveLinearExplicitContaminationHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound_le",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleDftUniformMinorSqPositiveLinearExplicitContaminationHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_positive_linear_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqPositiveLinearDerivedContaminationHandoff"
            ),
        )

        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_positive_linear_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated :=",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff"
            ),
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound where",
            lean,
        )
        self.assertIn("majorArcThreshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("coefficient := ((1 / 8) : ℝ)", lean)
        self.assertIn(
            "minorArcDftBound := exampleMinorArcUniformDftBound",
            lean,
        )
        self.assertIn(
            "majorArcLinearLowerBound := Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_major_arc_linear_lower_bound",
            lean,
        )
        self.assertIn(
            "minorArcDftBoundValid := Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_minor_arc_uniform_dft_bound_valid",
            lean,
        )
        self.assertNotIn("minorArcError :=", lean)
        self.assertNotIn("minorArcDftBoundSqErrorBound", lean)
        self.assertIn(
            "contaminationDominated := Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_contamination_dominated",
            lean,
        )
        self.assertIn(
            "exampleDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound_le",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_positive_linear_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorPositiveLinearDerivedContaminationHandoff"
            ),
        )

        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated :=",
            lean,
        )
        self.assertNotIn("minorArcDftBoundSqErrorBound", lean)

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_formalized_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationHandoff"
            ),
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("majorArcThreshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("relativeError := ((1 / 2) : ℝ)", lean)
        self.assertIn(
            "minorArcDftBound := exampleMinorArcUniformDftBound",
            lean,
        )
        self.assertIn(
            "majorArcLowerBound := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_major_arc_lower_bound",
            lean,
        )
        self.assertIn(
            "minorArcDftBoundValid := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_minor_arc_uniform_dft_bound_valid",
            lean,
        )
        self.assertNotIn("minorArcError :=", lean)
        self.assertNotIn("minorArcDftBoundSqErrorBound", lean)
        self.assertIn(
            "contaminationDominated := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_contamination_dominated",
            lean,
        )
        self.assertIn(
            "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_with_derived_model_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundDerivedContaminationHandoff"
            ),
        )

        self.assertIn(
            "quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated :=",
            lean,
        )
        self.assertNotIn("minorArcDftBoundSqErrorBound", lean)

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationHandoff"
            ),
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("contaminationThreshold_ge_two := by norm_num", lean)
        self.assertIn(
            "contaminationSqrtLogModelBound := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertNotIn("contaminationDominated :=", lean)
        self.assertNotIn("minorArcDftBoundSqErrorBound", lean)
        self.assertIn(
            "DiscreteCircleMethod.strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationHandoff :",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_off_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_off_major_minor_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogOffMajorMinorHandoff"
            ),
        )

        self.assertIn(
            "DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_off_major_arcs",
            lean,
        )
        self.assertNotIn(
            "minorArcDftBoundValid := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_valid",
            lean,
        )

    def test_render_lean_handoff_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_nonzero_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_nonzero_minor_certificate(),
            definition_name=(
                "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogNonzeroMinorHandoff"
            ),
        )

        self.assertIn(
            "DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_zero_frequency_mem_major_arcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_nonzero",
            lean,
        )
        self.assertNotIn(
            "minorArcDftBoundValid := Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_valid",
            lean,
        )

    def test_render_lean_obligation_probe_from_dft_model_uniform_minor_sq_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_model_uniform_minor_sq_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertNotIn("0 ≤ exampleMinorArcUniformDftBound n", lean)
        self.assertIn(
            "exampleMinorArcUniformDftBound n ^ 2 ≤",
            lean,
        )
        self.assertNotIn("exampleMinorArcFrequencyCountBound", lean)

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_positive_linear_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
            lean,
        )
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) +", lean)
        self.assertIn(
            "∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertIn(
            "exampleMinorArcUniformDftBound n ^ 2 ≤",
            lean,
        )
        self.assertNotIn("0 ≤ exampleMinorArcUniformDftBound n", lean)
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_positive_linear_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate()
        )

        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_positive_linear_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
            lean,
        )
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) +", lean)
        self.assertIn(
            "exampleMinorArcUniformDftBound n ^ 2 ≤",
            lean,
        )
        self.assertIn(
            "∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertNotIn("exampleMinorArcError n", lean)
        self.assertNotIn("0 ≤ exampleMinorArcUniformDftBound n", lean)
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_positive_linear_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate()
        )

        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
            lean,
        )
        self.assertIn(
            "(1 - ((1 / 2) : ℝ)) *",
            lean,
        )
        self.assertIn(
            "goldbachSingularSeriesFromQuarter n * (n : ℝ)",
            lean,
        )
        self.assertIn(
            "exampleMinorArcUniformDftBound n ^ 2 ≤",
            lean,
        )
        self.assertIn(
            "∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertNotIn("exampleMinorArcError n", lean)
        self.assertNotIn("0 ≤ exampleMinorArcUniformDftBound n", lean)
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_derived_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_with_derived_model_certificate()
        )

        self.assertIn(
            "quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model_ge_two_threshold",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
            lean,
        )
        self.assertIn(
            "vonMangoldtSqrtLogBudgetComparisonConstant",
            lean,
        )
        self.assertIn(
            "Real.sqrt (n : ℝ)",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_contamination_sqrt_log_model_bound",
            lean,
        )
        self.assertNotIn("vonMangoldtWeightSumContaminationBudget", lean)

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_off_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_off_major_minor_certificate()
        )

        self.assertIn(
            "DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_off_major_arcs",
            lean,
        )

    def test_render_lean_obligation_probe_from_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_nonzero_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_nonzero_minor_certificate()
        )

        self.assertIn(
            "DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_zero_frequency_mem_major_arcs",
            lean,
        )
        self.assertIn(
            "Gdbh.example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_nonzero",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_certificate(self) -> None:
        lean = render_lean_obligation_probe(formalized_certificate())

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat, 100 < n → Even n →", lean)
        self.assertIn(
            "((1 / 4) : ℝ) ≤ exampleSingularSeries n",
            lean,
        )
        self.assertIn(
            "Gdbh.example_raw_normalized_error_bound",
            lean,
        )
        self.assertIn(
            "NonPrimePrimePowerVonMangoldtWeightSum n ≤",
            lean,
        )
        self.assertIn(
            "vonMangoldtWeightSumContaminationBudget",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_canonical_certificate(self) -> None:
        lean = render_lean_obligation_probe(canonical_formalized_certificate())

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat, 100 < n → Even n →", lean)
        self.assertIn(
            "((1 / 4) : ℝ) ≤ exampleSingularSeries n",
            lean,
        )
        self.assertIn(
            "Gdbh.example_raw_normalized_error_bound",
            lean,
        )
        self.assertNotIn(
            "NonPrimePrimePowerVonMangoldtWeightSum",
            lean,
        )
        self.assertNotIn(
            "vonMangoldtWeightSumContaminationBudget",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_quarter_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            quarter_canonical_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat, 100 < n → Even n →", lean)
        self.assertIn("goldbachSingularSeriesFromQuarter n", lean)
        self.assertIn(
            "Gdbh.example_quarter_raw_normalized_error_bound",
            lean,
        )
        self.assertNotIn("exampleSingularSeries", lean)
        self.assertNotIn("singular_series_lower_bound", lean)

    def test_render_lean_handoff_from_quarter_lower_bound_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_handoff(
            quarter_lower_bound_explicit_contamination_canonical_formalized_certificate(),
            definition_name=(
                "exampleQuarterLowerBoundExplicitContaminationCanonicalHandoff"
            ),
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "noncomputable def exampleQuarterLowerBoundExplicitContaminationCanonicalHandoff :",
            lean,
        )
        self.assertIn(
            "VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate where",
            lean,
        )
        self.assertIn("threshold := 100", lean)
        self.assertIn("contaminationThreshold := 100", lean)
        self.assertIn("relativeError := ((1 / 2) : ℝ)", lean)
        self.assertIn(
            "rawRelativeLowerBound := Gdbh.example_quarter_lower_bound_explicit_contamination_canonical_raw_relative_lower_bound",
            lean,
        )
        self.assertIn(
            "contaminationDominated := Gdbh.example_quarter_lower_bound_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertIn(
            "exampleQuarterLowerBoundExplicitContaminationCanonicalHandoff.directRawWeightSumThreshold_le_of_components",
            lean,
        )
        self.assertIn(
            "strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le",
            lean,
        )
        self.assertIn(
            "explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate",
            lean,
        )
        self.assertNotIn("rawNormalizedErrorBound", lean)

    def test_render_lean_obligation_probe_from_complete_quarter_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            quarter_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("goldbachSingularSeriesFromQuarter n", lean)
        self.assertIn(
            "Gdbh.example_quarter_explicit_contamination_canonical_raw_normalized_error_bound",
            lean,
        )
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )
        self.assertIn("(1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)", lean)
        self.assertIn(
            "Gdbh.example_quarter_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertNotIn("exampleSingularSeries", lean)
        self.assertNotIn("singular_series_lower_bound", lean)

    def test_render_lean_obligation_probe_from_complete_quarter_lower_bound_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            quarter_lower_bound_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("goldbachSingularSeriesFromQuarter n", lean)
        self.assertIn(
            "Gdbh.example_quarter_lower_bound_explicit_contamination_canonical_raw_relative_lower_bound",
            lean,
        )
        self.assertIn("RawVonMangoldtGoldbachSum n", lean)
        self.assertIn("vonMangoldtWeightSumContaminationBudget", lean)
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )
        self.assertIn("(1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)", lean)
        self.assertIn(
            "Gdbh.example_quarter_lower_bound_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertNotIn("raw_normalized_error_bound", lean)

    def test_render_lean_obligation_probe_from_complete_positive_linear_raw_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            positive_linear_raw_canonical_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat, 100 < n → Even n →", lean)
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) ≤", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n", lean)
        self.assertIn(
            "Gdbh.example_positive_linear_raw_raw_linear_lower_bound",
            lean,
        )
        self.assertNotIn("goldbachSingularSeriesFromQuarter", lean)
        self.assertNotIn("relativeError", lean)

    def test_render_lean_obligation_probe_from_complete_positive_linear_raw_explicit_contamination_canonical_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            positive_linear_raw_explicit_contamination_canonical_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat,", lean)
        self.assertIn("100 < n →", lean)
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) ≤", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n", lean)
        self.assertIn(
            "vonMangoldtWeightSumContaminationBudget",
            lean,
        )
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_raw_explicit_contamination_canonical_raw_linear_lower_bound",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_raw_explicit_contamination_canonical_contamination_dominated",
            lean,
        )
        self.assertNotIn("goldbachSingularSeriesFromQuarter", lean)
        self.assertNotIn("relativeError", lean)

    def test_render_lean_obligation_probe_from_complete_positive_linear_canonical_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            positive_linear_canonical_major_minor_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("∀ n : Nat,", lean)
        self.assertIn("100 < n →", lean)
        self.assertIn("exampleMajorMinorMainTerm n -", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n +", lean)
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) +", lean)
        self.assertIn(
            "Gdbh.example_positive_linear_canonical_major_minor_combined_lower_bound",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_canonical_major_minor_linear_net_lower_bound",
            lean,
        )
        self.assertNotIn("goldbachSingularSeriesFromQuarter", lean)
        self.assertNotIn("relativeError", lean)

    def test_render_lean_obligation_probe_from_complete_positive_linear_explicit_contamination_canonical_major_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("exampleMajorMinorMainTerm n -", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n +", lean)
        self.assertIn("((1 / 8) : ℝ) * (n : ℝ) +", lean)
        self.assertIn(
            "vonMangoldtWeightSumContaminationBudget",
            lean,
        )
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )
        self.assertIn(
            "Gdbh.example_positive_linear_explicit_contamination_canonical_major_minor_contamination_dominated",
            lean,
        )
        self.assertNotIn("goldbachSingularSeriesFromQuarter", lean)
        self.assertNotIn("relativeError", lean)

    def test_render_lean_obligation_probe_from_complete_decomposition_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(decomposition_formalized_certificate())

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n =", lean)
        self.assertIn(
            "exampleMajorArcContribution n +",
            lean,
        )
        self.assertIn(
            "|exampleMajorArcContribution n -",
            lean,
        )
        self.assertIn(
            "|exampleMinorArcContribution n| ≤",
            lean,
        )
        self.assertIn(
            "goldbachSingularSeriesFromQuarter n * (n : ℝ)",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_linear_decomposition_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            linear_decomposition_formalized_certificate()
        )

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("RawVonMangoldtGoldbachSum n =", lean)
        self.assertIn(
            "exampleMajorArcError n +",
            lean,
        )
        self.assertIn(
            "((1 / 8) : ℝ) *",
            lean,
        )
        self.assertIn(
            "(n : ℝ)",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_dft_model_l2_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(dft_model_l2_formalized_certificate())

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn("open scoped BigOperators", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k",
            lean,
        )
        self.assertIn(
            "goldbachSingularSeriesFromQuarter n *",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertIn(
            "exampleMinorArcDftBound n k ^ 2",
            lean,
        )
        self.assertIn(
            "((1 / 8) : ℝ) *",
            lean,
        )

    def test_render_lean_obligation_probe_from_complete_dft_model_uniform_minor_certificate(
        self,
    ) -> None:
        lean = render_lean_obligation_probe(
            dft_model_uniform_minor_formalized_certificate()
        )

        self.assertIn("import Gdbh.DiscreteCircleMethod", lean)
        self.assertIn("open scoped BigOperators", lean)
        self.assertIn(
            "DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k",
            lean,
        )
        self.assertIn(
            "DiscreteCircleMethod.zmodMinorFrequencies",
            lean,
        )
        self.assertIn(
            "exampleMinorArcUniformDftBound n",
            lean,
        )
        self.assertIn(
            "exampleMinorArcFrequencyCountBound n *",
            lean,
        )
        self.assertIn(
            "exampleMinorArcUniformDftBound n ^ 2",
            lean,
        )

    def test_render_lean_handoff_rejects_incomplete_certificate(self) -> None:
        certificate = json.loads(
            (PROJECT_ROOT / "analytic_handoff_certificate.example.json").read_text()
        )

        with self.assertRaises(ValueError):
            render_lean_handoff(certificate)

        with self.assertRaises(ValueError):
            render_lean_obligation_probe(certificate)

    def test_render_formalized_obligation_probe_from_partial_certificate(self) -> None:
        certificate = json.loads(
            (PROJECT_ROOT / "analytic_handoff_certificate.example.json").read_text()
        )

        lean = render_lean_formalized_obligation_probe(certificate)

        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn(
            "NonPrimePrimePowerVonMangoldtWeightSum n ≤",
            lean,
        )
        self.assertIn(
            "canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n",
            lean,
        )
        self.assertNotIn("RawVonMangoldtGoldbachSum n -", lean)

    def test_example_formalized_obligations_typecheck_with_lean(self) -> None:
        if lake_command() is None:
            self.skipTest("lake is not available")

        certificate = json.loads(
            (PROJECT_ROOT / "analytic_handoff_certificate.example.json").read_text()
        )
        result = check_formalized_lean_obligations(
            certificate, workdir=PROJECT_ROOT
        )

        self.assertEqual(result.returncode, 0, result.stderr or result.stdout)

    def test_complete_mock_certificate_typechecks_with_lean(self) -> None:
        lake = lake_command()
        if lake is None:
            self.skipTest("lake is not available")

        with tempfile.TemporaryDirectory(
            prefix="TmpAnalytic", dir=PROJECT_ROOT
        ) as tmpdir:
            tmp_path = Path(tmpdir)
            mock_module = f"{tmp_path.name}.AnalyticMock"
            mock_path = tmp_path / "AnalyticMock.lean"
            mock_path.write_text(
                "\n".join(
                    [
                        "import Gdbh.VonMangoldtGoldbach",
                        "",
                        "namespace Gdbh",
                        "",
                        "noncomputable def exampleSingularSeries (_ : Nat) : ℝ := 1",
                        "noncomputable def exampleWeightSumBound (_ : Nat) : ℝ := 0",
                        "",
                        "axiom example_singular_series_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 4) : ℝ) ≤ exampleSingularSeries n",
                        "",
                        "axiom example_raw_normalized_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |(RawVonMangoldtGoldbachSum n -",
                        "          exampleSingularSeries n * (n : ℝ)) /",
                        "        (exampleSingularSeries n * (n : ℝ))| ≤",
                        "        ((1 / 2) : ℝ)",
                        "",
                        "axiom example_non_prime_prime_power_weight_sum_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      NonPrimePrimePowerVonMangoldtWeightSum n ≤",
                        "        exampleWeightSumBound n",
                        "",
                        "axiom example_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        exampleWeightSumBound n <",
                        "        ((1 - ((1 / 2) : ℝ)) * ((1 / 4) : ℝ)) *",
                        "          (n : ℝ)",
                        "",
                        "end Gdbh",
                        "",
                    ]
                )
            )
            env = os.environ.copy()
            existing_lean_path = env.get("LEAN_PATH")
            env["LEAN_PATH"] = (
                str(PROJECT_ROOT)
                if not existing_lean_path
                else f"{PROJECT_ROOT}{os.pathsep}{existing_lean_path}"
            )
            mock_result = subprocess.run(
                [*lake, "-o", str(tmp_path / "AnalyticMock.olean"), str(mock_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                mock_result.returncode,
                0,
                mock_result.stderr or mock_result.stdout,
            )

            certificate = formalized_certificate()
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleAnalyticHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = tmp_path / "GeneratedHandoff.lean"
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="exampleAnalyticHandoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

    def test_complete_mock_canonical_certificate_typechecks_with_lean(self) -> None:
        lake = lake_command()
        if lake is None:
            self.skipTest("lake is not available")

        with tempfile.TemporaryDirectory(
            prefix="TmpAnalyticCanonical", dir=PROJECT_ROOT
        ) as tmpdir:
            tmp_path = Path(tmpdir)
            mock_module = f"{tmp_path.name}.AnalyticMock"
            mock_path = tmp_path / "AnalyticMock.lean"
            mock_path.write_text(
                "\n".join(
                    [
                        "import Gdbh.VonMangoldtGoldbach",
                        "",
                        "namespace Gdbh",
                        "",
                        "noncomputable def exampleSingularSeries (_ : Nat) : ℝ := 1",
                        "noncomputable def exampleMajorMinorMainTerm (_ : Nat) : ℝ := 1",
                        "noncomputable def exampleMajorArcError (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMinorArcError (_ : Nat) : ℝ := 0",
                        "",
                        "axiom example_singular_series_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 4) : ℝ) ≤ exampleSingularSeries n",
                        "",
                        "axiom example_raw_normalized_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |(RawVonMangoldtGoldbachSum n -",
                        "          exampleSingularSeries n * (n : ℝ)) /",
                        "        (exampleSingularSeries n * (n : ℝ))| ≤",
                        "        ((1 / 2) : ℝ)",
                        "",
                        "axiom example_quarter_raw_normalized_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |(RawVonMangoldtGoldbachSum n -",
                        "          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /",
                        "        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤",
                        "        ((1 / 2) : ℝ)",
                        "",
                        "axiom example_quarter_explicit_contamination_canonical_raw_normalized_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |(RawVonMangoldtGoldbachSum n -",
                        "          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /",
                        "        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤",
                        "        ((1 / 2) : ℝ)",
                        "",
                        "axiom example_quarter_explicit_contamination_canonical_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *",
                        "          (n : ℝ)",
                        "",
                        "axiom example_quarter_lower_bound_explicit_contamination_canonical_raw_relative_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      (1 - ((1 / 2) : ℝ)) *",
                        "          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤",
                        "        RawVonMangoldtGoldbachSum n",
                        "",
                        "axiom example_quarter_lower_bound_explicit_contamination_canonical_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *",
                        "          (n : ℝ)",
                        "",
                        "axiom example_quarter_lower_bound_explicit_contamination_canonical_sqrt_log_model_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                        "          (Real.sqrt (n : ℝ) *",
                        "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                        "        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *",
                        "          (n : ℝ)",
                        "",
                        "axiom example_canonical_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate,",
                        "      estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100",
                        "",
                        "axiom example_quarter_canonical_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_positive_linear_raw_raw_linear_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) ≤",
                        "        RawVonMangoldtGoldbachSum n",
                        "",
                        "axiom example_positive_linear_raw_canonical_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_positive_linear_raw_explicit_contamination_canonical_raw_linear_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) ≤",
                        "        RawVonMangoldtGoldbachSum n",
                        "",
                        "axiom example_positive_linear_raw_explicit_contamination_canonical_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_positive_linear_canonical_major_minor_combined_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMajorMinorMainTerm n -",
                        "          exampleMajorArcError n ≤",
                        "        RawVonMangoldtGoldbachSum n +",
                        "          exampleMinorArcError n",
                        "",
                        "axiom example_positive_linear_canonical_major_minor_linear_net_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) +",
                        "          exampleMinorArcError n ≤",
                        "        exampleMajorMinorMainTerm n -",
                        "          exampleMajorArcError n",
                        "",
                        "axiom example_positive_linear_canonical_major_minor_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_positive_linear_explicit_contamination_canonical_major_minor_combined_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMajorMinorMainTerm n -",
                        "          exampleMajorArcError n ≤",
                        "        RawVonMangoldtGoldbachSum n +",
                        "          exampleMinorArcError n",
                        "",
                        "axiom example_positive_linear_explicit_contamination_canonical_major_minor_linear_net_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) +",
                        "          exampleMinorArcError n ≤",
                        "        exampleMajorMinorMainTerm n -",
                        "          exampleMajorArcError n",
                        "",
                        "axiom example_positive_linear_explicit_contamination_canonical_major_minor_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "end Gdbh",
                        "",
                    ]
                )
            )
            env = os.environ.copy()
            existing_lean_path = env.get("LEAN_PATH")
            env["LEAN_PATH"] = (
                str(PROJECT_ROOT)
                if not existing_lean_path
                else f"{PROJECT_ROOT}{os.pathsep}{existing_lean_path}"
            )
            mock_result = subprocess.run(
                [*lake, "-o", str(tmp_path / "AnalyticMock.olean"), str(mock_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                mock_result.returncode,
                0,
                mock_result.stderr or mock_result.stdout,
            )

            certificate = canonical_final_certificate()
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleCanonicalHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = tmp_path / "GeneratedCanonicalHandoff.lean"
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="exampleCanonicalHandoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                positive_linear_explicit_contamination_canonical_major_minor_formalized_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff"
                ),
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path
                / "GeneratedPositiveLinearExplicitContaminationCanonicalMajorMinorHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name=(
                        "examplePositiveLinearExplicitContaminationCanonicalMajorMinorHandoff"
                    ),
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                positive_linear_canonical_major_minor_structured_final_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="examplePositiveLinearCanonicalMajorMinorHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path / "GeneratedPositiveLinearCanonicalMajorMinorHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name=(
                        "examplePositiveLinearCanonicalMajorMinorHandoff"
                    ),
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = quarter_canonical_structured_final_certificate()
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleQuarterCanonicalHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = tmp_path / "GeneratedQuarterCanonicalHandoff.lean"
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="exampleQuarterCanonicalHandoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                quarter_explicit_contamination_canonical_formalized_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleQuarterExplicitContaminationCanonicalHandoff"
                ),
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path
                / "GeneratedQuarterExplicitContaminationCanonicalHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name=(
                        "exampleQuarterExplicitContaminationCanonicalHandoff"
                    ),
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                quarter_lower_bound_explicit_contamination_canonical_formalized_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleQuarterLowerBoundExplicitContaminationCanonicalHandoff"
                ),
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path
                / "GeneratedQuarterLowerBoundExplicitContaminationCanonicalHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name=(
                        "exampleQuarterLowerBoundExplicitContaminationCanonicalHandoff"
                    ),
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                quarter_lower_bound_explicit_contamination_canonical_with_derived_model_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            derived_handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleQuarterLowerBoundExplicitContaminationCanonicalDerivedHandoff"
                ),
            )
            self.assertEqual(
                derived_handoff_result.returncode,
                0,
                derived_handoff_result.stderr
                or derived_handoff_result.stdout,
            )

            certificate = (
                positive_linear_raw_canonical_structured_final_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="examplePositiveLinearRawCanonicalHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path / "GeneratedPositiveLinearRawCanonicalHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="examplePositiveLinearRawCanonicalHandoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            certificate = (
                positive_linear_raw_explicit_contamination_canonical_formalized_certificate()
            )
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "examplePositiveLinearRawExplicitContaminationCanonicalHandoff"
                ),
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = (
                tmp_path
                / "GeneratedPositiveLinearRawExplicitContaminationCanonicalHandoff.lean"
            )
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name=(
                        "examplePositiveLinearRawExplicitContaminationCanonicalHandoff"
                    ),
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

    def test_complete_mock_decomposition_certificate_typechecks_with_lean(
        self,
    ) -> None:
        lake = lake_command()
        if lake is None:
            self.skipTest("lake is not available")

        with tempfile.TemporaryDirectory(
            prefix="TmpAnalyticDecomposition", dir=PROJECT_ROOT
        ) as tmpdir:
            tmp_path = Path(tmpdir)
            mock_module = f"{tmp_path.name}.AnalyticMock"
            mock_path = tmp_path / "AnalyticMock.lean"
            mock_path.write_text(
                "\n".join(
                    [
                        "import Gdbh.VonMangoldtGoldbach",
                        "",
                        "namespace Gdbh",
                        "",
                        "noncomputable def exampleMajorArcContribution (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMinorArcContribution (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMajorArcError (_ : Nat) : ℝ := 1",
                        "noncomputable def exampleMinorArcError (_ : Nat) : ℝ := 1",
                        "",
                        "axiom example_raw_decomposition :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      RawVonMangoldtGoldbachSum n =",
                        "        exampleMajorArcContribution n +",
                        "          exampleMinorArcContribution n",
                        "",
                        "axiom example_major_arc_approximation_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |exampleMajorArcContribution n -",
                        "          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤",
                        "        exampleMajorArcError n",
                        "",
                        "axiom example_minor_arc_contribution_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |exampleMinorArcContribution n| ≤",
                        "        exampleMinorArcError n",
                        "",
                        "axiom example_total_analytic_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMajorArcError n +",
                        "          exampleMinorArcError n ≤",
                        "        ((1 / 2) : ℝ) *",
                        "          (goldbachSingularSeriesFromQuarter n * (n : ℝ))",
                        "",
                        "axiom example_decomposition_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate,",
                        "      estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100",
                        "",
                        "axiom example_decomposition_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_total_linear_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMajorArcError n +",
                        "          exampleMinorArcError n ≤",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_linear_decomposition_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "end Gdbh",
                        "",
                    ]
                )
            )
            env = os.environ.copy()
            existing_lean_path = env.get("LEAN_PATH")
            env["LEAN_PATH"] = (
                str(PROJECT_ROOT)
                if not existing_lean_path
                else f"{PROJECT_ROOT}{os.pathsep}{existing_lean_path}"
            )
            mock_result = subprocess.run(
                [*lake, "-o", str(tmp_path / "AnalyticMock.olean"), str(mock_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                mock_result.returncode,
                0,
                mock_result.stderr or mock_result.stdout,
            )

            certificate = decomposition_final_certificate()
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleDecompositionHandoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = tmp_path / "GeneratedDecompositionHandoff.lean"
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="exampleDecompositionHandoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            structured_certificate = decomposition_structured_final_certificate()
            structured_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                mock_module,
            ]

            structured_handoff_result = check_lean_handoff(
                structured_certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleDecompositionHandoff",
            )
            self.assertEqual(
                structured_handoff_result.returncode,
                0,
                structured_handoff_result.stderr
                or structured_handoff_result.stdout,
            )

            structured_wrapper_path = (
                tmp_path / "GeneratedStructuredDecompositionHandoff.lean"
            )
            structured_wrapper_path.write_text(
                render_lean_handoff(
                    structured_certificate,
                    definition_name="exampleDecompositionHandoff",
                )
            )
            structured_wrapper_result = subprocess.run(
                [*lake, str(structured_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                structured_wrapper_result.returncode,
                0,
                structured_wrapper_result.stderr
                or structured_wrapper_result.stdout,
            )

            linear_certificate = (
                linear_decomposition_structured_final_certificate()
            )
            linear_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                mock_module,
            ]

            linear_probe_result = check_lean_obligations(
                linear_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                linear_probe_result.returncode,
                0,
                linear_probe_result.stderr or linear_probe_result.stdout,
            )

            linear_handoff_result = check_lean_handoff(
                linear_certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleLinearDecompositionHandoff",
            )
            self.assertEqual(
                linear_handoff_result.returncode,
                0,
                linear_handoff_result.stderr or linear_handoff_result.stdout,
            )

            linear_wrapper_path = (
                tmp_path / "GeneratedLinearDecompositionHandoff.lean"
            )
            linear_wrapper_path.write_text(
                render_lean_handoff(
                    linear_certificate,
                    definition_name="exampleLinearDecompositionHandoff",
                )
            )
            linear_wrapper_result = subprocess.run(
                [*lake, str(linear_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                linear_wrapper_result.returncode,
                0,
                linear_wrapper_result.stderr
                or linear_wrapper_result.stdout,
            )

    def test_complete_mock_dft_model_l2_certificate_typechecks_with_lean(
        self,
    ) -> None:
        lake = lake_command()
        if lake is None:
            self.skipTest("lake is not available")

        with tempfile.TemporaryDirectory(
            prefix="TmpAnalyticDftModelL2", dir=PROJECT_ROOT
        ) as tmpdir:
            tmp_path = Path(tmpdir)
            mock_module = f"{tmp_path.name}.AnalyticMock"
            mock_path = tmp_path / "AnalyticMock.lean"
            mock_path.write_text(
                "\n".join(
                    [
                        "import Gdbh.DiscreteCircleMethod",
                        "",
                        "open scoped BigOperators",
                        "",
                        "namespace Gdbh",
                        "",
                        "noncomputable def exampleMajorArcs (n : Nat) : Finset (ZMod n.succ) := ∅",
                        "noncomputable def exampleMajorArcModelTerm (n : Nat) (_ : ZMod n.succ) : ℂ := 0",
                        "noncomputable def exampleMajorArcTermError (n : Nat) (_ : ZMod n.succ) : ℝ := 0",
                        "noncomputable def exampleMajorArcModelError (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMajorArcError (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMinorArcDftBound (n : Nat) (_ : ZMod n.succ) : ℝ := 0",
                        "noncomputable def exampleMinorArcUniformDftBound (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMinorArcFrequencyCountBound (_ : Nat) : ℝ := 0",
                        "noncomputable def exampleMinorArcError (_ : Nat) : ℝ := 0",
                        "",
                        "axiom example_major_arc_term_approximation_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ exampleMajorArcs n,",
                        "        ‖DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm n k -",
                        "            exampleMajorArcModelTerm n k‖ ≤",
                        "          exampleMajorArcTermError n k",
                        "",
                        "axiom example_major_arc_model_approximation_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ‖(∑ k ∈ exampleMajorArcs n,",
                        "          exampleMajorArcModelTerm n k) -",
                        "          (goldbachSingularSeriesFromQuarter n *",
                        "            (n : ℝ) : ℂ)‖ ≤",
                        "        exampleMajorArcModelError n",
                        "",
                        "axiom example_major_arc_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      (∑ k ∈ exampleMajorArcs n,",
                        "          exampleMajorArcTermError n k) +",
                        "        exampleMajorArcModelError n ≤",
                        "          exampleMajorArcError n",
                        "",
                        "axiom example_minor_arc_dft_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcDftBound n k",
                        "",
                        "axiom example_minor_arc_square_sum_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ‖((n.succ : ℂ)⁻¹)‖ *",
                        "        (∑ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "          exampleMinorArcDftBound n k ^ 2) ≤",
                        "        exampleMinorArcError n",
                        "",
                        "axiom example_minor_arc_uniform_dft_bound_nonneg :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      0 ≤ exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_minor_arc_uniform_dft_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_minor_arc_frequency_count_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n)).card : ℝ) ≤",
                        "        exampleMinorArcFrequencyCountBound n",
                        "",
                        "axiom example_minor_arc_square_sum_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMinorArcFrequencyCountBound n *",
                        "        (‖((n.succ : ℂ)⁻¹)‖ *",
                        "          exampleMinorArcUniformDftBound n ^ 2) ≤",
                        "          exampleMinorArcError n",
                        "",
                        "axiom example_minor_arc_dft_bound_sq_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMinorArcUniformDftBound n ^ 2 ≤",
                        "        exampleMinorArcError n",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_major_arc_linear_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) +",
                        "          exampleMinorArcError n ≤",
                        "        DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                        "          exampleMajorArcs n",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_minor_arc_uniform_dft_bound_nonneg :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      0 ≤ exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_minor_arc_uniform_dft_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_minor_arc_dft_bound_sq_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMinorArcUniformDftBound n ^ 2 ≤",
                        "        exampleMinorArcError n",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_dft_uniform_minor_sq_positive_linear_explicit_contamination_sqrt_log_model_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                        "          (Real.sqrt (n : ℝ) *",
                        "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_major_arc_linear_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 8) : ℝ) * (n : ℝ) +",
                        "          exampleMinorArcUniformDftBound n ^ 2 ≤",
                        "        DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                        "          exampleMajorArcs n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_minor_arc_uniform_dft_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_contamination_dominated :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      2 * vonMangoldtWeightSumContaminationBudget",
                        "        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_sqrt_log_model_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                        "          (Real.sqrt (n : ℝ) *",
                        "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_major_arc_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      (1 - ((1 / 2) : ℝ)) *",
                        "          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +",
                        "        exampleMinorArcUniformDftBound n ^ 2 ≤",
                        "          DiscreteCircleMethod.rawVonMangoldtFourierMajorArcContribution",
                        "            exampleMajorArcs n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_valid :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies",
                        "          (exampleMajorArcs n),",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_contamination_sqrt_log_model_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      vonMangoldtSqrtLogBudgetComparisonConstant *",
                        "          (Real.sqrt (n : ℝ) *",
                        "            Real.log (n : ℝ) ^ (3 : Nat)) <",
                        "        ((1 - ((1 / 2) : ℝ)) * (1 / 4 : ℝ)) *",
                        "          (n : ℝ)",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_off_major_arcs :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k : ZMod n.succ, k ∉ exampleMajorArcs n →",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_zero_frequency_mem_major_arcs :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      (0 : ZMod n.succ) ∈ exampleMajorArcs n",
                        "",
                        "axiom example_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_minor_arc_uniform_dft_bound_nonzero :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ∀ k : ZMod n.succ, k ≠ 0 →",
                        "        ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤",
                        "          exampleMinorArcUniformDftBound n",
                        "",
                        "axiom example_total_linear_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      exampleMajorArcError n +",
                        "          exampleMinorArcError n ≤",
                        "        ((1 / 8) : ℝ) * (n : ℝ)",
                        "",
                        "axiom example_dft_model_l2_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_dft_model_uniform_minor_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "axiom example_dft_model_uniform_minor_sq_contamination_threshold_bound :",
                        "    ∀ estimate :",
                        "      DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate,",
                        "      estimate.canonicalContaminationThreshold ≤ 100",
                        "",
                        "end Gdbh",
                        "",
                    ]
                )
            )
            env = os.environ.copy()
            existing_lean_path = env.get("LEAN_PATH")
            env["LEAN_PATH"] = (
                str(PROJECT_ROOT)
                if not existing_lean_path
                else f"{PROJECT_ROOT}{os.pathsep}{existing_lean_path}"
            )
            mock_result = subprocess.run(
                [*lake, "-o", str(tmp_path / "AnalyticMock.olean"), str(mock_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                mock_result.returncode,
                0,
                mock_result.stderr or mock_result.stdout,
            )

            certificate = dft_model_l2_structured_final_certificate()
            certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            probe_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                probe_result.returncode,
                0,
                probe_result.stderr or probe_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleDftModelL2Handoff",
            )
            self.assertEqual(
                handoff_result.returncode,
                0,
                handoff_result.stderr or handoff_result.stdout,
            )

            wrapper_path = tmp_path / "GeneratedDftModelL2Handoff.lean"
            wrapper_path.write_text(
                render_lean_handoff(
                    certificate,
                    definition_name="exampleDftModelL2Handoff",
                )
            )
            wrapper_result = subprocess.run(
                [*lake, str(wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                wrapper_result.returncode,
                0,
                wrapper_result.stderr or wrapper_result.stdout,
            )

            uniform_certificate = (
                dft_model_uniform_minor_structured_final_certificate()
            )
            uniform_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            uniform_probe_result = check_lean_obligations(
                uniform_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                uniform_probe_result.returncode,
                0,
                uniform_probe_result.stderr or uniform_probe_result.stdout,
            )

            uniform_handoff_result = check_lean_handoff(
                uniform_certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleDftModelUniformMinorHandoff",
            )
            self.assertEqual(
                uniform_handoff_result.returncode,
                0,
                uniform_handoff_result.stderr or uniform_handoff_result.stdout,
            )

            uniform_wrapper_path = (
                tmp_path / "GeneratedDftModelUniformMinorHandoff.lean"
            )
            uniform_wrapper_path.write_text(
                render_lean_handoff(
                    uniform_certificate,
                    definition_name="exampleDftModelUniformMinorHandoff",
                )
            )
            uniform_wrapper_result = subprocess.run(
                [*lake, str(uniform_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                uniform_wrapper_result.returncode,
                0,
                uniform_wrapper_result.stderr or uniform_wrapper_result.stdout,
            )

            uniform_sq_certificate = (
                dft_model_uniform_minor_sq_structured_final_certificate()
            )
            uniform_sq_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            uniform_sq_probe_result = check_lean_obligations(
                uniform_sq_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                uniform_sq_probe_result.returncode,
                0,
                uniform_sq_probe_result.stderr
                or uniform_sq_probe_result.stdout,
            )

            uniform_sq_handoff_result = check_lean_handoff(
                uniform_sq_certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleDftModelUniformMinorSqHandoff",
            )
            self.assertEqual(
                uniform_sq_handoff_result.returncode,
                0,
                uniform_sq_handoff_result.stderr
                or uniform_sq_handoff_result.stdout,
            )

            uniform_sq_wrapper_path = (
                tmp_path / "GeneratedDftModelUniformMinorSqHandoff.lean"
            )
            uniform_sq_wrapper_path.write_text(
                render_lean_handoff(
                    uniform_sq_certificate,
                    definition_name="exampleDftModelUniformMinorSqHandoff",
                )
            )
            uniform_sq_wrapper_result = subprocess.run(
                [*lake, str(uniform_sq_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                uniform_sq_wrapper_result.returncode,
                0,
                uniform_sq_wrapper_result.stderr
                or uniform_sq_wrapper_result.stdout,
            )

            positive_linear_explicit_certificate = (
                dft_uniform_minor_sq_positive_linear_explicit_contamination_formalized_certificate()
            )
            positive_linear_explicit_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            positive_linear_explicit_probe_result = check_lean_obligations(
                positive_linear_explicit_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                positive_linear_explicit_probe_result.returncode,
                0,
                positive_linear_explicit_probe_result.stderr
                or positive_linear_explicit_probe_result.stdout,
            )

            positive_linear_explicit_handoff_result = check_lean_handoff(
                positive_linear_explicit_certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleDftUniformMinorSqPositiveLinearExplicitContaminationHandoff"
                ),
            )
            self.assertEqual(
                positive_linear_explicit_handoff_result.returncode,
                0,
                positive_linear_explicit_handoff_result.stderr
                or positive_linear_explicit_handoff_result.stdout,
            )

            positive_linear_explicit_wrapper_path = (
                tmp_path
                / "GeneratedDftUniformMinorSqPositiveLinearExplicitContaminationHandoff.lean"
            )
            positive_linear_explicit_wrapper_path.write_text(
                render_lean_handoff(
                    positive_linear_explicit_certificate,
                    definition_name=(
                        "exampleDftUniformMinorSqPositiveLinearExplicitContaminationHandoff"
                    ),
                )
            )
            positive_linear_explicit_wrapper_result = subprocess.run(
                [*lake, str(positive_linear_explicit_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                positive_linear_explicit_wrapper_result.returncode,
                0,
                positive_linear_explicit_wrapper_result.stderr
                or positive_linear_explicit_wrapper_result.stdout,
            )

            derived_positive_linear_certificate = (
                dft_uniform_minor_sq_positive_linear_explicit_contamination_with_derived_model_certificate()
            )
            derived_positive_linear_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            derived_positive_linear_probe_result = check_lean_obligations(
                derived_positive_linear_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                derived_positive_linear_probe_result.returncode,
                0,
                derived_positive_linear_probe_result.stderr
                or derived_positive_linear_probe_result.stdout,
            )

            derived_positive_linear_handoff_result = check_lean_handoff(
                derived_positive_linear_certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleDftUniformMinorSqPositiveLinearDerivedContaminationHandoff"
                ),
            )
            self.assertEqual(
                derived_positive_linear_handoff_result.returncode,
                0,
                derived_positive_linear_handoff_result.stderr
                or derived_positive_linear_handoff_result.stdout,
            )

            fixed_error_positive_linear_certificate = (
                dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_formalized_certificate()
            )
            fixed_error_positive_linear_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            fixed_error_positive_linear_probe_result = check_lean_obligations(
                fixed_error_positive_linear_certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                fixed_error_positive_linear_probe_result.returncode,
                0,
                fixed_error_positive_linear_probe_result.stderr
                or fixed_error_positive_linear_probe_result.stdout,
            )

            fixed_error_positive_linear_handoff_result = check_lean_handoff(
                fixed_error_positive_linear_certificate,
                workdir=PROJECT_ROOT,
                definition_name=(
                    "exampleDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff"
                ),
            )
            self.assertEqual(
                fixed_error_positive_linear_handoff_result.returncode,
                0,
                fixed_error_positive_linear_handoff_result.stderr
                or fixed_error_positive_linear_handoff_result.stdout,
            )

            fixed_error_positive_linear_wrapper_path = (
                tmp_path
                / "GeneratedDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff.lean"
            )
            fixed_error_positive_linear_wrapper_path.write_text(
                render_lean_handoff(
                    fixed_error_positive_linear_certificate,
                    definition_name=(
                        "exampleDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationHandoff"
                    ),
                )
            )
            fixed_error_positive_linear_wrapper_result = subprocess.run(
                [*lake, str(fixed_error_positive_linear_wrapper_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                fixed_error_positive_linear_wrapper_result.returncode,
                0,
                fixed_error_positive_linear_wrapper_result.stderr
                or fixed_error_positive_linear_wrapper_result.stdout,
            )

            derived_fixed_error_positive_linear_certificate = (
                dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_with_derived_model_certificate()
            )
            derived_fixed_error_positive_linear_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            derived_fixed_error_positive_linear_probe_result = (
                check_lean_obligations(
                    derived_fixed_error_positive_linear_certificate,
                    workdir=PROJECT_ROOT,
                )
            )
            self.assertEqual(
                derived_fixed_error_positive_linear_probe_result.returncode,
                0,
                derived_fixed_error_positive_linear_probe_result.stderr
                or derived_fixed_error_positive_linear_probe_result.stdout,
            )

            derived_fixed_error_positive_linear_handoff_result = (
                check_lean_handoff(
                    derived_fixed_error_positive_linear_certificate,
                    workdir=PROJECT_ROOT,
                    definition_name=(
                        "exampleDftUniformMinorSqFixedErrorPositiveLinearDerivedContaminationHandoff"
                    ),
                )
            )
            self.assertEqual(
                derived_fixed_error_positive_linear_handoff_result.returncode,
                0,
                derived_fixed_error_positive_linear_handoff_result.stderr
                or derived_fixed_error_positive_linear_handoff_result.stdout,
            )

            fixed_error_quarter_sqrt_log_certificate = (
                dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_formalized_certificate()
            )
            fixed_error_quarter_sqrt_log_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            fixed_error_quarter_sqrt_log_probe_result = (
                check_lean_obligations(
                    fixed_error_quarter_sqrt_log_certificate,
                    workdir=PROJECT_ROOT,
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_probe_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_probe_result.stderr
                or fixed_error_quarter_sqrt_log_probe_result.stdout,
            )

            fixed_error_quarter_sqrt_log_handoff_result = (
                check_lean_handoff(
                    fixed_error_quarter_sqrt_log_certificate,
                    workdir=PROJECT_ROOT,
                    definition_name=(
                        "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationHandoff"
                    ),
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_handoff_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_handoff_result.stderr
                or fixed_error_quarter_sqrt_log_handoff_result.stdout,
            )

            fixed_error_quarter_sqrt_log_off_major_certificate = (
                dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_off_major_minor_certificate()
            )
            fixed_error_quarter_sqrt_log_off_major_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            fixed_error_quarter_sqrt_log_off_major_probe_result = (
                check_lean_obligations(
                    fixed_error_quarter_sqrt_log_off_major_certificate,
                    workdir=PROJECT_ROOT,
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_off_major_probe_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_off_major_probe_result.stderr
                or fixed_error_quarter_sqrt_log_off_major_probe_result.stdout,
            )

            fixed_error_quarter_sqrt_log_off_major_handoff_result = (
                check_lean_handoff(
                    fixed_error_quarter_sqrt_log_off_major_certificate,
                    workdir=PROJECT_ROOT,
                    definition_name=(
                        "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogOffMajorMinorHandoff"
                    ),
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_off_major_handoff_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_off_major_handoff_result.stderr
                or fixed_error_quarter_sqrt_log_off_major_handoff_result.stdout,
            )

            fixed_error_quarter_sqrt_log_nonzero_certificate = (
                dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_with_nonzero_minor_certificate()
            )
            fixed_error_quarter_sqrt_log_nonzero_certificate["imports"] = [
                "Gdbh.VonMangoldtGoldbach",
                "Gdbh.DiscreteCircleMethod",
                mock_module,
            ]

            fixed_error_quarter_sqrt_log_nonzero_probe_result = (
                check_lean_obligations(
                    fixed_error_quarter_sqrt_log_nonzero_certificate,
                    workdir=PROJECT_ROOT,
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_nonzero_probe_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_nonzero_probe_result.stderr
                or fixed_error_quarter_sqrt_log_nonzero_probe_result.stdout,
            )

            fixed_error_quarter_sqrt_log_nonzero_handoff_result = (
                check_lean_handoff(
                    fixed_error_quarter_sqrt_log_nonzero_certificate,
                    workdir=PROJECT_ROOT,
                    definition_name=(
                        "exampleDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogNonzeroMinorHandoff"
                    ),
                )
            )
            self.assertEqual(
                fixed_error_quarter_sqrt_log_nonzero_handoff_result.returncode,
                0,
                fixed_error_quarter_sqrt_log_nonzero_handoff_result.stderr
                or fixed_error_quarter_sqrt_log_nonzero_handoff_result.stdout,
            )

    def test_complete_mock_canonical_handoff_check_rejects_bad_threshold_term(
        self,
    ) -> None:
        lake = lake_command()
        if lake is None:
            self.skipTest("lake is not available")

        with tempfile.TemporaryDirectory(
            prefix="TmpAnalyticCanonicalBad", dir=PROJECT_ROOT
        ) as tmpdir:
            tmp_path = Path(tmpdir)
            mock_module = f"{tmp_path.name}.AnalyticMock"
            mock_path = tmp_path / "AnalyticMock.lean"
            mock_path.write_text(
                "\n".join(
                    [
                        "import Gdbh.VonMangoldtGoldbach",
                        "",
                        "namespace Gdbh",
                        "",
                        "noncomputable def exampleSingularSeries (_ : Nat) : ℝ := 1",
                        "",
                        "axiom example_singular_series_lower_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      ((1 / 4) : ℝ) ≤ exampleSingularSeries n",
                        "",
                        "axiom example_raw_normalized_error_bound :",
                        "    ∀ n : Nat, 100 < n → Even n →",
                        "      |(RawVonMangoldtGoldbachSum n -",
                        "          exampleSingularSeries n * (n : ℝ)) /",
                        "        (exampleSingularSeries n * (n : ℝ))| ≤",
                        "        ((1 / 2) : ℝ)",
                        "",
                        "end Gdbh",
                        "",
                    ]
                )
            )
            env = os.environ.copy()
            existing_lean_path = env.get("LEAN_PATH")
            env["LEAN_PATH"] = (
                str(PROJECT_ROOT)
                if not existing_lean_path
                else f"{PROJECT_ROOT}{os.pathsep}{existing_lean_path}"
            )
            mock_result = subprocess.run(
                [*lake, "-o", str(tmp_path / "AnalyticMock.olean"), str(mock_path)],
                cwd=PROJECT_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                mock_result.returncode,
                0,
                mock_result.stderr or mock_result.stdout,
            )

            certificate = canonical_final_certificate()
            certificate["imports"] = ["Gdbh.VonMangoldtGoldbach", mock_module]
            threshold_bound = certificate["derivedThresholdBound"]
            assert isinstance(threshold_bound, dict)
            threshold_bound["lean_term"] = "Gdbh.missing_threshold_bound"

            obligation_result = check_lean_obligations(
                certificate, workdir=PROJECT_ROOT
            )
            self.assertEqual(
                obligation_result.returncode,
                0,
                obligation_result.stderr or obligation_result.stdout,
            )

            handoff_result = check_lean_handoff(
                certificate,
                workdir=PROJECT_ROOT,
                definition_name="exampleCanonicalHandoff",
            )
            self.assertNotEqual(handoff_result.returncode, 0)
            self.assertIn(
                "missing_threshold_bound",
                handoff_result.stderr or handoff_result.stdout,
            )


if __name__ == "__main__":
    unittest.main()
