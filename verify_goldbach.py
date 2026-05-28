#!/usr/bin/env python3
"""Finite verifier for the strong Goldbach conjecture.

This script checks even numbers up to a user-provided bound. It is not a
proof of the conjecture, because it only covers a finite interval.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Witness:
    even: int
    left: int
    right: int


def build_prime_sieve(limit: int) -> bytearray:
    """Return a bytearray where sieve[n] is true exactly when n is prime."""
    if limit < 0:
        raise ValueError("limit must be non-negative")

    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0

    for candidate in range(2, math.isqrt(limit) + 1):
        if sieve[candidate]:
            start = candidate * candidate
            step = candidate
            sieve[start : limit + 1 : step] = b"\x00" * (
                ((limit - start) // step) + 1
            )
    return sieve


def primes_from_sieve(sieve: bytearray) -> list[int]:
    return [value for value, is_prime in enumerate(sieve) if is_prime]


def find_witness(even: int, primes: list[int], sieve: bytearray) -> Witness | None:
    for prime in primes:
        if prime > even // 2:
            return None
        other = even - prime
        if sieve[other]:
            return Witness(even=even, left=prime, right=other)
    return None


def witnesses_up_to(limit: int) -> list[Witness]:
    if limit < 4:
        raise ValueError("limit must be at least 4")

    return witnesses_between(2, limit)


def witnesses_between(lower: int, limit: int) -> list[Witness]:
    if lower < 2:
        raise ValueError("lower bound must be at least 2")
    if limit <= lower:
        raise ValueError("limit must be greater than the lower bound")

    sieve = build_prime_sieve(limit)
    primes = primes_from_sieve(sieve)
    witnesses: list[Witness] = []
    first_even = lower + 1 if (lower + 1) % 2 == 0 else lower + 2

    for even in range(first_even, limit + 1, 2):
        witness = find_witness(even, primes, sieve)
        if witness is None:
            raise RuntimeError(f"counterexample candidate found: {even}")
        witnesses.append(witness)

    return witnesses


def export_witnesses_csv(limit: int, output_path: Path) -> None:
    witnesses = witnesses_up_to(limit)
    write_witnesses_csv(witnesses, output_path)


def export_interval_witnesses_csv(
    lower: int, limit: int, output_path: Path
) -> None:
    witnesses = witnesses_between(lower, limit)
    write_witnesses_csv(witnesses, output_path)


def write_witnesses_csv(witnesses: list[Witness], output_path: Path) -> None:
    with output_path.open("w", newline="") as output_file:
        writer = csv.writer(output_file)
        writer.writerow(["even", "left", "right"])
        for witness in witnesses:
            writer.writerow([witness.even, witness.left, witness.right])


def interval_certificate_name(lower: int, limit: int) -> str:
    return f"certificate{lower}To{limit}"


def interval_theorem_suffix(lower: int, limit: int) -> str:
    return f"{lower}To{limit}"


def chunk_intervals(lower: int, limit: int, chunk_size: int) -> list[tuple[int, int]]:
    if chunk_size <= 0:
        raise ValueError("chunk size must be positive")
    if limit <= lower:
        raise ValueError("limit must be greater than the lower bound")

    chunks: list[tuple[int, int]] = []
    start = lower
    while start < limit:
        end = min(start + chunk_size, limit)
        chunks.append((start, end))
        start = end
    return chunks


def render_lean_certificate(limit: int) -> str:
    witnesses = witnesses_up_to(limit)
    certificate_name = f"certificate{limit}"

    lines = [
        "import Gdbh.CircleMethod",
        "",
        "set_option maxRecDepth 200000",
        "",
        "namespace Gdbh",
        "",
        f"def {certificate_name}Verified : List VerifiedCertificateEntry :=",
        "  [",
    ]

    for index, witness in enumerate(witnesses):
        prefix = "    " if index == 0 else "    "
        comma = "," if index < len(witnesses) - 1 else ""
        lines.extend(
            [
                f"{prefix}{{ entry := {{ n := {witness.even}, "
                f"p := {witness.left}, q := {witness.right} }},",
                f"      valid := by norm_num [CertificateEntry.Valid] }}{comma}",
            ]
        )

    lines.extend(
        [
            "  ]",
            "",
            f"def {certificate_name} : List CertificateEntry :=",
            f"  verifiedCertificateEntries {certificate_name}Verified",
            "",
            f"theorem {certificate_name}_covers : "
            f"CertificateCovers {limit} {certificate_name} :=",
            "  certificateCovers_of_verified_list_check",
            "    (by",
            "      unfold VerifiedCertificateCoversListCheck",
            "        VerifiedCertificateHasEntryCheck",
            "      rfl)",
        ]
    )

    lines.extend(
        [
            "",
            f"theorem goldbachUpTo{limit} : GoldbachUpTo {limit} :=",
            f"  goldbachUpTo_of_certificate {certificate_name}_covers",
            "",
            f"theorem strongGoldbach_from_certificate{limit}_and_analytic_bridge",
            f"    (analytic_goldbach_above_{limit} : GoldbachAbove {limit}) :",
            "    StrongGoldbach :=",
            f"  strongGoldbach_of_finite_and_above goldbachUpTo{limit} "
            f"analytic_goldbach_above_{limit}",
            "",
            f"theorem strongGoldbach_iff_goldbachAbove{limit} :",
            f"    StrongGoldbach ↔ GoldbachAbove {limit} := by",
            "  constructor",
            "  · intro strong",
            "    exact goldbachAbove_of_strongGoldbach (by decide) strong",
            f"  · intro above",
            f"    exact strongGoldbach_from_certificate{limit}_and_analytic_bridge above",
            "",
            f"theorem strongGoldbach_from_certificate{limit}_and_count_positive_bridge",
            f"    (count_positive_above_{limit} : GoldbachCountPositiveAbove {limit}) :",
            "    StrongGoldbach :=",
            f"  strongGoldbach_from_certificate{limit}_and_analytic_bridge",
            f"    (goldbachAbove_of_count_positive_above count_positive_above_{limit})",
            "",
            f"theorem strongGoldbach_iff_count_positive_above{limit} :",
            f"    StrongGoldbach ↔ GoldbachCountPositiveAbove {limit} := by",
            "  constructor",
            "  · intro strong",
            f"    exact goldbachCountPositiveAbove_iff_goldbachAbove.mpr",
            f"      (strongGoldbach_iff_goldbachAbove{limit}.mp strong)",
            "  · intro count_positive",
            f"    exact strongGoldbach_iff_goldbachAbove{limit}.mpr",
            f"      (goldbachCountPositiveAbove_iff_goldbachAbove.mp count_positive)",
            "",
            f"theorem strongGoldbach_from_certificate{limit}_and_circle_method",
            "    (bound : CircleMethodLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach := by",
            f"  exact strongGoldbach_from_certificate{limit}_and_count_positive_bridge",
            f"    (goldbachCountPositiveAbove_mono hthreshold",
            "      (count_positive_of_circle_method_lower_bound bound))",
            "",
            "end Gdbh",
            "",
        ]
    )
    return "\n".join(lines)


def render_lean_interval_block(lower: int, limit: int) -> list[str]:
    witnesses = witnesses_between(lower, limit)
    certificate_name = interval_certificate_name(lower, limit)
    suffix = interval_theorem_suffix(lower, limit)

    lines = [
        f"def {certificate_name}Verified : List VerifiedCertificateEntry :=",
        "  [",
    ]

    for index, witness in enumerate(witnesses):
        comma = "," if index < len(witnesses) - 1 else ""
        lines.extend(
            [
                f"    {{ entry := {{ n := {witness.even}, "
                f"p := {witness.left}, q := {witness.right} }},",
                f"      valid := by norm_num [CertificateEntry.Valid] }}{comma}",
            ]
        )

    lines.extend(
        [
            "  ]",
            "",
            f"def {certificate_name} : List CertificateEntry :=",
            f"  verifiedCertificateEntries {certificate_name}Verified",
            "",
            f"theorem {certificate_name}_covers :",
            f"    CertificateCoversBetween {lower} {limit} {certificate_name} :=",
            "  certificateCoversBetween_of_verified_list_check",
            "    (by",
            "      unfold VerifiedCertificateCoversBetweenListCheck",
            "        VerifiedCertificateHasEntryCheck",
            "      rfl)",
        ]
    )

    lines.extend(
        [
            "",
            f"theorem goldbachBetween{suffix} :",
            f"    GoldbachBetween {lower} {limit} :=",
            f"  goldbachBetween_of_certificate {certificate_name}_covers",
            "",
        ]
    )
    return lines


def render_lean_interval_certificate(lower: int, limit: int) -> str:
    certificate_name = interval_certificate_name(lower, limit)
    suffix = interval_theorem_suffix(lower, limit)
    lines = [
        "import Gdbh.FiniteIntervals",
    ]
    if lower == 2:
        lines.append("import Gdbh.GeneralHandoff")
        lines.append("import Gdbh.ContaminatedWeightedGoldbach")
        lines.append("import Gdbh.RealContaminatedWeightedGoldbach")
        lines.append("import Gdbh.VonMangoldtGoldbach")
    lines.extend(["", "set_option maxRecDepth 200000", "", "namespace Gdbh", ""])
    lines.extend(render_lean_interval_block(lower, limit))
    lines.extend(
        render_interval_upgrade_lines(
            lower,
            limit,
            certificate_name,
            suffix,
            is_chunked=False,
        )
    )
    return "\n".join(lines)


def render_interval_upgrade_lines(
    lower: int,
    limit: int,
    certificate_name: str,
    suffix: str,
    *,
    is_chunked: bool,
) -> list[str]:
    theorem_tag = (
        f"chunkedCertificate{suffix}" if is_chunked else certificate_name
    )
    if lower == 2:
        theorem_name = f"goldbachUpTo{limit}_of_{theorem_tag}"
        return [
            f"theorem {theorem_name} :",
            f"    GoldbachUpTo {limit} :=",
            f"  goldbachUpTo_of_between_two goldbachBetween{suffix}",
            "",
            f"theorem explicitLowerBound100_from_{theorem_tag}_and_explicit_lower_bound",
            "    {T : Nat}",
            f"    (hthreshold : T ≤ {limit})",
            "    (lower_bound : ExplicitGoldbachLowerBound T) :",
            "    ExplicitGoldbachLowerBound 100 :=",
            "  explicit_lower_bound100_of_finite_and_explicit_lower_bound_le",
            f"    {theorem_name} hthreshold lower_bound",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_explicit_lower_bound",
            "    {T : Nat}",
            f"    (hthreshold : T ≤ {limit})",
            "    (lower_bound : ExplicitGoldbachLowerBound T) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_explicit_lower_bound_le",
            f"    {theorem_name} hthreshold lower_bound",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_circle_method_lower_bound",
            "    (bound : CircleMethodLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_circle_method_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_major_minor_arc_estimate",
            "    (estimate : MajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_count_positive_above",
            "    {T : Nat}",
            f"    (hthreshold : T ≤ {limit})",
            "    (count_positive : GoldbachCountPositiveAbove T) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_count_positive_above_le",
            f"    {theorem_name} hthreshold count_positive",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_weighted_lower_bound",
            "    (bound : WeightedGoldbachLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_weighted_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_weighted_major_minor_arc_estimate",
            "    (estimate : WeightedMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_weighted_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_contaminated_weighted_lower_bound",
            "    (bound : ContaminatedWeightedGoldbachLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_contaminated_weighted_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_contaminated_weighted_major_minor_arc_estimate",
            "    (estimate : ContaminatedWeightedMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_contaminated_weighted_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_real_contaminated_weighted_lower_bound",
            "    (bound : RealContaminatedWeightedGoldbachLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_real_contaminated_weighted_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_real_contaminated_weighted_major_minor_arc_estimate",
            "    (estimate : RealContaminatedWeightedMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_real_contaminated_weighted_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_lower_bound",
            "    (bound : VonMangoldtGoldbachLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_major_minor_arc_estimate",
            "    (estimate : VonMangoldtMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_prime_power_contamination_lower_bound",
            "    (bound : VonMangoldtPrimePowerContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_prime_power_contamination_lower_bound",
            "    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_pointwise_split_contamination_lower_bound",
            "    (bound : VonMangoldtPointwiseSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_uniform_split_contamination_lower_bound",
            "    (bound : VonMangoldtUniformSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_counted_split_contamination_lower_bound",
            "    (bound : VonMangoldtCountedSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_trivial_count_split_contamination_lower_bound",
            "    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_weight_bound_split_contamination_lower_bound",
            "    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_log_weight_split_contamination_lower_bound",
            "    (bound : VonMangoldtLogWeightSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound",
            "    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_canonical_log_count_contamination_lower_bound",
            "    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_direct_raw_log_count_lower_bound",
            "    (bound : VonMangoldtDirectRawLogCountLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_count_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_direct_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtDirectRawWeightSumLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound",
            "    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound)",
            f"    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_sqrt_log_count_raw_lower_bound",
            "    (bound : VonMangoldtSqrtLogCountRawLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound",
            "    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound",
            "    (bound : VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)",
            f"    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate",
            "    (estimate : VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)",
            f"    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_hardy_littlewood_normalized_estimate",
            "    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)",
            f"    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate",
            "    (estimate : VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate",
            "    (estimate : VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate",
            "    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate",
            "    (estimate : VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate",
            "    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_canonical_log_contamination_lower_bound",
            "    (bound : VonMangoldtCanonicalLogContaminationLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate",
            "    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate)",
            f"    (hthreshold : estimate.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate_le",
            f"    {theorem_name} estimate hthreshold",
            "",
            f"theorem strongGoldbach_from_{theorem_tag}_and_vonMangoldt_direct_raw_log_lower_bound",
            "    (bound : VonMangoldtDirectRawLogLowerBound)",
            f"    (hthreshold : bound.threshold ≤ {limit}) :",
            "    StrongGoldbach :=",
            "  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_lower_bound_le",
            f"    {theorem_name} bound hthreshold",
            "",
            "end Gdbh",
            "",
        ]

    theorem_name = f"goldbachUpTo{limit}_of_goldbachUpTo{lower}_and_{theorem_tag}"
    return [
        f"theorem {theorem_name}",
        f"    (upTo_lower : GoldbachUpTo {lower}) :",
        f"    GoldbachUpTo {limit} :=",
        f"  goldbachUpTo_of_upTo_and_between upTo_lower goldbachBetween{suffix}",
        "",
        "end Gdbh",
        "",
    ]


def render_lean_chunked_interval_certificate(
    lower: int, limit: int, chunk_size: int
) -> str:
    chunks = chunk_intervals(lower, limit, chunk_size)
    final_suffix = interval_theorem_suffix(lower, limit)
    lines = [
        "import Gdbh.FiniteIntervals",
    ]
    if lower == 2:
        lines.append("import Gdbh.GeneralHandoff")
        lines.append("import Gdbh.ContaminatedWeightedGoldbach")
        lines.append("import Gdbh.RealContaminatedWeightedGoldbach")
        lines.append("import Gdbh.VonMangoldtGoldbach")
    lines.extend(["", "set_option maxRecDepth 200000", "", "namespace Gdbh", ""])

    for chunk_lower, chunk_limit in chunks:
        lines.extend(render_lean_interval_block(chunk_lower, chunk_limit))

    def render_balanced_between(
        intervals: list[tuple[int, int]],
    ) -> tuple[int, int]:
        if len(intervals) == 1:
            return intervals[0]

        midpoint = len(intervals) // 2
        left_lower, left_upper = render_balanced_between(intervals[:midpoint])
        right_lower, right_upper = render_balanced_between(intervals[midpoint:])
        combined_suffix = interval_theorem_suffix(left_lower, right_upper)
        lines.extend(
            [
                f"theorem goldbachBetween{combined_suffix} :",
                f"    GoldbachBetween {left_lower} {right_upper} :=",
                "  goldbachBetween_of_between_and_between",
                f"    goldbachBetween{interval_theorem_suffix(left_lower, left_upper)}",
                f"    goldbachBetween{interval_theorem_suffix(right_lower, right_upper)}",
                "",
            ]
        )
        return left_lower, right_upper

    combined_lower, combined_upper = render_balanced_between(chunks)
    combined_suffix = interval_theorem_suffix(combined_lower, combined_upper)
    if combined_suffix != final_suffix:
        raise AssertionError("balanced chunk suffix should equal the final suffix")

    lines.extend(
        render_interval_upgrade_lines(
            lower,
            limit,
            certificate_name="",
            suffix=final_suffix,
            is_chunked=True,
        )
    )
    return "\n".join(lines)


def export_witnesses_lean(limit: int, output_path: Path) -> None:
    output_path.write_text(render_lean_certificate(limit))


def export_interval_witnesses_lean(
    lower: int, limit: int, output_path: Path
) -> None:
    output_path.write_text(render_lean_interval_certificate(lower, limit))


def export_chunked_interval_witnesses_lean(
    lower: int, limit: int, chunk_size: int, output_path: Path
) -> None:
    output_path.write_text(
        render_lean_chunked_interval_certificate(lower, limit, chunk_size)
    )


def build_certificate_manifest(
    limit: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> dict[str, object]:
    certificate_text = render_lean_certificate(limit)
    certificate_path_text = certificate_path.as_posix()
    manifest_path_text = manifest_path.as_posix()
    return {
        "bound": limit,
        "certificate": certificate_path_text,
        "generator": "verify_goldbach.py",
        "generator_command": (
            f"python3 verify_goldbach.py {limit} --export-lean "
            f"{certificate_path_text} --export-manifest {manifest_path_text}"
        ),
        "lean_theorem": f"Gdbh.goldbachUpTo{limit}",
        "sha256": hashlib.sha256(certificate_text.encode()).hexdigest(),
        "notes": (
            "Finite Lean-checked certificate only; this does not prove the "
            "strong Goldbach conjecture."
        ),
    }


def self_contained_strong_handoff_manifest(
    theorem_tag: str,
) -> dict[str, str]:
    theorem_prefix = f"Gdbh.strongGoldbach_from_{theorem_tag}_and"
    exact_prefix = f"Gdbh.explicitLowerBound100_from_{theorem_tag}_and"
    return {
        "lean_explicit_lower_bound100_explicit_lower_bound_theorem": (
            f"{exact_prefix}_explicit_lower_bound"
        ),
        "lean_strong_explicit_lower_bound_theorem": (
            f"{theorem_prefix}_explicit_lower_bound"
        ),
        "lean_strong_circle_method_theorem": (
            f"{theorem_prefix}_circle_method_lower_bound"
        ),
        "lean_strong_major_minor_arc_theorem": (
            f"{theorem_prefix}_major_minor_arc_estimate"
        ),
        "lean_strong_count_theorem": f"{theorem_prefix}_count_positive_above",
        "lean_strong_weighted_lower_bound_theorem": (
            f"{theorem_prefix}_weighted_lower_bound"
        ),
        "lean_strong_weighted_major_minor_theorem": (
            f"{theorem_prefix}_weighted_major_minor_arc_estimate"
        ),
        "lean_strong_contaminated_weighted_lower_bound_theorem": (
            f"{theorem_prefix}_contaminated_weighted_lower_bound"
        ),
        "lean_strong_contaminated_weighted_major_minor_theorem": (
            f"{theorem_prefix}_contaminated_weighted_major_minor_arc_estimate"
        ),
        "lean_strong_real_contaminated_weighted_lower_bound_theorem": (
            f"{theorem_prefix}_real_contaminated_weighted_lower_bound"
        ),
        "lean_strong_real_contaminated_weighted_major_minor_theorem": (
            f"{theorem_prefix}_real_contaminated_weighted_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_lower_bound"
        ),
        "lean_strong_vonMangoldt_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_prime_power_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_prime_power_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_prime_power_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_prime_power_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_prime_power_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_prime_power_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_split_prime_power_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_pointwise_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_pointwise_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_pointwise_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_uniform_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_uniform_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_uniform_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_counted_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_counted_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_counted_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_counted_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_trivial_count_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_trivial_count_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_trivial_count_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_weight_bound_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_weight_bound_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_weight_bound_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_log_weight_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_log_weight_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_log_weight_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_canonical_log_count_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_canonical_log_count_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_canonical_log_count_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_direct_raw_log_count_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_direct_raw_log_count_lower_bound"
        ),
        "lean_strong_vonMangoldt_direct_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_direct_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_positive_linear_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_relative_error_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_eventually_relative_error_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound"
        ),
        "lean_strong_vonMangoldt_direct_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_direct_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_threshold_direct_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_eventually_direct_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_sqrt_log_count_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_sqrt_log_count_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_sqrt_log_count_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound"
        ),
        "lean_strong_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_hardy_littlewood_normalized_estimate"
        ),
        "lean_strong_vonMangoldt_hardy_littlewood_normalized_estimate_theorem": (
            f"{theorem_prefix}_vonMangoldt_hardy_littlewood_normalized_estimate"
        ),
        "lean_strong_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_theorem": (
            f"{theorem_prefix}_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate"
        ),
        "lean_strong_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_theorem": (
            f"{theorem_prefix}_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate"
        ),
        "lean_strong_vonMangoldt_eventually_positive_linear_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_sqrt_log_count_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_sqrt_log_count_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_canonical_log_contamination_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_canonical_log_contamination_lower_bound"
        ),
        "lean_strong_vonMangoldt_canonical_log_contamination_major_minor_theorem": (
            f"{theorem_prefix}_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate"
        ),
        "lean_strong_vonMangoldt_direct_raw_log_lower_bound_theorem": (
            f"{theorem_prefix}_vonMangoldt_direct_raw_log_lower_bound"
        ),
    }


def build_interval_certificate_manifest(
    lower: int,
    limit: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> dict[str, object]:
    certificate_text = render_lean_interval_certificate(lower, limit)
    certificate_path_text = certificate_path.as_posix()
    manifest_path_text = manifest_path.as_posix()
    suffix = interval_theorem_suffix(lower, limit)
    certificate_name = interval_certificate_name(lower, limit)
    if lower == 2:
        lean_upgrade_theorem = f"Gdbh.goldbachUpTo{limit}_of_{certificate_name}"
    else:
        lean_upgrade_theorem = (
            f"Gdbh.goldbachUpTo{limit}_of_goldbachUpTo{lower}_and_"
            f"{certificate_name}"
        )
    manifest = {
        "lower_bound": lower,
        "bound": limit,
        "certificate": certificate_path_text,
        "generator": "verify_goldbach.py",
        "generator_command": (
            f"python3 verify_goldbach.py {limit} --interval-start {lower} "
            f"--export-lean {certificate_path_text} "
            f"--export-manifest {manifest_path_text}"
        ),
        "lean_theorem": f"Gdbh.goldbachBetween{suffix}",
        "lean_upgrade_theorem": lean_upgrade_theorem,
        "sha256": hashlib.sha256(certificate_text.encode()).hexdigest(),
        "notes": (
            "Finite Lean-checked interval certificate only; this does not "
            "prove the strong Goldbach conjecture."
        ),
    }
    if lower == 2:
        manifest.update(self_contained_strong_handoff_manifest(certificate_name))
    return manifest


def build_chunked_interval_certificate_manifest(
    lower: int,
    limit: int,
    chunk_size: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> dict[str, object]:
    certificate_text = render_lean_chunked_interval_certificate(
        lower, limit, chunk_size
    )
    certificate_path_text = certificate_path.as_posix()
    manifest_path_text = manifest_path.as_posix()
    suffix = interval_theorem_suffix(lower, limit)
    if lower == 2:
        lean_upgrade_theorem = (
            f"Gdbh.goldbachUpTo{limit}_of_chunkedCertificate{suffix}"
        )
    else:
        lean_upgrade_theorem = (
            f"Gdbh.goldbachUpTo{limit}_of_goldbachUpTo{lower}_and_"
            f"chunkedCertificate{suffix}"
        )
    manifest = {
        "lower_bound": lower,
        "bound": limit,
        "chunk_size": chunk_size,
        "certificate": certificate_path_text,
        "generator": "verify_goldbach.py",
        "generator_command": (
            f"python3 verify_goldbach.py {limit} --interval-start {lower} "
            f"--chunk-size {chunk_size} --export-lean {certificate_path_text} "
            f"--export-manifest {manifest_path_text}"
        ),
        "lean_theorem": f"Gdbh.goldbachBetween{suffix}",
        "lean_upgrade_theorem": lean_upgrade_theorem,
        "sha256": hashlib.sha256(certificate_text.encode()).hexdigest(),
        "notes": (
            "Finite Lean-checked chunked interval certificate only; this does "
            "not prove the strong Goldbach conjecture."
        ),
    }
    if lower == 2:
        manifest.update(
            self_contained_strong_handoff_manifest(
                f"chunkedCertificate{suffix}"
            )
        )
    return manifest


def render_certificate_manifest(
    limit: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> str:
    manifest = build_certificate_manifest(limit, certificate_path, manifest_path)
    return json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"


def render_interval_certificate_manifest(
    lower: int,
    limit: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> str:
    manifest = build_interval_certificate_manifest(
        lower, limit, certificate_path, manifest_path
    )
    return json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"


def render_chunked_interval_certificate_manifest(
    lower: int,
    limit: int,
    chunk_size: int,
    certificate_path: Path,
    manifest_path: Path = Path("certificate_manifest.json"),
) -> str:
    manifest = build_chunked_interval_certificate_manifest(
        lower, limit, chunk_size, certificate_path, manifest_path
    )
    return json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"


def export_certificate_manifest(
    limit: int, certificate_path: Path, manifest_path: Path
) -> None:
    manifest_path.write_text(
        render_certificate_manifest(limit, certificate_path, manifest_path)
    )


def export_interval_certificate_manifest(
    lower: int, limit: int, certificate_path: Path, manifest_path: Path
) -> None:
    manifest_path.write_text(
        render_interval_certificate_manifest(
            lower, limit, certificate_path, manifest_path
        )
    )


def export_chunked_interval_certificate_manifest(
    lower: int,
    limit: int,
    chunk_size: int,
    certificate_path: Path,
    manifest_path: Path,
) -> None:
    manifest_path.write_text(
        render_chunked_interval_certificate_manifest(
            lower, limit, chunk_size, certificate_path, manifest_path
        )
    )


def verify_up_to(limit: int, *, show_witnesses: bool = False) -> bool:
    try:
        witnesses = witnesses_up_to(limit)
    except RuntimeError as exc:
        print(str(exc))
        return False

    for witness in witnesses:
        if show_witnesses:
            print(f"{witness.even} = {witness.left} + {witness.right}")

    print(f"Verified every even number from 4 through {limit}.")
    print("This is finite verification, not a proof of the conjecture.")
    return True


def verify_between(
    lower: int, limit: int, *, show_witnesses: bool = False
) -> bool:
    try:
        witnesses = witnesses_between(lower, limit)
    except RuntimeError as exc:
        print(str(exc))
        return False

    for witness in witnesses:
        if show_witnesses:
            print(f"{witness.even} = {witness.left} + {witness.right}")

    print(f"Verified every even number n with {lower} < n <= {limit}.")
    print("This is finite verification, not a proof of the conjecture.")
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify strong Goldbach representations up to a finite bound."
    )
    parser.add_argument("limit", type=int, help="inclusive upper bound, at least 4")
    parser.add_argument(
        "--show-witnesses",
        action="store_true",
        help="print one prime-pair witness for every checked even number",
    )
    parser.add_argument(
        "--interval-start",
        type=int,
        help="verify and export only the interval interval_start < n <= limit",
    )
    parser.add_argument(
        "--chunk-size",
        type=int,
        help=(
            "with --interval-start, export the interval Lean certificate as "
            "multiple stitched chunks of this size"
        ),
    )
    parser.add_argument(
        "--export-csv",
        type=Path,
        help="write one prime-pair witness for every checked even number as CSV",
    )
    parser.add_argument(
        "--export-lean",
        type=Path,
        help="write a Lean module proving GoldbachUpTo for the finite interval",
    )
    parser.add_argument(
        "--export-manifest",
        type=Path,
        help="write manifest metadata for the Lean certificate",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        interval_start = args.interval_start
        if args.export_csv is not None:
            if interval_start is None:
                export_witnesses_csv(args.limit, args.export_csv)
            else:
                export_interval_witnesses_csv(
                    interval_start, args.limit, args.export_csv
                )
        if args.export_lean is not None:
            if interval_start is None:
                export_witnesses_lean(args.limit, args.export_lean)
            elif args.chunk_size is not None:
                export_chunked_interval_witnesses_lean(
                    interval_start,
                    args.limit,
                    args.chunk_size,
                    args.export_lean,
                )
            else:
                export_interval_witnesses_lean(
                    interval_start, args.limit, args.export_lean
                )
        if args.export_manifest is not None:
            if args.export_lean is None:
                raise ValueError("--export-manifest requires --export-lean")
            if interval_start is None:
                if args.chunk_size is not None:
                    raise ValueError("--chunk-size requires --interval-start")
                export_certificate_manifest(
                    args.limit, args.export_lean, args.export_manifest
                )
            elif args.chunk_size is not None:
                export_chunked_interval_certificate_manifest(
                    interval_start,
                    args.limit,
                    args.chunk_size,
                    args.export_lean,
                    args.export_manifest,
                )
            else:
                export_interval_certificate_manifest(
                    interval_start,
                    args.limit,
                    args.export_lean,
                    args.export_manifest,
                )
        if interval_start is None:
            ok = verify_up_to(args.limit, show_witnesses=args.show_witnesses)
        else:
            ok = verify_between(
                interval_start, args.limit, show_witnesses=args.show_witnesses
            )
    except ValueError as exc:
        print(f"error: {exc}")
        return 2
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
