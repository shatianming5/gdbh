#!/usr/bin/env python3
"""Finite exploratory data for the von Mangoldt Goldbach handoff.

This script does not prove Goldbach. It computes the finite raw Λ convolution
used by ``Gdbh.RawVonMangoldtGoldbachSum`` and compares it with the current
Lean-proved square-root/log contamination budget.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path

from verify_goldbach import build_prime_sieve, primes_from_sieve


@dataclass(frozen=True)
class VonMangoldtSample:
    even: int
    raw_sum: float
    raw_over_n: float
    singular_series_approx: float
    hl_main_term_approx: float
    raw_over_hl_main_approx: float
    hl_normalized_error_abs_approx: float
    prime_pair_sum: float
    prime_pair_over_n: float
    actual_contamination_sum: float
    actual_contamination_over_n: float
    doubled_contamination_budget: float
    doubled_contamination_over_n: float
    actual_contamination_over_doubled_budget: float
    raw_over_doubled_contamination: float
    non_prime_prime_power_weight_sum: float
    doubled_weight_sum_contamination_budget: float
    doubled_weight_sum_contamination_budget_over_n: float
    actual_contamination_over_doubled_weight_sum_budget: float
    raw_over_doubled_weight_sum_contamination: float
    raw_over_actual_contamination: float


@dataclass(frozen=True)
class VonMangoldtAnalysis:
    start: int
    limit: int
    samples: list[VonMangoldtSample]

    @property
    def min_raw_over_n(self) -> VonMangoldtSample:
        return min(self.samples, key=lambda sample: sample.raw_over_n)

    @property
    def min_raw_over_doubled_contamination(self) -> VonMangoldtSample:
        return min(
            self.samples,
            key=lambda sample: sample.raw_over_doubled_contamination,
        )

    @property
    def min_raw_over_doubled_weight_sum_contamination(
        self,
    ) -> VonMangoldtSample:
        return min(
            self.samples,
            key=lambda sample: sample.raw_over_doubled_weight_sum_contamination,
        )

    @property
    def max_doubled_contamination_over_n(self) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: sample.doubled_contamination_over_n,
        )

    @property
    def max_doubled_weight_sum_contamination_budget_over_n(
        self,
    ) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: sample.doubled_weight_sum_contamination_budget_over_n,
        )

    @property
    def min_prime_pair_over_n(self) -> VonMangoldtSample:
        return min(self.samples, key=lambda sample: sample.prime_pair_over_n)

    @property
    def min_singular_series_approx(self) -> VonMangoldtSample:
        return min(self.samples, key=lambda sample: sample.singular_series_approx)

    @property
    def max_hl_normalized_error_abs_approx(self) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: sample.hl_normalized_error_abs_approx,
        )

    @property
    def max_actual_contamination_over_n(self) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: sample.actual_contamination_over_n,
        )

    @property
    def max_actual_contamination_over_doubled_budget(
        self,
    ) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: sample.actual_contamination_over_doubled_budget,
        )

    @property
    def max_actual_contamination_over_doubled_weight_sum_budget(
        self,
    ) -> VonMangoldtSample:
        return max(
            self.samples,
            key=lambda sample: (
                sample.actual_contamination_over_doubled_weight_sum_budget
            ),
        )

    def finite_tail_threshold_for_raw_lower_bound(
        self, coefficient: float
    ) -> int | None:
        """Return first sampled even n after which raw_sum >= coefficient*n.

        The result is only a finite-range tail threshold inside this analysis
        window. ``None`` means even the last sampled point fails the predicate.
        """
        if coefficient <= 0:
            raise ValueError("coefficient must be positive")
        return finite_tail_threshold(
            self.samples,
            lambda sample: sample.raw_sum >= coefficient * sample.even,
        )

    def finite_tail_threshold_for_budget_domination(
        self, coefficient: float
    ) -> int | None:
        """Return first sampled even n after which budget < coefficient*n.

        The result is only a finite-range tail threshold inside this analysis
        window. ``None`` means even the last sampled point fails the predicate.
        """
        if coefficient <= 0:
            raise ValueError("coefficient must be positive")
        return finite_tail_threshold(
            self.samples,
            lambda sample: sample.doubled_contamination_budget
            < coefficient * sample.even,
        )

    def finite_tail_threshold_for_weight_sum_budget_domination(
        self, coefficient: float
    ) -> int | None:
        """Return first sampled even n after which weight-sum budget < c*n."""
        if coefficient <= 0:
            raise ValueError("coefficient must be positive")
        return finite_tail_threshold(
            self.samples,
            lambda sample: sample.doubled_weight_sum_contamination_budget
            < coefficient * sample.even,
        )

    def finite_tail_threshold_for_hl_singular_series_lower_bound(
        self, coefficient: float
    ) -> int | None:
        """Return first sampled even n after which approx singular series >= c."""
        if coefficient <= 0:
            raise ValueError("coefficient must be positive")
        return finite_tail_threshold(
            self.samples,
            lambda sample: sample.singular_series_approx >= coefficient,
        )

    def finite_tail_threshold_for_hl_normalized_error(
        self, relative_error: float
    ) -> int | None:
        """Return first sampled even n after which approx HL error <= δ."""
        if relative_error < 0 or relative_error >= 1:
            raise ValueError("relative_error must satisfy 0 <= relative_error < 1")
        return finite_tail_threshold(
            self.samples,
            lambda sample: sample.hl_normalized_error_abs_approx
            <= relative_error,
        )

    def finite_tail_threshold_for_canonical_hl_certificate_shape(
        self,
        coefficient: float,
        relative_error: float,
    ) -> int | None:
        """Return sampled tail threshold for the canonical HL certificate shape.

        This finite check uses the truncated singular-series approximation and
        the computed weight-sum budget. It is exploratory only, not a proof of
        any Lean obligation.
        """
        if coefficient <= 0:
            raise ValueError("coefficient must be positive")
        if relative_error < 0 or relative_error >= 1:
            raise ValueError("relative_error must satisfy 0 <= relative_error < 1")
        effective_coefficient = (1.0 - relative_error) * coefficient
        return finite_tail_threshold(
            self.samples,
            lambda sample: (
                sample.singular_series_approx >= coefficient
                and sample.hl_normalized_error_abs_approx <= relative_error
                and sample.doubled_weight_sum_contamination_budget
                < effective_coefficient * sample.even
            ),
        )


def finite_tail_threshold(
    samples: list[VonMangoldtSample],
    predicate,
) -> int | None:
    threshold: int | None = None
    all_later = True

    for sample in reversed(samples):
        all_later = all_later and predicate(sample)
        if all_later:
            threshold = sample.even

    return threshold


def nat_log(base: int, value: int) -> int:
    """Return Lean/Mathlib-style ``Nat.log base value`` for base >= 2."""
    if base < 2:
        raise ValueError("base must be at least 2")
    if value < 1:
        return 0

    exponent = 0
    power = base
    while power <= value:
        exponent += 1
        power *= base
    return exponent


def build_von_mangoldt_values(limit: int) -> list[float]:
    """Return Λ(n) for 0 <= n <= limit, with Λ(p^k) = log(p)."""
    if limit < 0:
        raise ValueError("limit must be non-negative")

    values = [0.0] * (limit + 1)
    primes = primes_from_sieve(build_prime_sieve(limit))

    for prime in primes:
        log_prime = math.log(prime)
        power = prime
        while power <= limit:
            values[power] = log_prime
            power *= prime

    return values


def raw_von_mangoldt_goldbach_sums(limit: int) -> list[float]:
    """Compute ordered sums ``sum_{p=0}^n Λ(p)Λ(n-p)`` for n <= limit."""
    if limit < 0:
        raise ValueError("limit must be non-negative")

    mangoldt = build_von_mangoldt_values(limit)
    support = [index for index, value in enumerate(mangoldt) if value != 0.0]
    raw_sums = [0.0] * (limit + 1)

    for left in support:
        left_weight = mangoldt[left]
        for right in support:
            total = left + right
            if total > limit:
                break
            raw_sums[total] += left_weight * mangoldt[right]

    return raw_sums


def weighted_prime_pair_goldbach_sums(limit: int) -> list[float]:
    """Compute ordered sums over prime pairs ``p + q = n`` for n <= limit."""
    if limit < 0:
        raise ValueError("limit must be non-negative")

    primes = primes_from_sieve(build_prime_sieve(limit))
    log_values = [0.0] * (limit + 1)
    for prime in primes:
        log_values[prime] = math.log(prime)

    prime_pair_sums = [0.0] * (limit + 1)
    for left in primes:
        left_weight = log_values[left]
        for right in primes:
            total = left + right
            if total > limit:
                break
            prime_pair_sums[total] += left_weight * log_values[right]

    return prime_pair_sums


def goldbach_singular_series_approximations(limit: int) -> list[float]:
    """Return truncated Goldbach singular-series approximations.

    For even n this uses the standard finite Euler-product truncation

      2 * Π_{3 <= p <= limit} (1 - 1 / (p - 1)^2)
        * Π_{p | n, p > 2} (p - 1) / (p - 2).

    These values are only finite numerical diagnostics for the HL handoff; the
    analytic certificate still needs formal Lean declarations.
    """
    if limit < 0:
        raise ValueError("limit must be non-negative")

    sieve = build_prime_sieve(limit)
    primes = primes_from_sieve(sieve)
    twin_prime_product = 1.0
    for prime in primes:
        if prime > 2:
            twin_prime_product *= 1.0 - 1.0 / ((prime - 1) * (prime - 1))

    base = 2.0 * twin_prime_product
    values = [0.0] * (limit + 1)
    for even in range(4, limit + 1, 2):
        values[even] = base

    for prime in primes:
        if prime <= 2:
            continue
        multiplier = (prime - 1) / (prime - 2)
        for multiple in range(prime * 2, limit + 1, prime * 2):
            values[multiple] *= multiplier

    return values


def non_prime_prime_power_von_mangoldt_weight_sums(limit: int) -> list[float]:
    """Compute Lean's ``NonPrimePrimePowerVonMangoldtWeightSum n`` for n <= limit."""
    if limit < 0:
        raise ValueError("limit must be non-negative")

    mangoldt = build_von_mangoldt_values(limit)
    sieve = build_prime_sieve(limit)
    weight_sums = [0.0] * (limit + 1)
    running_sum = 0.0

    for value in range(limit + 1):
        if mangoldt[value] != 0.0 and not sieve[value]:
            running_sum += mangoldt[value]
        weight_sums[value] = running_sum

    return weight_sums


def non_prime_prime_power_sqrt_log_count_bound(value: int) -> int:
    if value < 0:
        raise ValueError("value must be non-negative")
    return (math.isqrt(value) + 1) * (nat_log(2, value) + 1)


def doubled_sqrt_log_contamination_budget(value: int) -> float:
    if value <= 0:
        return 0.0
    count_bound = non_prime_prime_power_sqrt_log_count_bound(value)
    log_value = math.log(value)
    return 2.0 * count_bound * log_value * log_value


def doubled_weight_sum_contamination_budget(value: int, weight_sum: float) -> float:
    """Compute ``2 * NonPrimePrimePowerVonMangoldtWeightSum n * log n``."""
    if value <= 0:
        return 0.0
    return 2.0 * weight_sum * math.log(value)


def analyze_von_mangoldt(limit: int, start: int = 4) -> VonMangoldtAnalysis:
    if limit < 4:
        raise ValueError("limit must be at least 4")
    if start < 4:
        raise ValueError("start must be at least 4")
    if limit < start:
        raise ValueError("limit must be at least start")

    first_even = start if start % 2 == 0 else start + 1
    raw_sums = raw_von_mangoldt_goldbach_sums(limit)
    singular_series = goldbach_singular_series_approximations(limit)
    prime_pair_sums = weighted_prime_pair_goldbach_sums(limit)
    non_prime_prime_power_weight_sums = (
        non_prime_prime_power_von_mangoldt_weight_sums(limit)
    )
    samples: list[VonMangoldtSample] = []

    for even in range(first_even, limit + 1, 2):
        raw_sum = raw_sums[even]
        singular_series_approx = singular_series[even]
        hl_main_term_approx = singular_series_approx * even
        raw_over_hl_main_approx = (
            raw_sum / hl_main_term_approx if hl_main_term_approx else math.inf
        )
        hl_normalized_error_abs_approx = (
            abs(raw_sum - hl_main_term_approx) / abs(hl_main_term_approx)
            if hl_main_term_approx
            else math.inf
        )
        prime_pair_sum = prime_pair_sums[even]
        actual_contamination = raw_sum - prime_pair_sum
        if abs(actual_contamination) < 1e-12:
            actual_contamination = 0.0
        doubled_budget = doubled_sqrt_log_contamination_budget(even)
        weight_sum = non_prime_prime_power_weight_sums[even]
        doubled_weight_sum_budget = doubled_weight_sum_contamination_budget(
            even, weight_sum
        )
        samples.append(
            VonMangoldtSample(
                even=even,
                raw_sum=raw_sum,
                raw_over_n=raw_sum / even,
                singular_series_approx=singular_series_approx,
                hl_main_term_approx=hl_main_term_approx,
                raw_over_hl_main_approx=raw_over_hl_main_approx,
                hl_normalized_error_abs_approx=hl_normalized_error_abs_approx,
                prime_pair_sum=prime_pair_sum,
                prime_pair_over_n=prime_pair_sum / even,
                actual_contamination_sum=actual_contamination,
                actual_contamination_over_n=actual_contamination / even,
                doubled_contamination_budget=doubled_budget,
                doubled_contamination_over_n=doubled_budget / even,
                actual_contamination_over_doubled_budget=(
                    actual_contamination / doubled_budget
                    if doubled_budget
                    else math.inf
                ),
                raw_over_doubled_contamination=(
                    raw_sum / doubled_budget if doubled_budget else math.inf
                ),
                non_prime_prime_power_weight_sum=weight_sum,
                doubled_weight_sum_contamination_budget=doubled_weight_sum_budget,
                doubled_weight_sum_contamination_budget_over_n=(
                    doubled_weight_sum_budget / even
                ),
                actual_contamination_over_doubled_weight_sum_budget=(
                    actual_contamination / doubled_weight_sum_budget
                    if doubled_weight_sum_budget
                    else math.inf
                ),
                raw_over_doubled_weight_sum_contamination=(
                    raw_sum / doubled_weight_sum_budget
                    if doubled_weight_sum_budget
                    else math.inf
                ),
                raw_over_actual_contamination=(
                    raw_sum / actual_contamination
                    if actual_contamination
                    else math.inf
                ),
            )
        )

    return VonMangoldtAnalysis(start=first_even, limit=limit, samples=samples)


def write_analysis_csv(analysis: VonMangoldtAnalysis, output_path: Path) -> None:
    with output_path.open("w", newline="") as output_file:
        writer = csv.writer(output_file)
        writer.writerow(
            [
                "even",
                "raw_sum",
                "raw_over_n",
                "singular_series_approx",
                "hl_main_term_approx",
                "raw_over_hl_main_approx",
                "hl_normalized_error_abs_approx",
                "prime_pair_sum",
                "prime_pair_over_n",
                "actual_contamination_sum",
                "actual_contamination_over_n",
                "doubled_contamination_budget",
                "doubled_contamination_over_n",
                "actual_contamination_over_doubled_budget",
                "raw_over_doubled_contamination",
                "non_prime_prime_power_weight_sum",
                "doubled_weight_sum_contamination_budget",
                "doubled_weight_sum_contamination_budget_over_n",
                "actual_contamination_over_doubled_weight_sum_budget",
                "raw_over_doubled_weight_sum_contamination",
                "raw_over_actual_contamination",
            ]
        )
        for sample in analysis.samples:
            writer.writerow(
                [
                    sample.even,
                    f"{sample.raw_sum:.17g}",
                    f"{sample.raw_over_n:.17g}",
                    f"{sample.singular_series_approx:.17g}",
                    f"{sample.hl_main_term_approx:.17g}",
                    f"{sample.raw_over_hl_main_approx:.17g}",
                    f"{sample.hl_normalized_error_abs_approx:.17g}",
                    f"{sample.prime_pair_sum:.17g}",
                    f"{sample.prime_pair_over_n:.17g}",
                    f"{sample.actual_contamination_sum:.17g}",
                    f"{sample.actual_contamination_over_n:.17g}",
                    f"{sample.doubled_contamination_budget:.17g}",
                    f"{sample.doubled_contamination_over_n:.17g}",
                    f"{sample.actual_contamination_over_doubled_budget:.17g}",
                    f"{sample.raw_over_doubled_contamination:.17g}",
                    f"{sample.non_prime_prime_power_weight_sum:.17g}",
                    f"{sample.doubled_weight_sum_contamination_budget:.17g}",
                    f"{sample.doubled_weight_sum_contamination_budget_over_n:.17g}",
                    f"{sample.actual_contamination_over_doubled_weight_sum_budget:.17g}",
                    f"{sample.raw_over_doubled_weight_sum_contamination:.17g}",
                    f"{sample.raw_over_actual_contamination:.17g}",
                ]
            )


def render_coefficient_summary(
    analysis: VonMangoldtAnalysis, coefficient: float
) -> list[str]:
    raw_threshold = analysis.finite_tail_threshold_for_raw_lower_bound(coefficient)
    budget_threshold = analysis.finite_tail_threshold_for_budget_domination(
        coefficient
    )
    weight_sum_budget_threshold = (
        analysis.finite_tail_threshold_for_weight_sum_budget_domination(
            coefficient
        )
    )
    raw_text = (
        str(raw_threshold)
        if raw_threshold is not None
        else "not found in sampled range"
    )
    budget_text = (
        str(budget_threshold)
        if budget_threshold is not None
        else "not found in sampled range"
    )
    weight_sum_budget_text = (
        str(weight_sum_budget_threshold)
        if weight_sum_budget_threshold is not None
        else "not found in sampled range"
    )
    return [
        f"Finite tail threshold for raw_sum >= {coefficient:.12g}*n: {raw_text}.",
        (
            "Finite tail threshold for doubled contamination budget "
            f"< {coefficient:.12g}*n: {budget_text}."
        ),
        (
            "Finite tail threshold for doubled weight-sum contamination budget "
            f"< {coefficient:.12g}*n: {weight_sum_budget_text}."
        ),
    ]


def render_hl_certificate_shape_summary(
    analysis: VonMangoldtAnalysis,
    coefficient: float,
    relative_error: float,
) -> list[str]:
    singular_threshold = (
        analysis.finite_tail_threshold_for_hl_singular_series_lower_bound(
            coefficient
        )
    )
    normalized_error_threshold = (
        analysis.finite_tail_threshold_for_hl_normalized_error(relative_error)
    )
    canonical_threshold = (
        analysis.finite_tail_threshold_for_canonical_hl_certificate_shape(
            coefficient,
            relative_error,
        )
    )

    def render_threshold(threshold: int | None) -> str:
        return str(threshold) if threshold is not None else "not found in sampled range"

    return [
        (
            "Finite tail threshold for approximate singularSeries(n) >= "
            f"{coefficient:.12g}: {render_threshold(singular_threshold)}."
        ),
        (
            "Finite tail threshold for approximate HL normalized error <= "
            f"{relative_error:.12g}: "
            f"{render_threshold(normalized_error_threshold)}."
        ),
        (
            "Finite tail threshold for canonical HL certificate shape "
            f"(c={coefficient:.12g}, δ={relative_error:.12g}): "
            f"{render_threshold(canonical_threshold)}."
        ),
    ]


def render_summary(
    analysis: VonMangoldtAnalysis,
    coefficients: list[float] | None = None,
    relative_errors: list[float] | None = None,
) -> str:
    min_raw = analysis.min_raw_over_n
    min_prime_pair = analysis.min_prime_pair_over_n
    min_singular_series = analysis.min_singular_series_approx
    max_hl_normalized_error = analysis.max_hl_normalized_error_abs_approx
    max_actual_contamination = analysis.max_actual_contamination_over_n
    max_budget = analysis.max_doubled_contamination_over_n
    max_weight_sum_budget = (
        analysis.max_doubled_weight_sum_contamination_budget_over_n
    )
    max_actual_over_budget = (
        analysis.max_actual_contamination_over_doubled_budget
    )
    max_actual_over_weight_sum_budget = (
        analysis.max_actual_contamination_over_doubled_weight_sum_budget
    )
    min_ratio = analysis.min_raw_over_doubled_contamination
    min_weight_sum_ratio = (
        analysis.min_raw_over_doubled_weight_sum_contamination
    )

    lines = [
        f"Analyzed even n from {analysis.start} through {analysis.limit}.",
        (
            "Minimum RawVonMangoldtGoldbachSum(n)/n: "
            f"{min_raw.raw_over_n:.12g} at n = {min_raw.even}."
        ),
        (
            "Minimum prime-pair Λ contribution / n: "
            f"{min_prime_pair.prime_pair_over_n:.12g} "
            f"at n = {min_prime_pair.even}."
        ),
        (
            "Minimum truncated Goldbach singular series approximation: "
            f"{min_singular_series.singular_series_approx:.12g} "
            f"at n = {min_singular_series.even}."
        ),
        (
            "Maximum approximate HL normalized error: "
            f"{max_hl_normalized_error.hl_normalized_error_abs_approx:.12g} "
            f"at n = {max_hl_normalized_error.even}."
        ),
        (
            "Maximum actual non-prime-pair contamination / n: "
            f"{max_actual_contamination.actual_contamination_over_n:.12g} "
            f"at n = {max_actual_contamination.even}."
        ),
        (
            "Maximum doubled contamination budget / n: "
            f"{max_budget.doubled_contamination_over_n:.12g} "
            f"at n = {max_budget.even}."
        ),
        (
            "Maximum doubled weight-sum contamination budget / n: "
            f"{max_weight_sum_budget.doubled_weight_sum_contamination_budget_over_n:.12g} "
            f"at n = {max_weight_sum_budget.even}."
        ),
        (
            "Maximum actual contamination / doubled budget: "
            f"{max_actual_over_budget.actual_contamination_over_doubled_budget:.12g} "
            f"at n = {max_actual_over_budget.even}."
        ),
        (
            "Maximum actual contamination / doubled weight-sum budget: "
            f"{max_actual_over_weight_sum_budget.actual_contamination_over_doubled_weight_sum_budget:.12g} "
            f"at n = {max_actual_over_weight_sum_budget.even}."
        ),
        (
            "Minimum raw / doubled contamination budget: "
            f"{min_ratio.raw_over_doubled_contamination:.12g} "
            f"at n = {min_ratio.even}."
        ),
        (
            "Minimum raw / doubled weight-sum contamination budget: "
            f"{min_weight_sum_ratio.raw_over_doubled_weight_sum_contamination:.12g} "
            f"at n = {min_weight_sum_ratio.even}."
        ),
    ]
    if coefficients is not None:
        for coefficient in coefficients:
            lines.extend(render_coefficient_summary(analysis, coefficient))
    if coefficients is not None and relative_errors is not None:
        for coefficient in coefficients:
            for relative_error in relative_errors:
                lines.extend(
                    render_hl_certificate_shape_summary(
                        analysis,
                        coefficient,
                        relative_error,
                    )
                )
    lines.append("This is finite numerical exploration, not a proof of Goldbach.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Analyze finite raw von Mangoldt Goldbach data."
    )
    parser.add_argument("limit", type=int, help="inclusive upper bound")
    parser.add_argument(
        "--start",
        type=int,
        default=4,
        help="inclusive lower bound for even n; default: 4",
    )
    parser.add_argument(
        "--export-csv",
        type=Path,
        help="optional CSV output path for per-even samples",
    )
    parser.add_argument(
        "--coefficient",
        type=float,
        action="append",
        help=(
            "positive coefficient c for finite tail checks of raw_sum >= c*n "
            "and doubled contamination budget < c*n; also combines with "
            "--relative-error for canonical HL shape checks; may be repeated"
        ),
    )
    parser.add_argument(
        "--relative-error",
        type=float,
        action="append",
        help=(
            "relative error δ for finite exploratory checks of the canonical "
            "HL certificate shape; requires at least one --coefficient and "
            "may be repeated"
        ),
    )
    args = parser.parse_args()

    analysis = analyze_von_mangoldt(args.limit, args.start)
    if args.export_csv is not None:
        write_analysis_csv(analysis, args.export_csv)
    print(render_summary(analysis, args.coefficient, args.relative_error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
