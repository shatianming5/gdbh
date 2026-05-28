import csv
import math
import tempfile
import unittest
from pathlib import Path

from analyze_von_mangoldt import (
    analyze_von_mangoldt,
    build_von_mangoldt_values,
    doubled_sqrt_log_contamination_budget,
    doubled_weight_sum_contamination_budget,
    goldbach_singular_series_approximations,
    nat_log,
    non_prime_prime_power_von_mangoldt_weight_sums,
    raw_von_mangoldt_goldbach_sums,
    render_summary,
    weighted_prime_pair_goldbach_sums,
    write_analysis_csv,
)
from verify_goldbach import (
    build_prime_sieve,
    build_certificate_manifest,
    build_chunked_interval_certificate_manifest,
    build_interval_certificate_manifest,
    chunk_intervals,
    export_certificate_manifest,
    export_chunked_interval_witnesses_lean,
    export_interval_witnesses_lean,
    export_witnesses_csv,
    export_witnesses_lean,
    find_witness,
    primes_from_sieve,
    render_chunked_interval_certificate_manifest,
    render_interval_certificate_manifest,
    render_lean_chunked_interval_certificate,
    render_lean_interval_certificate,
    render_certificate_manifest,
    render_lean_certificate,
    witnesses_between,
    witnesses_up_to,
)


class GoldbachVerifierTests(unittest.TestCase):
    def test_sieve_marks_primes_and_composites(self) -> None:
        sieve = build_prime_sieve(20)
        primes = [index for index, is_prime in enumerate(sieve) if is_prime]
        self.assertEqual(primes, [2, 3, 5, 7, 11, 13, 17, 19])

    def test_nat_log_matches_floor_log_base(self) -> None:
        self.assertEqual(nat_log(2, 0), 0)
        self.assertEqual(nat_log(2, 1), 0)
        self.assertEqual(nat_log(2, 2), 1)
        self.assertEqual(nat_log(2, 7), 2)
        self.assertEqual(nat_log(2, 8), 3)
        self.assertEqual(nat_log(3, 26), 2)
        self.assertEqual(nat_log(3, 27), 3)

    def test_von_mangoldt_values_mark_prime_powers(self) -> None:
        values = build_von_mangoldt_values(10)
        self.assertEqual(values[0], 0.0)
        self.assertEqual(values[1], 0.0)
        self.assertAlmostEqual(values[2], math.log(2))
        self.assertAlmostEqual(values[3], math.log(3))
        self.assertAlmostEqual(values[4], math.log(2))
        self.assertAlmostEqual(values[6], 0.0)
        self.assertAlmostEqual(values[8], math.log(2))
        self.assertAlmostEqual(values[9], math.log(3))

    def test_raw_von_mangoldt_goldbach_sums_small_values(self) -> None:
        raw_sums = raw_von_mangoldt_goldbach_sums(6)
        prime_pair_sums = weighted_prime_pair_goldbach_sums(6)
        self.assertAlmostEqual(raw_sums[4], math.log(2) * math.log(2))
        self.assertAlmostEqual(
            raw_sums[6],
            2 * math.log(2) * math.log(2) + math.log(3) * math.log(3),
        )
        self.assertAlmostEqual(prime_pair_sums[4], math.log(2) * math.log(2))
        self.assertAlmostEqual(prime_pair_sums[6], math.log(3) * math.log(3))

    def test_non_prime_prime_power_weight_sums_small_values(self) -> None:
        weight_sums = non_prime_prime_power_von_mangoldt_weight_sums(10)

        self.assertAlmostEqual(weight_sums[3], 0.0)
        self.assertAlmostEqual(weight_sums[4], math.log(2))
        self.assertAlmostEqual(weight_sums[7], math.log(2))
        self.assertAlmostEqual(weight_sums[8], 2 * math.log(2))
        self.assertAlmostEqual(weight_sums[10], 2 * math.log(2) + math.log(3))
        self.assertAlmostEqual(
            doubled_weight_sum_contamination_budget(4, weight_sums[4]),
            4 * math.log(2) * math.log(2),
        )

    def test_goldbach_singular_series_approximations_small_values(self) -> None:
        series = goldbach_singular_series_approximations(10)
        base = 2 * (3 / 4) * (15 / 16) * (35 / 36)

        self.assertEqual(series[3], 0.0)
        self.assertAlmostEqual(series[4], base)
        self.assertAlmostEqual(series[6], 2 * base)
        self.assertAlmostEqual(series[10], (4 / 3) * base)

    def test_von_mangoldt_analysis_and_csv(self) -> None:
        analysis = analyze_von_mangoldt(10)
        self.assertEqual([sample.even for sample in analysis.samples], [4, 6, 8, 10])
        self.assertGreater(analysis.min_raw_over_n.raw_over_n, 0)
        self.assertGreater(analysis.min_singular_series_approx.singular_series_approx, 0)
        self.assertGreater(
            analysis.max_hl_normalized_error_abs_approx.hl_normalized_error_abs_approx,
            0,
        )
        self.assertEqual(analysis.samples[0].actual_contamination_sum, 0.0)
        self.assertGreater(analysis.samples[0].hl_main_term_approx, 0)
        self.assertLess(analysis.samples[0].raw_over_hl_main_approx, 1)
        self.assertAlmostEqual(
            analysis.samples[0].non_prime_prime_power_weight_sum,
            math.log(2),
        )
        self.assertAlmostEqual(
            analysis.samples[-1].non_prime_prime_power_weight_sum,
            2 * math.log(2) + math.log(3),
        )
        self.assertAlmostEqual(
            analysis.samples[1].actual_contamination_sum,
            2 * math.log(2) * math.log(2),
        )
        max_actual_over_budget = (
            analysis.max_actual_contamination_over_doubled_budget
        )
        self.assertGreaterEqual(
            max_actual_over_budget.actual_contamination_over_doubled_budget,
            0.0,
        )
        self.assertGreater(doubled_sqrt_log_contamination_budget(10), 0)
        self.assertEqual(
            analysis.finite_tail_threshold_for_raw_lower_bound(0.1), 4
        )
        self.assertIsNone(
            analysis.finite_tail_threshold_for_budget_domination(1.0)
        )
        self.assertIsNone(
            analysis.finite_tail_threshold_for_weight_sum_budget_domination(1.0)
        )
        self.assertEqual(
            analysis.finite_tail_threshold_for_budget_domination(100.0), 4
        )
        self.assertEqual(
            analysis.finite_tail_threshold_for_weight_sum_budget_domination(2.0),
            4,
        )
        self.assertEqual(
            analysis.finite_tail_threshold_for_hl_singular_series_lower_bound(1.0),
            4,
        )
        self.assertEqual(
            analysis.finite_tail_threshold_for_hl_normalized_error(0.99),
            4,
        )
        self.assertIsNone(
            analysis.finite_tail_threshold_for_canonical_hl_certificate_shape(
                1.0,
                0.99,
            )
        )
        self.assertIn(
            "Finite tail threshold for raw_sum >= 0.1*n: 4.",
            render_summary(analysis, [0.1]),
        )
        self.assertIn(
            "Finite tail threshold for canonical HL certificate shape",
            render_summary(analysis, [1.0], [0.99]),
        )
        self.assertIn("Maximum actual contamination / doubled budget", render_summary(analysis))
        self.assertIn(
            "Maximum approximate HL normalized error",
            render_summary(analysis),
        )
        self.assertIn(
            "Maximum actual contamination / doubled weight-sum budget",
            render_summary(analysis),
        )

        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "mangoldt.csv"
            write_analysis_csv(analysis, output_path)
            with output_path.open(newline="") as input_file:
                rows = list(csv.DictReader(input_file))

        self.assertEqual(rows[0]["even"], "4")
        self.assertIn("raw_over_n", rows[0])
        self.assertIn("singular_series_approx", rows[0])
        self.assertIn("hl_normalized_error_abs_approx", rows[0])
        self.assertIn("non_prime_prime_power_weight_sum", rows[0])
        self.assertIn("raw_over_doubled_weight_sum_contamination", rows[0])

    def test_find_witness_for_small_even_numbers(self) -> None:
        sieve = build_prime_sieve(20)
        primes = primes_from_sieve(sieve)

        for even in range(4, 22, 2):
            witness = find_witness(even, primes, sieve)
            self.assertIsNotNone(witness)
            assert witness is not None
            self.assertEqual(witness.left + witness.right, even)
            self.assertTrue(sieve[witness.left])
            self.assertTrue(sieve[witness.right])

    def test_negative_limit_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            build_prime_sieve(-1)

    def test_witnesses_up_to_rejects_too_small_limit(self) -> None:
        with self.assertRaises(ValueError):
            witnesses_up_to(3)

    def test_witnesses_between_rejects_invalid_interval(self) -> None:
        with self.assertRaises(ValueError):
            witnesses_between(1, 10)
        with self.assertRaises(ValueError):
            witnesses_between(10, 10)

    def test_chunk_intervals(self) -> None:
        self.assertEqual(chunk_intervals(10, 25, 6), [(10, 16), (16, 22), (22, 25)])
        with self.assertRaises(ValueError):
            chunk_intervals(10, 20, 0)

    def test_export_witnesses_csv(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "goldbach.csv"
            export_witnesses_csv(10, output_path)

            with output_path.open(newline="") as input_file:
                rows = list(csv.DictReader(input_file))

        self.assertEqual(
            rows,
            [
                {"even": "4", "left": "2", "right": "2"},
                {"even": "6", "left": "3", "right": "3"},
                {"even": "8", "left": "3", "right": "5"},
                {"even": "10", "left": "3", "right": "7"},
            ],
        )

    def test_render_lean_certificate(self) -> None:
        lean = render_lean_certificate(10)

        self.assertIn("import Gdbh.CircleMethod", lean)
        self.assertIn("def certificate10 : List CertificateEntry :=", lean)
        self.assertIn("theorem goldbachUpTo10 : GoldbachUpTo 10 :=", lean)
        self.assertIn(
            "theorem strongGoldbach_iff_goldbachAbove10 :",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_certificate10_and_count_positive_bridge",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_iff_count_positive_above10 :",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_certificate10_and_circle_method",
            lean,
        )
        self.assertIn("{ n := 10, p := 3, q := 7 }", lean)
        self.assertNotIn("axiom", lean)
        self.assertNotIn("sorry", lean)
        self.assertNotIn("admit", lean)

    def test_render_lean_interval_certificate(self) -> None:
        lean = render_lean_interval_certificate(10, 20)

        self.assertIn("import Gdbh.FiniteIntervals", lean)
        self.assertIn("def certificate10To20 : List CertificateEntry :=", lean)
        self.assertIn(
            "theorem goldbachBetween10To20 :",
            lean,
        )
        self.assertIn(
            "theorem goldbachUpTo20_of_goldbachUpTo10_and_certificate10To20",
            lean,
        )
        self.assertIn("{ n := 12, p := 5, q := 7 }", lean)
        self.assertIn("{ n := 20, p := 3, q := 17 }", lean)
        self.assertNotIn("{ n := 10,", lean)
        self.assertNotIn("axiom", lean)
        self.assertNotIn("sorry", lean)
        self.assertNotIn("admit", lean)

    def test_render_lean_chunked_interval_certificate(self) -> None:
        lean = render_lean_chunked_interval_certificate(10, 30, 10)

        self.assertIn("def certificate10To20 : List CertificateEntry :=", lean)
        self.assertIn("def certificate20To30 : List CertificateEntry :=", lean)
        self.assertIn("theorem goldbachBetween10To30 :", lean)
        self.assertIn(
            "theorem goldbachUpTo30_of_goldbachUpTo10_and_chunkedCertificate10To30",
            lean,
        )
        self.assertNotIn("axiom", lean)
        self.assertNotIn("sorry", lean)
        self.assertNotIn("admit", lean)

    def test_render_lean_chunked_interval_certificate_from_two_is_self_contained(self) -> None:
        lean = render_lean_chunked_interval_certificate(2, 30, 10)

        self.assertIn("theorem goldbachUpTo30_of_chunkedCertificate2To30 :", lean)
        self.assertIn("import Gdbh.ContaminatedWeightedGoldbach", lean)
        self.assertIn("import Gdbh.RealContaminatedWeightedGoldbach", lean)
        self.assertIn("import Gdbh.VonMangoldtGoldbach", lean)
        self.assertIn("goldbachUpTo_of_between_two goldbachBetween2To30", lean)
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_explicit_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem explicitLowerBound100_from_chunkedCertificate2To30_and_explicit_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_circle_method_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_count_positive_above",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_weighted_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_weighted_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_count_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_lower_bound",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate",
            lean,
        )
        self.assertIn(
            "theorem strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_lower_bound",
            lean,
        )
        self.assertNotIn("(upTo_lower : GoldbachUpTo 2)", lean)

    def test_export_witnesses_lean(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "Certificate10.lean"
            export_witnesses_lean(10, output_path)

            self.assertEqual(output_path.read_text(), render_lean_certificate(10))

    def test_export_interval_witnesses_lean(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "Certificate10To20.lean"
            export_interval_witnesses_lean(10, 20, output_path)

            self.assertEqual(
                output_path.read_text(), render_lean_interval_certificate(10, 20)
            )

    def test_export_chunked_interval_witnesses_lean(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "Certificate10To30.lean"
            export_chunked_interval_witnesses_lean(10, 30, 10, output_path)

            self.assertEqual(
                output_path.read_text(),
                render_lean_chunked_interval_certificate(10, 30, 10),
            )

    def test_render_certificate_manifest(self) -> None:
        manifest = build_certificate_manifest(10, Path("Gdbh/Certificate10.lean"))

        self.assertEqual(manifest["bound"], 10)
        self.assertEqual(manifest["certificate"], "Gdbh/Certificate10.lean")
        self.assertEqual(manifest["lean_theorem"], "Gdbh.goldbachUpTo10")
        self.assertEqual(len(str(manifest["sha256"])), 64)
        self.assertIn("--export-manifest", str(manifest["generator_command"]))

    def test_render_interval_certificate_manifest(self) -> None:
        manifest = build_interval_certificate_manifest(
            10, 20, Path("Gdbh/Certificate10To20.lean")
        )

        self.assertEqual(manifest["lower_bound"], 10)
        self.assertEqual(manifest["bound"], 20)
        self.assertEqual(
            manifest["lean_theorem"], "Gdbh.goldbachBetween10To20"
        )
        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo20_of_goldbachUpTo10_and_certificate10To20",
        )
        self.assertIn("--interval-start 10", str(manifest["generator_command"]))

    def test_render_interval_certificate_manifest_from_two(self) -> None:
        manifest = build_interval_certificate_manifest(
            2, 20, Path("Gdbh/Certificate2To20.lean")
        )

        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo20_of_certificate2To20",
        )
        self.assertEqual(
            manifest["lean_strong_explicit_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_explicit_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_explicit_lower_bound100_explicit_lower_bound_theorem"
            ],
            "Gdbh.explicitLowerBound100_from_certificate2To20_and_explicit_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_count_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_count_positive_above",
        )
        self.assertEqual(
            manifest["lean_strong_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_contaminated_weighted_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_contaminated_weighted_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_contaminated_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_contaminated_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_real_contaminated_weighted_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_real_contaminated_weighted_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_real_contaminated_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_real_contaminated_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_vonMangoldt_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_vonMangoldt_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_prime_power_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_prime_power_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_prime_power_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_prime_power_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_prime_power_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_prime_power_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_pointwise_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_pointwise_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_pointwise_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_uniform_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_uniform_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_uniform_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_counted_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_counted_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_counted_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_trivial_count_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_trivial_count_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_trivial_count_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_weight_bound_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_weight_bound_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_weight_bound_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_log_weight_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_log_weight_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_log_weight_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_count_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_canonical_log_count_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_count_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_log_count_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_direct_raw_log_count_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_sqrt_log_count_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_hardy_littlewood_normalized_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_canonical_log_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_log_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_certificate2To20_and_vonMangoldt_direct_raw_log_lower_bound",
        )

    def test_render_chunked_interval_certificate_manifest(self) -> None:
        manifest = build_chunked_interval_certificate_manifest(
            10, 30, 10, Path("Gdbh/Certificate10To30.lean")
        )

        self.assertEqual(manifest["lower_bound"], 10)
        self.assertEqual(manifest["bound"], 30)
        self.assertEqual(manifest["chunk_size"], 10)
        self.assertEqual(
            manifest["lean_theorem"], "Gdbh.goldbachBetween10To30"
        )
        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo30_of_goldbachUpTo10_and_chunkedCertificate10To30",
        )
        self.assertIn("--chunk-size 10", str(manifest["generator_command"]))

    def test_render_chunked_interval_certificate_manifest_from_two(self) -> None:
        manifest = build_chunked_interval_certificate_manifest(
            2, 30, 10, Path("Gdbh/Certificate2To30.lean")
        )

        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo30_of_chunkedCertificate2To30",
        )
        self.assertEqual(
            manifest["lean_strong_explicit_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_explicit_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_explicit_lower_bound100_explicit_lower_bound_theorem"
            ],
            "Gdbh.explicitLowerBound100_from_chunkedCertificate2To30_and_explicit_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_circle_method_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_circle_method_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_major_minor_arc_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_count_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_count_positive_above",
        )
        self.assertEqual(
            manifest["lean_strong_weighted_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_weighted_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_contaminated_weighted_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_contaminated_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_real_contaminated_weighted_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_real_contaminated_weighted_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest["lean_strong_vonMangoldt_lower_bound_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_lower_bound",
        )
        self.assertEqual(
            manifest["lean_strong_vonMangoldt_major_minor_theorem"],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_prime_power_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_prime_power_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_prime_power_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_prime_power_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_pointwise_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_pointwise_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_uniform_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_uniform_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_counted_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_counted_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_trivial_count_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_trivial_count_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_weight_bound_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_weight_bound_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_log_weight_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_log_weight_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_count_contamination_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_canonical_log_count_contamination_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_log_count_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_count_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_direct_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_sqrt_log_count_major_minor_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate",
        )
        self.assertEqual(
            manifest[
                "lean_strong_vonMangoldt_direct_raw_log_lower_bound_theorem"
            ],
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_lower_bound",
        )

    def test_export_certificate_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "manifest.json"
            export_certificate_manifest(10, Path("Gdbh/Certificate10.lean"), output_path)

            self.assertEqual(
                output_path.read_text(),
                render_certificate_manifest(
                    10, Path("Gdbh/Certificate10.lean"), output_path
                ),
            )

    def test_render_interval_certificate_manifest_json(self) -> None:
        rendered = render_interval_certificate_manifest(
            10, 20, Path("Gdbh/Certificate10To20.lean")
        )

        self.assertIn('"lower_bound": 10', rendered)
        self.assertIn('"lean_theorem": "Gdbh.goldbachBetween10To20"', rendered)

    def test_render_chunked_interval_certificate_manifest_json(self) -> None:
        rendered = render_chunked_interval_certificate_manifest(
            10, 30, 10, Path("Gdbh/Certificate10To30.lean")
        )

        self.assertIn('"chunk_size": 10', rendered)
        self.assertIn('"lean_theorem": "Gdbh.goldbachBetween10To30"', rendered)


if __name__ == "__main__":
    unittest.main()
