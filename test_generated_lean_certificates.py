import subprocess
import tempfile
import unittest
from pathlib import Path

from audit_lean_axioms import (
    ALLOWED_AXIOMS,
    iter_axiom_output_lines,
    lake_command,
    parse_axiom_line,
)
from verify_goldbach import (
    render_lean_certificate,
    render_lean_chunked_interval_certificate,
    render_lean_interval_certificate,
)


PROJECT_ROOT = Path(__file__).parent
LEAN_TIMEOUT_SECONDS = 600
GENERATED_CERTIFICATE_IMPORTS = [
    "Gdbh.CircleMethod",
    "Gdbh.FiniteIntervals",
    "Gdbh.GeneralHandoff",
    "Gdbh.ContaminatedWeightedGoldbach",
    "Gdbh.RealContaminatedWeightedGoldbach",
    "Gdbh.VonMangoldtGoldbach",
]


class GeneratedLeanCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        result = subprocess.run(
            [lake_command(), "build", *GENERATED_CERTIFICATE_IMPORTS],
            cwd=PROJECT_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise AssertionError(result.stderr or result.stdout)

    def check_lean_file(self, path: Path) -> str:
        result = subprocess.run(
            [lake_command(), "env", "lean", str(path)],
            cwd=PROJECT_ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=LEAN_TIMEOUT_SECONDS,
        )

        self.assertEqual(
            result.returncode,
            0,
            msg=result.stderr or result.stdout,
        )
        return result.stdout

    def check_generated_axioms(self, stdout: str, theorems: list[str]) -> None:
        parsed = {
            theorem: axioms
            for theorem, axioms in (
                parse_axiom_line(line)
                for line in iter_axiom_output_lines(stdout)
            )
        }
        for theorem in theorems:
            self.assertIn(theorem, parsed)
            self.assertLessEqual(parsed[theorem], ALLOWED_AXIOMS)

    def generated_body(self, certificate_text: str) -> str:
        lines = certificate_text.splitlines()
        start = lines.index("namespace Gdbh") + 2
        end = max(index for index, line in enumerate(lines) if line == "end Gdbh")
        return "\n".join(lines[start:end])

    def combined_generated_certificate(self, theorems: list[str]) -> str:
        bodies = [
            self.generated_body(render_lean_certificate(22)),
            self.generated_body(render_lean_interval_certificate(30, 40)),
            self.generated_body(render_lean_chunked_interval_certificate(50, 70, 10)),
            self.generated_body(render_lean_chunked_interval_certificate(2, 30, 10)),
        ]
        return "\n".join(
            [
                *[f"import {module}" for module in GENERATED_CERTIFICATE_IMPORTS],
                "",
                "namespace Gdbh",
                "",
                *bodies,
                "",
                *[f"#print axioms {theorem}" for theorem in theorems],
                "",
                "end Gdbh",
                "",
            ]
        )

    def test_generated_lean_certificates_typecheck(self) -> None:
        theorems = [
            "Gdbh.explicitLowerBound100_from_chunkedCertificate2To30_and_explicit_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_explicit_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_circle_method_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_count_positive_above",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_weighted_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_weighted_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_contaminated_weighted_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_real_contaminated_weighted_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_count_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_raw_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_lower_bound",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate",
            "Gdbh.strongGoldbach_from_chunkedCertificate2To30_and_vonMangoldt_direct_raw_log_lower_bound",
        ]
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "CombinedGeneratedCertificates.lean"
            path.write_text(self.combined_generated_certificate(theorems))
            stdout = self.check_lean_file(path)
        self.check_generated_axioms(stdout, theorems)


if __name__ == "__main__":
    unittest.main()
