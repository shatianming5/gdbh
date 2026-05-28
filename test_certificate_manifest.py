import hashlib
import json
import unittest
from pathlib import Path

from verify_goldbach import (
    render_certificate_manifest,
    render_chunked_interval_certificate_manifest,
    render_lean_certificate,
)


PROJECT_ROOT = Path(__file__).parent


class CertificateManifestTests(unittest.TestCase):
    def test_certificate_manifest_matches_generated_certificate(self) -> None:
        manifest = json.loads((PROJECT_ROOT / "certificate_manifest.json").read_text())
        certificate_path = PROJECT_ROOT / manifest["certificate"]
        certificate_text = certificate_path.read_text()

        self.assertEqual(
            (PROJECT_ROOT / "certificate_manifest.json").read_text(),
            render_certificate_manifest(manifest["bound"], Path(manifest["certificate"])),
        )
        self.assertEqual(certificate_text, render_lean_certificate(manifest["bound"]))
        self.assertEqual(
            hashlib.sha256(certificate_text.encode()).hexdigest(),
            manifest["sha256"],
        )
        self.assertEqual(manifest["lean_theorem"], "Gdbh.goldbachUpTo100")

    def test_custom_manifest_path_is_recorded_in_generator_command(self) -> None:
        manifest = json.loads(
            render_chunked_interval_certificate_manifest(
                2,
                20,
                10,
                Path("Gdbh/Certificate20.lean"),
                Path("cert20_manifest.json"),
            )
        )

        self.assertIn(
            "--export-manifest cert20_manifest.json",
            manifest["generator_command"],
        )

    def test_cert10000_manifest_records_own_path(self) -> None:
        manifest = json.loads((PROJECT_ROOT / "cert10000_manifest.json").read_text())

        self.assertEqual(manifest["bound"], 10000)
        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo10000_of_chunkedCertificate2To10000",
        )
        self.assertIn(
            "--export-manifest cert10000_manifest.json",
            manifest["generator_command"],
        )

    def test_cert20000_manifest_records_own_path(self) -> None:
        manifest = json.loads((PROJECT_ROOT / "cert20000_manifest.json").read_text())

        self.assertEqual(manifest["bound"], 20000)
        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo20000_of_chunkedCertificate2To20000",
        )
        self.assertIn(
            "--export-manifest cert20000_manifest.json",
            manifest["generator_command"],
        )

    def test_cert50000_manifest_records_own_path(self) -> None:
        manifest = json.loads((PROJECT_ROOT / "cert50000_manifest.json").read_text())

        self.assertEqual(manifest["bound"], 50000)
        self.assertEqual(
            manifest["lean_upgrade_theorem"],
            "Gdbh.goldbachUpTo50000_of_chunkedCertificate2To50000",
        )
        self.assertIn(
            "--export-manifest cert50000_manifest.json",
            manifest["generator_command"],
        )


if __name__ == "__main__":
    unittest.main()
