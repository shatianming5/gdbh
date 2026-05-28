import unittest
from pathlib import Path

from audit_lean_source import (
    BANNED_TOKENS,
    audit_project_sources,
    find_banned_tokens_in_text,
    mask_comments_and_strings,
    project_lean_files,
)


PROJECT_ROOT = Path(__file__).parent


class LeanSourceAuditTests(unittest.TestCase):
    def test_project_lean_files_do_not_use_banned_tokens(self) -> None:
        offenders = audit_project_sources(PROJECT_ROOT)

        self.assertEqual([offender.format(PROJECT_ROOT) for offender in offenders], [])

    def test_project_lean_files_include_root_module(self) -> None:
        files = project_lean_files(PROJECT_ROOT)

        self.assertIn(PROJECT_ROOT / "Gdbh.lean", files)
        self.assertIn(PROJECT_ROOT / "Gdbh" / "Goldbach.lean", files)

    def test_comment_and_string_masking_preserves_lines(self) -> None:
        source = "\n".join(
            [
                "-- axiom hidden",
                '/- sorry hidden "constant" -/',
                '/- nested /- admit -/ opaque -/',
                '#eval "unsafe axiom sorry"',
                "theorem safe : True := by trivial",
                "",
            ]
        )

        masked = mask_comments_and_strings(source)
        offenders = find_banned_tokens_in_text(source, Path("Example.lean"))

        self.assertEqual(masked.count("\n"), source.count("\n"))
        self.assertEqual(offenders, [])

    def test_banned_tokens_are_detected_outside_comments_and_strings(self) -> None:
        for token in BANNED_TOKENS:
            with self.subTest(token=token):
                source = f"{token} badDecl : True\n"
                offenders = find_banned_tokens_in_text(
                    source,
                    Path("Bad.lean"),
                )

                self.assertEqual(len(offenders), 1)
                self.assertEqual(offenders[0].token, token)
                self.assertEqual(offenders[0].line_number, 1)

    def test_substrings_inside_identifiers_are_not_banned_tokens(self) -> None:
        source = "\n".join(
            [
                "theorem axiomatic_name : True := by trivial",
                "theorem sorryful_name : True := by trivial",
                "",
            ]
        )

        offenders = find_banned_tokens_in_text(source, Path("Names.lean"))

        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()
