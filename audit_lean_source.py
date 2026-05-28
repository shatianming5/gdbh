#!/usr/bin/env python3
"""Syntax-level audit for project Lean sources.

This is a guardrail, not a proof of theorem independence.  It checks project
source files for commands and placeholders that would introduce assumptions or
hide missing proofs.  The separate audit_lean_axioms.py script checks selected
compiled declarations with Lean's `#print axioms`.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from pathlib import Path


PROJECT_ROOT = Path(__file__).parent
BANNED_TOKENS = ("axiom", "constant", "opaque", "unsafe", "sorry", "admit")
BANNED_TOKEN_RE = re.compile(
    r"\b(" + "|".join(re.escape(token) for token in BANNED_TOKENS) + r")\b"
)


@dataclass(frozen=True)
class SourceOffender:
    path: Path
    line_number: int
    column_number: int
    token: str
    line: str

    def format(self, root: Path = PROJECT_ROOT) -> str:
        try:
            display_path = self.path.relative_to(root)
        except ValueError:
            display_path = self.path
        return (
            f"{display_path}:{self.line_number}:{self.column_number}: "
            f"{self.token}: {self.line.strip()}"
        )


def project_lean_files(project_root: Path = PROJECT_ROOT) -> list[Path]:
    files: list[Path] = []
    root_module = project_root / "Gdbh.lean"
    if root_module.exists():
        files.append(root_module)
    files.extend(sorted((project_root / "Gdbh").rglob("*.lean")))
    return files


def mask_comments_and_strings(source: str) -> str:
    """Replace Lean comments and string contents with spaces.

    Newlines are preserved so line numbers in diagnostics still match the
    original file.  Lean block comments can be nested, so this tracks nesting
    instead of using a regular expression.
    """

    masked: list[str] = []
    index = 0
    line_comment = False
    block_comment_depth = 0
    string_literal = False
    escaped = False

    while index < len(source):
        char = source[index]
        pair = source[index : index + 2]

        if line_comment:
            if char == "\n":
                line_comment = False
                masked.append("\n")
            else:
                masked.append(" ")
            index += 1
            continue

        if block_comment_depth:
            if pair == "/-":
                block_comment_depth += 1
                masked.append("  ")
                index += 2
            elif pair == "-/":
                block_comment_depth -= 1
                masked.append("  ")
                index += 2
            else:
                masked.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if string_literal:
            if escaped:
                escaped = False
                masked.append(" ")
            elif char == "\\":
                escaped = True
                masked.append(" ")
            elif char == '"':
                string_literal = False
                masked.append(" ")
            elif char == "\n":
                string_literal = False
                masked.append("\n")
            else:
                masked.append(" ")
            index += 1
            continue

        if pair == "--":
            line_comment = True
            masked.append("  ")
            index += 2
        elif pair == "/-":
            block_comment_depth = 1
            masked.append("  ")
            index += 2
        elif char == '"':
            string_literal = True
            masked.append(" ")
            index += 1
        else:
            masked.append(char)
            index += 1

    return "".join(masked)


def find_banned_tokens_in_text(source: str, path: Path) -> list[SourceOffender]:
    masked = mask_comments_and_strings(source)
    original_lines = source.splitlines()
    offenders: list[SourceOffender] = []
    for line_number, line in enumerate(masked.splitlines(), start=1):
        for match in BANNED_TOKEN_RE.finditer(line):
            original = (
                original_lines[line_number - 1]
                if line_number - 1 < len(original_lines)
                else ""
            )
            offenders.append(
                SourceOffender(
                    path=path,
                    line_number=line_number,
                    column_number=match.start() + 1,
                    token=match.group(1),
                    line=original,
                )
            )
    return offenders


def audit_project_sources(project_root: Path = PROJECT_ROOT) -> list[SourceOffender]:
    offenders: list[SourceOffender] = []
    for path in project_lean_files(project_root):
        offenders.extend(find_banned_tokens_in_text(path.read_text(), path))
    return offenders


def main() -> int:
    offenders = audit_project_sources(PROJECT_ROOT)
    if offenders:
        for offender in offenders:
            print(f"FAIL: {offender.format(PROJECT_ROOT)}")
        return 1

    print(
        "OK: scanned "
        f"{len(project_lean_files(PROJECT_ROOT))} Lean files; "
        "no banned project assumptions or placeholders"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
