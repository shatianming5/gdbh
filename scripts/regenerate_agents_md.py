#!/usr/bin/env python3
"""Regenerate the AUTO sections of AGENTS.md from authoritative Lean source.

Run from any cwd; resolves the repo root from this script's location.

What it does
------------
1. Parses ``Gdbh/PathA_StatusPhase24.lean`` to recover the canonical list
   ``PathA_GenuineOpenProps`` (the 9 genuinely open Path A Props).
2. Parses ``Gdbh/PathC_FinalSummaryPhase22.lean`` to recover the
   ``FalsePropCatchList`` (the 15 false-Prop catches caught in Phases 9-22).
3. Locates the 4 named Path C open Props by grepping for their ``def`` lines.
4. Counts ``.lean`` files and total lines under ``Gdbh/``.
5. Attempts ``lake env lean --stdin`` for ``#print axioms`` on the two
   headline theorems.  Degrades gracefully if ``lake`` is not on PATH or
   the toolchain is not initialised.
6. Substitutes the regenerated content between the AUTO markers in
   ``AGENTS.md``.  Manual prose outside the markers is preserved verbatim.

Manual edits to AUTO sections WILL be overwritten on the next run.  Edit
the prose outside the markers, or extend this script.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
GDBH = REPO_ROOT / "Gdbh"
AGENTS = REPO_ROOT / "AGENTS.md"

PATHC_OPEN_PROPS: List[Tuple[str, str]] = [
    # (Prop name, file relative to repo root) — file:line resolved below.
    ("BrunGoldbachLocalMainTermRefinedAtSqrtKernel",
     "Gdbh/PathC_LocalMainTermRefinedAtSqrtClosure.lean"),
    ("SingularSeriesMertens3Bound",
     "Gdbh/PathC_BrunGoldbachSingularSeries.lean"),
    ("AtSqrtFixAStrongToUniversal",
     "Gdbh/PathC_FullChainAudit.lean"),
    ("WeightedSchnirelmannResidualBridge",
     "Gdbh/PathC_UnconditionalFixAStrong.lean"),
]

PATHC_OPEN_PROP_BLURB = {
    "BrunGoldbachLocalMainTermRefinedAtSqrtKernel":
        "Halberstam-Richert §3.11 master sieve inequality at z = √n",
    "SingularSeriesMertens3Bound":
        "Averaged Mertens-3 on the HL singular series (pointwise is FALSE — catch #14)",
    "AtSqrtFixAStrongToUniversal":
        "FixA' universal-in-z upgrade (uniform Brun-Bonferroni over z)",
    "WeightedSchnirelmannResidualBridge":
        "FixA' → original Refined absorption (weighted Schnirelmann + (log log n)²)",
}

HEADLINES = [
    ("Gdbh.strongGoldbach_under_RH_phase5_reduced",
     "Gdbh.PathA_Final",
     "Gdbh/PathA_Final.lean",
     re.compile(r"^theorem\s+strongGoldbach_under_RH_phase5_reduced\b")),
    ("Gdbh.PathCKGoldbachUnconditional.pathC_kGoldbach_unconditional",
     "Gdbh.PathC_KGoldbachUnconditional",
     "Gdbh/PathC_KGoldbachUnconditional.lean",
     re.compile(r"^theorem\s+pathC_kGoldbach_unconditional(?:\s|$)")),
]

EXPECTED_AXIOMS = "[propext, Classical.choice, Quot.sound]"


def normalize_axioms(s: str) -> str:
    """Lean sometimes prints axioms across lines; collapse to canonical form."""
    return re.sub(r"\s+", " ", s).strip()


def grep_line(path: Path, needle) -> Optional[int]:
    """Locate first line matching `needle`. Accepts a literal substring or a
    pre-compiled regex (matched against the line, stripped of trailing nl)."""
    if not path.exists():
        return None
    is_regex = isinstance(needle, re.Pattern)
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for i, line in enumerate(f, start=1):
            stripped = line.rstrip("\n")
            if is_regex:
                if needle.match(stripped):
                    return i
            else:
                if needle in stripped:
                    return i
    return None


def grep_def_line(path: Path, prop_name: str) -> Optional[int]:
    """Find the line declaring `def <prop_name> :` or similar."""
    if not path.exists():
        return None
    pattern = re.compile(
        rf"^(def|structure|theorem|lemma|abbrev)\s+{re.escape(prop_name)}\b"
    )
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for i, line in enumerate(f, start=1):
            if pattern.match(line):
                return i
    return None


def parse_patha_open_props() -> List[str]:
    src = (GDBH / "PathA_StatusPhase24.lean")
    if not src.exists():
        return []
    text = src.read_text(encoding="utf-8", errors="replace")
    m = re.search(
        r"def\s+PathA_GenuineOpenProps\s*:\s*List\s+String\s*:=\s*\[(.*?)\]",
        text,
        re.DOTALL,
    )
    if not m:
        return []
    body = m.group(1)
    return re.findall(r'"([^"]+)"', body)


PATHA_OPEN_PROP_BLURB = {
    "psiBound": ("P5-T1", "RH-conditional ψ square-root error"),
    "pageLogDistance": ("P5-T2", "classical Page zero-free region"),
    "siegelAlone": ("P5-T2", "classical Siegel zero"),
    "pntRemainder": ("P5-T2", "classical PNT with remainder"),
    "uniformPlancherel": ("P5-T3", "uniform Plancherel + char orthogonality"),
    "typeIUnconditional": ("P5-T5", "classical Vinogradov Type I"),
    "typeIIUnconditional": ("P5-T5", "classical Vinogradov Type II"),
    "typeIIIUnconditional": ("P5-T5", "classical Vinogradov Type III"),
    "minorArcVinogradov": ("P5-T6", "classical minor-arc bilinear bound"),
}


def parse_false_prop_catches() -> List[Tuple[str, str, str]]:
    """Return list of (task, prop, resolution) tuples."""
    src = GDBH / "PathC_FinalSummaryPhase22.lean"
    if not src.exists():
        return []
    text = src.read_text(encoding="utf-8", errors="replace")
    m = re.search(
        r"def\s+FalsePropCatchList\s*:\s*List\s+FalsePropCatch\s*:=\s*\[(.*?)\n\s*\]",
        text,
        re.DOTALL,
    )
    if not m:
        return []
    body = m.group(1)
    catches = []
    for entry in re.finditer(
        r"task\s*:=\s*\"([^\"]+)\"\s*,\s*prop\s*:=\s*\"([^\"]+)\""
        r"\s*,\s*resolution\s*:=\s*\"([^\"]+)\"",
        body,
    ):
        catches.append((entry.group(1), entry.group(2), entry.group(3)))
    return catches


def count_files_and_lines() -> Tuple[int, int]:
    files = list(GDBH.rglob("*.lean"))
    total_lines = 0
    for f in files:
        try:
            with f.open("rb") as fh:
                total_lines += sum(1 for _ in fh)
        except OSError:
            pass
    return len(files), total_lines


def run_print_axioms() -> List[Tuple[str, str]]:
    """Returns list of (theorem_name, axioms_or_error)."""
    lean_input_lines = []
    seen = set()
    for theorem, module, _, _ in HEADLINES:
        if module not in seen:
            lean_input_lines.append(f"import {module}")
            seen.add(module)
    for theorem, _, _, _ in HEADLINES:
        lean_input_lines.append(f"#print axioms {theorem}")
    lean_input = "\n".join(lean_input_lines) + "\n"

    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.exists():
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            input=lean_input,
            cwd=REPO_ROOT,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=360,
            text=True,
        )
    except FileNotFoundError:
        return [(t, "lake not on PATH — run `source $HOME/.elan/env` first")
                for t, _, _, _ in HEADLINES]
    except subprocess.TimeoutExpired:
        return [(t, "TIMEOUT after 180s") for t, _, _, _ in HEADLINES]

    out = (result.stdout or "") + (result.stderr or "")
    parsed = []
    for theorem, _, _, _ in HEADLINES:
        m = re.search(
            rf"'{re.escape(theorem)}' depends on axioms:\s*(\[[^\]]*\])",
            out,
            re.DOTALL,
        )
        if m:
            parsed.append((theorem, normalize_axioms(m.group(1))))
        else:
            head_err = out.strip().splitlines()[-3:] if out.strip() else []
            parsed.append((theorem, "NOT FOUND — see lake output: "
                           + " | ".join(head_err)[:160]))
    return parsed


def fmt_headlines_section(axioms: List[Tuple[str, str]]) -> str:
    lines = [
        "| Theorem | File:Line | `#print axioms` |",
        "|---|---|---|",
    ]
    for (theorem, _, rel_path, locator), (_, ax) in zip(HEADLINES, axioms):
        full = REPO_ROOT / rel_path
        ln = grep_line(full, locator)
        loc = f"`{rel_path}:{ln}`" if ln else f"`{rel_path}` (line not located)"
        clean_marker = "✅" if ax == EXPECTED_AXIOMS else "⚠️"
        lines.append(f"| `{theorem}` | {loc} | {clean_marker} `{ax}` |")
    return "\n".join(lines)


def fmt_pathc_open_props_section() -> str:
    lines = [
        "| # | Name | File:Line | Meaning |",
        "|---|---|---|---|",
    ]
    for i, (prop, rel_path) in enumerate(PATHC_OPEN_PROPS, start=1):
        full = REPO_ROOT / rel_path
        ln = grep_def_line(full, prop)
        loc = f"`{rel_path}:{ln}`" if ln else f"`{rel_path}` (TODO: locate)"
        blurb = PATHC_OPEN_PROP_BLURB.get(prop, "")
        lines.append(f"| {i} | `{prop}` | {loc} | {blurb} |")
    return "\n".join(lines)


def fmt_patha_open_props_section(props: Iterable[str]) -> str:
    items = list(props)
    if not items:
        return "_(parse failed — check Gdbh/PathA_StatusPhase24.lean `PathA_GenuineOpenProps`)_"
    lines = ["| # | Name | Task | Description |", "|---|---|---|---|"]
    for i, p in enumerate(items, start=1):
        task, desc = PATHA_OPEN_PROP_BLURB.get(p, ("?", ""))
        lines.append(f"| {i} | `{p}` | {task} | {desc} |")
    return "\n".join(lines)


def fmt_false_props_section(catches: List[Tuple[str, str, str]]) -> str:
    if not catches:
        return "_(parse failed — check Gdbh/PathC_FinalSummaryPhase22.lean `FalsePropCatchList`)_"
    lines = ["| # | Task | False Prop | Resolution |", "|---|---|---|---|"]
    for i, (task, prop, resolution) in enumerate(catches, start=1):
        prop_s = prop.replace("|", "\\|")
        res_s = resolution.replace("|", "\\|")
        lines.append(f"| {i} | {task} | {prop_s} | {res_s} |")
    return "\n".join(lines)


def fmt_stats_section(file_count: int, line_count: int) -> str:
    return (f"- `.lean` files under `Gdbh/`: **{file_count}**\n"
            f"- Total lines (incl. comments / blank): **{line_count:,}**")


def fmt_header_section() -> str:
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%MZ")
    return (f"_Last auto-regenerated: **{now}** by "
            f"`scripts/regenerate_agents_md.py`. Manual edits to AUTO sections "
            f"will be overwritten — edit prose outside the markers._")


MARKER_PATTERN = re.compile(
    r"(<!-- AUTO:(?P<name>[A-Z_]+) -->)(.*?)(<!-- /AUTO:(?P=name) -->)",
    re.DOTALL,
)


def replace_section(text: str, name: str, new_content: str) -> Tuple[str, bool]:
    found = [False]

    def sub(match: re.Match[str]) -> str:
        if match.group("name") != name:
            return match.group(0)
        found[0] = True
        return f"{match.group(1)}\n{new_content}\n{match.group(4)}"

    new_text = MARKER_PATTERN.sub(sub, text)
    return new_text, found[0]


def main() -> int:
    if not AGENTS.exists():
        print(f"ERROR: {AGENTS} not found — create it with AUTO markers first.",
              file=sys.stderr)
        return 2

    text = AGENTS.read_text(encoding="utf-8")
    patha_open = parse_patha_open_props()
    false_catches = parse_false_prop_catches()
    file_count, line_count = count_files_and_lines()
    axioms = run_print_axioms()

    sections = {
        "HEADER": fmt_header_section(),
        "HEADLINES": fmt_headlines_section(axioms),
        "PATHC_OPEN_PROPS": fmt_pathc_open_props_section(),
        "PATHA_OPEN_PROPS": fmt_patha_open_props_section(patha_open),
        "FALSE_PROPS": fmt_false_props_section(false_catches),
        "STATS": fmt_stats_section(file_count, line_count),
    }

    summary = []
    for name, content in sections.items():
        text, found = replace_section(text, name, content)
        if found:
            summary.append(f"  ✓ AUTO:{name}")
        else:
            summary.append(f"  ✗ AUTO:{name} (marker not found in AGENTS.md)")

    AGENTS.write_text(text, encoding="utf-8")
    print(f"AGENTS.md regenerated ({file_count} files, {line_count:,} lines).")
    for line in summary:
        print(line)
    bad = [t for t, a in axioms if a != EXPECTED_AXIOMS]
    if bad:
        print("WARNING: headline axiom mismatch:")
        for t in bad:
            print(f"  - {t}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
