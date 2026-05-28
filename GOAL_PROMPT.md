# Goal Prompt

This repository is the working tree for a Lean 4 / mathlib v4.29.1 attack on
Binary Goldbach, with Path C currently emphasized.

## Active Controller Goal

Use a master-controller workflow with up to 4 concurrent subagents to attack
the Path C open Props in `/Users/tommy/Downloads/gdbh`, preserving
`AGENTS.md` constraints, decomposing named sub-Props, keeping file-write
isolation, and verifying with Lean audits after any Lean edits.

## Operating Rules

- Maintain a score/expected-delta before executing a candidate task.
- Continue only work that plausibly improves the final target.
- Prefer decomposition into strictly smaller named sub-Props before proof
  attempts.
- Keep each agent's writes isolated to its own file.
- Subagents may spawn child or grandchild agents for score-positive work with
  a clear report path. There is no mandatory close step after dispatch.
- Preserve axiom hygiene: headline theorems must remain exactly
  `[propext, Classical.choice, Quot.sound]`.
- Keep `Gdbh/` free of genuine `sorry`, `admit`, `axiom`, `opaque`,
  `constant`, and `unsafe`.
- After Lean edits, run the project verification chain described in
  `AGENTS.md`, including `python3 scripts/regenerate_agents_md.py`.

## Canonical Project Guidance

- `AGENTS.md` is the authoritative agent instruction file for this repository.
- `goal.md` contains the long-form mission prompt and multi-vector attack plan.
- `pathc_master_scoreboard.md` records the controller's score decisions,
  residual decomposition, and verification history.

## Current Honest Status

This project is an axiom-clean formalization attempt with two headline paths,
not a completed proof of Binary Goldbach. The current headline theorems remain
clean only modulo the named open analytic Props documented in `AGENTS.md`.
