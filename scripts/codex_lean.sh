#!/usr/bin/env bash
# codex_lean.sh — opinionated wrapper for invoking codex on the Goldbach project.
#
# What it does:
#   1. Sources ~/.elan/env so `lake` / `lean` are on PATH inside the codex sandbox.
#   2. Asserts AGENTS.md exists at repo root.
#   3. Wraps the user's prompt with the project's invariants (read AGENTS.md,
#      axiom hygiene, banned tokens, regen on exit).
#   4. Pipes through `codex exec --profile lean -C <repo>`.
#   5. After codex returns, runs the AGENTS.md regenerator and reports.
#
# Usage:
#   ./scripts/codex_lean.sh "Attack BrunGoldbachLocalMainTermRefinedAtSqrtKernel."
#   ./scripts/codex_lean.sh -f extra-context.md "Decompose AtSqrtFixAStrongToUniversal."
#
# Options (forwarded to codex exec verbatim before the prompt):
#   --image FILE         attach an image
#   -o, --output FILE    write final message to FILE
#   --json               JSONL event stream
#   anything else        forwarded
#
# The actual prompt is ALWAYS the LAST positional argument; everything before
# it is forwarded to codex.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

if [ ! -f "${REPO_ROOT}/AGENTS.md" ]; then
  echo "ERROR: ${REPO_ROOT}/AGENTS.md not found." >&2
  echo "       Did you delete it? The project relies on it." >&2
  exit 2
fi

# Make lake / lean available inside the codex workspace-write sandbox.
if [ -f "${HOME}/.elan/env" ]; then
  # shellcheck disable=SC1091
  . "${HOME}/.elan/env"
fi

# Default proxy (in case the shell didn't export it).
: "${HTTPS_PROXY:=http://127.0.0.1:1097}"
: "${HTTP_PROXY:=${HTTPS_PROXY}}"
export HTTPS_PROXY HTTP_PROXY

if [ "$#" -lt 1 ]; then
  echo "Usage: $0 [codex-exec-flags…] \"<prompt>\"" >&2
  exit 1
fi

# The user's prompt is the last argument; everything before it is forwarded.
USER_PROMPT="${@: -1}"
set -- "${@:1:$#-1}"

WRAPPED_PROMPT=$(cat <<EOF
You are working on the Lean 4 Binary Goldbach formalization at ${REPO_ROOT}.

Step 0 (mandatory): read AGENTS.md in full before doing anything else.
The 4 PathC named open Props, 9 PathA named open Props, 15 false-Prop
blacklist, axiom-hygiene rules, and banned tokens are all defined there.

Hard constraints (non-negotiable):
- Banned tokens in Gdbh/: sorry, admit, axiom, opaque, constant, unsafe.
- Every closed theorem on the headline chain must have
  '#print axioms' = [propext, Classical.choice, Quot.sound]. Anything else
  is a regression — revert.
- No trivial-witness exploitation (k=0, C=∞, S=∅, …) to satisfy ∃.
- Do not edit Gdbh/PathA_Final.lean or Gdbh/PathC_KGoldbachUnconditional.lean
  unless the diff is strictly additive (new theorem at end).
- Before any inequality of the form f(n) ≤ g(n) · (log log n)^k, verify
  numerically at n ∈ {6, 30, 210, 2310, 30030, 510510, 9699690}. If it fails
  at any primorial, the Prop is false — document and stop.

Workflow:
1. Identify the target Prop and quote its literal Lean statement.
2. Check FalsePropCatchList in Gdbh/PathC_FinalSummaryPhase22.lean.
3. Primorial sanity check (Python one-liner).
4. Decompose into ≥1 strictly smaller named sub-Prop in a NEW attempt file
   (Gdbh/<Path>_<Name>Attempt.lean).
5. Attempt closure or honest-catch.
6. Verify: lake build && python3 audit_lean_source.py && per-theorem #print axioms.
7. MANDATORY: run \`python3 scripts/regenerate_agents_md.py\` to refresh
   the AUTO sections of AGENTS.md.

Task from user:

${USER_PROMPT}

Reminder before you finish: run the regen script. If it exits non-zero,
investigate the headline axiom mismatch before claiming success.
EOF
)

echo ">>> codex exec --profile lean -C ${REPO_ROOT} $* <wrapped-prompt>"
echo "---"

# shellcheck disable=SC2068
codex exec --profile lean -C "${REPO_ROOT}" $@ "${WRAPPED_PROMPT}"
CODEX_STATUS=$?

echo ""
echo "--- codex exited with status ${CODEX_STATUS}, running AGENTS.md regen ---"
if ! python3 "${REPO_ROOT}/scripts/regenerate_agents_md.py"; then
  echo "WARNING: regen reported axiom mismatch — review AGENTS.md and codex output above." >&2
fi

exit "${CODEX_STATUS}"
