#!/usr/bin/env bash
# Standalone Lean-file audit for Gdbh.
#
# `lake build` checks the import graph rooted at the lake targets.  This
# script also runs `lake env lean <file>` on files that may not be covered by
# the root barrel, so experimental files cannot silently drift.
#
# Usage:
#   scripts/audit_standalone_lean.sh
#   scripts/audit_standalone_lean.sh --all
#   scripts/audit_standalone_lean.sh --timeout 180

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

MODE="orphans"
TIMEOUT_SECONDS=120
REPORT="${REPO_ROOT}/scripts/audit_standalone_lean_report.txt"
LIST_ONLY=0
EXCLUDE_REGEX=""

usage() {
  cat <<'USAGE'
Usage: scripts/audit_standalone_lean.sh [--orphans-only|--all] [--timeout SECONDS]
                                        [--list-targets] [--exclude REGEX]

Modes:
  --orphans-only   Check Gdbh/*.lean modules not directly imported by Gdbh.lean. Default.
  --all            Check every Lean file under Gdbh/.

Options:
  --timeout N      Per-file timeout in seconds. Default: 120.
  --list-targets   Print target files/modules without running Lean.
  --exclude REGEX  Skip target files whose path or module matches REGEX.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --orphans-only)
      MODE="orphans"
      shift
      ;;
    --all)
      MODE="all"
      shift
      ;;
    --timeout)
      if [[ $# -lt 2 ]]; then
        usage
        exit 2
      fi
      TIMEOUT_SECONDS="$2"
      shift 2
      ;;
    --list-targets)
      LIST_ONLY=1
      shift
      ;;
    --exclude)
      if [[ $# -lt 2 ]]; then
        usage
        exit 2
      fi
      EXCLUDE_REGEX="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      usage
      exit 2
      ;;
  esac
done

if [[ -f "${HOME}/.elan/env" ]]; then
  # shellcheck source=/dev/null
  source "${HOME}/.elan/env"
fi

module_of_file() {
  local file="$1"
  file="${file%.lean}"
  file="${file//\//.}"
  printf '%s\n' "${file}"
}

file_of_module() {
  local module="$1"
  module="${module//.//}"
  printf '%s.lean\n' "${module}"
}

run_with_timeout() {
  local seconds="$1"
  shift
  perl -e 'alarm shift; exec @ARGV' "${seconds}" "$@"
}

TMP_ALL="$(mktemp)"
TMP_IMPORTS="$(mktemp)"
TMP_TARGETS="$(mktemp)"
TMP_OUT="$(mktemp)"
trap 'rm -f "${TMP_ALL}" "${TMP_IMPORTS}" "${TMP_TARGETS}" "${TMP_OUT}"' EXIT

find Gdbh -type f -name '*.lean' | LC_ALL=C sort > "${TMP_ALL}"
rg '^import Gdbh\.' Gdbh.lean | sed 's/^import //' | LC_ALL=C sort > "${TMP_IMPORTS}"

if [[ "${MODE}" == "all" ]]; then
  cp "${TMP_ALL}" "${TMP_TARGETS}"
else
  while IFS= read -r file; do
    module="$(module_of_file "${file}")"
    if ! grep -Fxq "${module}" "${TMP_IMPORTS}"; then
      printf '%s\n' "${file}" >> "${TMP_TARGETS}"
    fi
  done < "${TMP_ALL}"
fi

if [[ -n "${EXCLUDE_REGEX}" ]]; then
  TMP_FILTERED="$(mktemp)"
  trap 'rm -f "${TMP_ALL}" "${TMP_IMPORTS}" "${TMP_TARGETS}" "${TMP_OUT}" "${TMP_FILTERED}"' EXIT
  while IFS= read -r file; do
    module="$(module_of_file "${file}")"
    if [[ "${file}" =~ ${EXCLUDE_REGEX} ]] || [[ "${module}" =~ ${EXCLUDE_REGEX} ]]; then
      continue
    fi
    printf '%s\n' "${file}" >> "${TMP_FILTERED}"
  done < "${TMP_TARGETS}"
  mv "${TMP_FILTERED}" "${TMP_TARGETS}"
fi

: > "${REPORT}"
{
  printf 'Standalone Lean audit\n'
  printf 'Repository: %s\n' "${REPO_ROOT}"
  printf 'Mode:       %s\n' "${MODE}"
  printf 'Timeout:    %ss per file\n' "${TIMEOUT_SECONDS}"
  printf 'Report:     %s\n\n' "${REPORT}"
} | tee -a "${REPORT}"

total="$(wc -l < "${TMP_TARGETS}" | tr -d ' ')"
printf 'Targets:    %s\n\n' "${total}" | tee -a "${REPORT}"

if [[ "${LIST_ONLY}" -eq 1 ]]; then
  while IFS= read -r file; do
    module="$(module_of_file "${file}")"
    printf '%s  %s\n' "${module}" "${file}" | tee -a "${REPORT}"
  done < "${TMP_TARGETS}"
  exit 0
fi

failures=0
timeouts=0
checked=0

while IFS= read -r file; do
  checked=$((checked + 1))
  module="$(module_of_file "${file}")"
  printf '[%s/%s] %s ... ' "${checked}" "${total}" "${module}" | tee -a "${REPORT}"
  : > "${TMP_OUT}"
  if run_with_timeout "${TIMEOUT_SECONDS}" lake env lean "${file}" > "${TMP_OUT}" 2>&1; then
    printf 'OK\n' | tee -a "${REPORT}"
  else
    rc=$?
    failures=$((failures + 1))
    if [[ "${rc}" -eq 142 ]]; then
      timeouts=$((timeouts + 1))
      printf 'TIMEOUT\n' | tee -a "${REPORT}"
    else
      printf 'FAIL rc=%s\n' "${rc}" | tee -a "${REPORT}"
    fi
    {
      printf '%s\n' '--- output begin ---'
      sed -n '1,220p' "${TMP_OUT}"
      printf '%s\n' '--- output end ---'
    } >> "${REPORT}"
  fi
done < "${TMP_TARGETS}"

{
  printf '\nSummary\n'
  printf '  checked:  %s\n' "${checked}"
  printf '  failures: %s\n' "${failures}"
  printf '  timeouts: %s\n' "${timeouts}"
} | tee -a "${REPORT}"

if [[ "${failures}" -eq 0 ]]; then
  exit 0
fi

exit 1
