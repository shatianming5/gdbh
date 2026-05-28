# Resume For cpudev Codex

Generated from local workspace `/Users/tommy/Downloads/gdbh`.

## Repository

- GitHub: `https://github.com/shatianming5/gdbh`
- Branch: `main`
- Latest local/remote commit at handoff: run `git log -1 --oneline` after pull
- Visibility at handoff: private
- Local caches are intentionally excluded by `.gitignore`: `.lake/`,
  Python caches, and Lean build artifacts.

## What To Read First

1. `AGENTS.md`
2. `Agent.md` (compatibility copy of `AGENTS.md`)
3. `GOAL_PROMPT.md`
4. `goal.md`
5. `pathc_master_scoreboard.md`
6. `Gdbh/PathC_ResidueRemainderCoprimeSplit.lean`
7. `Gdbh/PathC_ResiduePrimeSetProductSupport.lean`

## Active Goal

Use a master-controller workflow with up to 4 concurrent subagents to attack
the Path C open Props, preserving `AGENTS.md` constraints, decomposing named
sub-Props, keeping file-write isolation, and verifying with Lean audits after
any Lean edits.

Do not mark the goal complete unless the full objective is actually achieved
and verified. Do not mark it blocked merely because a subagent/thread limit or
hard mathematics makes progress slow.

## Controller Rules To Preserve

- Maintain an explicit score/expected-delta for candidate work.
- Execute only score-positive work that improves the final Path C target.
- Decompose every ambitious Prop into strictly smaller named sub-Props before
  proof attempts.
- Keep file-write isolation. Add new Lean files instead of casually editing
  headline files.
- Subagents may spawn child/grandchild agents if the work is score-positive,
  non-overlapping, and has a report path back to the parent.
- Do not close useful subagents merely to free slots.
- Preserve headline axiom hygiene exactly:
  `[propext, Classical.choice, Quot.sound]`.
- Keep `Gdbh/` free of genuine `sorry`, `admit`, `axiom`, `opaque`,
  `constant`, and `unsafe`.
- After any `Gdbh/*.lean` edit, run:

```bash
source "$HOME/.elan/env"
lake build
python3 audit_lean_source.py
bash scripts/audit_full.sh
python3 scripts/regenerate_agents_md.py
```

Use targeted `#print axioms` probes for individual theorems. Do not run
`audit_lean_axioms.py`.

## Current Verified State

Latest verified mathematical round in the scoreboard is Round 76.

Round 75 added the coprime/non-coprime compatible-remainder split:

- `Gdbh/PathC_ResidueRemainderCoprimeSplit.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    ∧ ResidueNonCoprimeCompatibleRemainderLogSquaredUpperEventually
  => ResidueCompatibleRemainderLogSquaredUpperEventually
  => ResidueRemainderLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

Round 76 added public residue-prime product support:

- `Gdbh/PathC_ResiduePrimeSetProductSupport.lean`
- import in `Gdbh.lean`
- reusable theorem cluster:

```text
residuePrimeSubset_gcd_prod_eq_prod_inter
residuePrimeSubset_lcm_prod_eq_prod_union
residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd
residuePrimeSubset_coprime_iff_inter_eq_empty
```

These normalize products of finite residue-prime subsets into intersection
and union statements.  They are intended to support the Round75 coprime and
shared-prime compatible-remainder workers.

Round 76 verification passed:

- `lake env lean Gdbh/PathC_ResiduePrimeSetProductSupport.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The full audit reported 273 Lean files under `Gdbh/`, 235,122 lines, 7,392
theorem/lemma declarations, 3,059 definitions, zero genuine `sorry` or
`admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

## Most Recent Non-Math Work

The repository was initialized locally, pushed to GitHub, and then updated
with a compatibility copy:

- `Agent.md` is a byte-identical copy of `AGENTS.md`.
- `GOAL_PROMPT.md` records the active controller goal.
- `README.md` has a top-level navigation and reproduction section.
- `.gitignore` excludes local build/dependency caches.

`Agent.md` should remain a compatibility copy of `AGENTS.md` after each
regeneration.

No Lean mathematical change has been made after Round 76.

## Suggested Next Round

Continue with Round 77.

Primary candidate:

```text
Candidate: non-coprime compatible remainder intersection split
  Goal: split shared-prime remainder by a nonempty intersection witness and reuse
        residuePrimeSubset_coprime_iff_inter_eq_empty
  ExpectedDelta: about 40
  Risk: low-to-moderate, mostly finite-set algebra
  Execute if Lean proof is small and additive
```

Reason:

Round76 made these product-support facts public:

```text
Nat.gcd (d1.prod id) (d2.prod id) = (d1 inter d2).prod id
Nat.lcm (d1.prod id) (d2.prod id) = (d1 union d2).prod id
Nat.Coprime (d1.prod id) (d2.prod id) <-> d1 inter d2 = empty
```

The next useful decomposition is to expose the non-coprime compatible
remainder as a finite union or sum indexed by a nonempty shared prime
intersection.  Keep it as a named worker Prop first; do not attempt the full
log-squared analytic bound in the same step.

Possible additive file:

```text
Gdbh/PathC_ResidueRemainderIntersectionSplit.lean
```

Possible public theorems:

```text
residueNonCoprimeCompatiblePairCountingRemainder_eq_sharedPrimeSum
residueNonCoprimeCompatibleRemainderIntersectionSplitUpperEventually
residueCompatibleRemainderCoprimeSplit_of_intersectionSplit
```

Secondary candidate:

```text
Candidate: coprime CRT discrepancy worker normalization
  Goal: isolate the coprime compatible-pair remainder into a CRT-counting Prop
  Risk: moderate because it touches the bridge to counting input
```

Avoid:

- Directly proving the log-squared analytic upper bound in one jump.
- Any pointwise `S(n) <= K * log log n` style bound.
- Any naive `n / (log n)^2` Brun main-term claim.

## cpudev Usage

If continuing on cpudev, either clone/pull the GitHub repo or use the uploaded
workspace path if one was created. Then run:

```bash
cd /path/to/gdbh
source "$HOME/.elan/env"
git status --short --branch
sed -n '1,140p' AGENTS.md
tail -n 260 pathc_master_scoreboard.md
```

Then start Round 77 with the master-controller workflow above.
