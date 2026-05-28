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
8. `Gdbh/PathC_ResidueRemainderIntersectionSplit.lean`
9. `Gdbh/PathC_ResidueRemainderSharedPrimeWitness.lean`
10. `Gdbh/PathC_ResidueRemainderWitnessDivisorPartition.lean`

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

Latest verified mathematical round in the scoreboard is Round 79.

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

Round 77 added the shared-prime intersection split:

- `Gdbh/PathC_ResidueRemainderIntersectionSplit.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeIntersectionRemainderLogSquaredUpperEventually
  => ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderLogSquaredUpperEventually
  => ResidueRemainderLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The new shared-prime branch is:

```text
if d1 inter d2 = empty then 0
else if (d1 inter d2).prod id divides n then
  residuePairCountingRemainder n d1 d2
else 0
```

It is connected to the Round75 non-coprime compatible branch by:

```text
residueNonCoprimeCompatiblePairCountingRemainder_eq_sharedPrimeIntersection
residueDoubleDivisorNonCoprimeCompatibleRemainderSum_eq_sharedPrimeIntersection
residueNonCoprimeCompatibleRemainderLogSquaredUpperEventually_of_sharedPrimeIntersection
residueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually_of_intersectionSplit
pathC_kGoldbach_of_compatibleRemainderIntersectionSplit_and_countingInput
```

Round 78 added the witness-supported shared-prime split:

- `Gdbh/PathC_ResidueRemainderSharedPrimeWitness.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeWitnessRemainderLogSquaredUpperEventually
  => ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderLogSquaredUpperEventually
  => ResidueRemainderLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The witness-supported pair branch is:

```text
if exists p, p in d1 inter d2 and p divides n then
  residueSharedPrimeIntersectionPairCountingRemainder n d1 d2
else 0
```

Key bridges:

```text
residueSharedPrimeIntersection_prime_dvd_of_prod_dvd
residueSharedPrimeIntersectionPairCountingRemainder_eq_witness
residueDoubleDivisorSharedPrimeIntersectionRemainderSum_eq_witness
residueSharedPrimeIntersectionRemainderLogSquaredUpperEventually_of_witness
residueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually_of_witnessSplit
pathC_kGoldbach_of_compatibleRemainderWitnessSplit_and_countingInput
```

Round 79 added the divisor-filter witness support:

- `Gdbh/PathC_ResidueRemainderWitnessDivisorPartition.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually
  => ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderCoprimeSplitLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The finite support is:

```text
residuePrimeDivisorWitnessSet n z =
  (residuePrimeSet z).filter (fun p => p divides n)
```

Key bridges:

```text
residueSharedPrimeWitnessCondition_iff_primeDivisorWitness
residueSharedPrimeWitnessPairCountingRemainder_eq_divisorWitness
residueDoubleDivisorSharedPrimeWitnessRemainderSum_eq_divisorWitness
residueSharedPrimeWitnessRemainderLogSquaredUpperEventually_of_divisorWitness
residueCompatibleRemainderWitnessSplitLogSquaredUpperEventually_of_divisorWitnessSplit
pathC_kGoldbach_of_compatibleRemainderDivisorWitnessSplit_and_countingInput
```

This is a support/filter normalization, not a disjoint sum over witnesses.
A divisor pair can have multiple shared prime witnesses.

Round 79 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessDivisorPartition.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 277 Lean files with no banned project assumptions or
placeholders.  The full audit reported 276 Lean files under `Gdbh/`, 235,879
lines, 7,421 theorem/lemma declarations, 3,078 definitions, zero genuine `sorry` or
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

No Lean mathematical change has been made after Round 79.

## Suggested Next Round

Continue with Round 80.

Primary candidate:

```text
Candidate: divisor-witness cover inequality
  Goal: bound the witness-supported branch by a finite cover over
        residuePrimeDivisorWitnessSet n z, explicitly allowing overlaps
  ExpectedDelta: about 36-40
  Risk: moderate, because it needs absolute values and finite-cover bookkeeping
  Execute if Lean proof is small and additive
```

Reason:

Round79 made the finite divisor witness support explicit:

```text
residuePrimeDivisorWitnessSet n z =
  (residuePrimeSet z).filter (fun p => p divides n)
```

The next useful decomposition is a finite cover/upper-bound statement over
this set.  Avoid claiming a disjoint sum over witnesses, because a pair can
have multiple shared primes.  The safe shape is an absolute-value cover bound
or a support inclusion that explicitly allows overlap.

Possible additive file:

```text
Gdbh/PathC_ResidueRemainderWitnessCover.lean
```

Possible public theorems:

```text
residueSharedPrimeDivisorWitnessPair_abs_le_coverSum
residueDoubleDivisorSharedPrimeDivisorWitness_abs_le_coverSum
ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually
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

Then start Round 80 with the master-controller workflow above.
