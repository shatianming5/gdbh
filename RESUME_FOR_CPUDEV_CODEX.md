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
11. `Gdbh/PathC_ResidueRemainderWitnessCover.lean`
12. `Gdbh/PathC_ResidueRemainderWitnessCoverRearrange.lean`
13. `Gdbh/PathC_ResidueRemainderWitnessCoverFiltered.lean`
14. `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelope.lean`
15. `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelopeApplications.lean`

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

Latest verified mathematical round in the scoreboard is Round 84.

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

Round 80 added the finite cover worker:

- `Gdbh/PathC_ResidueRemainderWitnessCover.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeWitnessCoverLogSquaredUpperEventually
  => ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderWitnessSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderIntersectionSplitLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The cover inequalities are:

```text
abs (residueSharedPrimeDivisorWitnessPairCountingRemainder n z d1 d2)
  <= residueSharedPrimeDivisorWitnessPairCover n z d1 d2

abs (residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum n z k)
  <= residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum n z k
```

Key bridges:

```text
residueSharedPrimeDivisorWitnessPair_abs_le_cover
residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSum_abs_le_coverSum
residueDoubleDivisorSharedPrimeDivisorWitnessRemainderSumAtSqrt_abs_le_coverSum
residueSharedPrimeDivisorWitnessRemainderLogSquaredUpperEventually_of_cover
residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_coverSplit
pathC_kGoldbach_of_compatibleRemainderWitnessCoverSplit_and_countingInput
```

This is a nonnegative finite cover, not a disjoint partition over witnesses.

Round 81 added the prime-first cover rearrangement:

- `Gdbh/PathC_ResidueRemainderWitnessCoverRearrange.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually
  => ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The cover equality is:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum n z k
  =
residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum n z k
```

The prime-first form still has the indicator `if p in d1 inter d2`; it is not
a disjoint witness decomposition.

Key bridges:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessCoverSum_eq_primeFirst
residueDoubleDivisorSharedPrimeDivisorWitnessCoverSumAtSqrt_eq_primeFirst
residueSharedPrimeWitnessCoverLogSquaredUpperEventually_of_primeFirst
residueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually_of_primeFirstSplit
residueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually_of_primeFirstSplit
pathC_kGoldbach_of_compatibleRemainderPrimeFirstCoverSplit_and_countingInput
```

Round 81 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverRearrange.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 279 Lean files with no banned project assumptions or
placeholders.  The full audit reported 278 Lean files under `Gdbh/`, 236,407
lines, 7,436 theorem/lemma declarations, 3,089 definitions, zero genuine `sorry` or
`admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

Round 82 added the filtered-support prime-first cover:

- `Gdbh/PathC_ResidueRemainderWitnessCoverFiltered.lean`
- import in `Gdbh.lean`
- active worker:

```text
ResidueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually
  = ResidueCoprimeCompatibleRemainderLogSquaredUpperEventually
    and ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually
  => ResidueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderWitnessCoverSplitLogSquaredUpperEventually
  => ResidueCompatibleRemainderDivisorWitnessSplitLogSquaredUpperEventually
  => ...
  => Path C K-Goldbach
```

The filtered family is:

```text
residueWitnessContainingDivisorFamily z k p =
  ((residuePrimeSet z).powerset.filter (fun d => d.card <= k)).filter
    (fun d => p in d)
```

The cover equality is:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum n z k
  =
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum n z k
```

The filtered form remains an overlapping witness-prime cover:

```text
sum p in residuePrimeDivisorWitnessSet n z,
  sum d1 in residueWitnessContainingDivisorFamily z k p,
    sum d2 in residueWitnessContainingDivisorFamily z k p,
      |mu d1 * mu d2| * |pairRemainder n d1 d2|
```

Key bridges:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSum_eq_filtered
residueDoubleDivisorSharedPrimeDivisorWitnessPrimeFirstCoverSumAtSqrt_eq_filtered
residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperAfter_of_filtered
residueSharedPrimeWitnessPrimeFirstCoverLogSquaredUpperEventually_of_filtered
residueCompatibleRemainderPrimeFirstCoverSplitLogSquaredUpperEventually_of_filteredSplit
pathC_kGoldbach_of_compatibleRemainderFilteredCoverSplit_and_countingInput
```

Round 82 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverFiltered.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 280 Lean files with no banned project assumptions or
placeholders.  The full audit reported 279 Lean files under `Gdbh/`, 236,659
lines, 7,442 theorem/lemma declarations, 3,095 definitions, zero genuine `sorry`
or `admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

Round 83 added the filtered-cover cardinal envelope:

- `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelope.lean`
- import in `Gdbh.lean`
- finite multiplier:

```text
residueFilteredCoverCardinalityEnvelope M =
  M * (2^M * 2^M) * 2
```

Key support/cardinality facts:

```text
residueWitnessContainingDivisorFamily_card_le_base
residueWitnessContainingDivisorFamily_card_le_two_pow_of_card_le
residuePrimeDivisorWitnessSet_card_le_of_residuePrimeSet_card_le
```

Main envelope bounds:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum_le_cardinalityEnvelope
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_cardinalityEnvelope
```

The theorem shape is:

```text
if (residuePrimeSet z).card <= M then
  residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum n z k
    <= residueFilteredCoverCardinalityEnvelope M * n
```

This is only a crude finite cardinality envelope.  It is useful as a finite
fallback and support-size normalization, but it is not an analytic
large-range log-squared closure.

Round 83 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelope.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 281 Lean files with no banned project assumptions or
placeholders.  The full audit reported 280 Lean files under `Gdbh/`, 236,995
lines, 7,454 theorem/lemma declarations, 3,096 definitions, zero genuine `sorry`
or `admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

Round 84 added filtered-envelope finite-prefix applications:

- `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelopeApplications.lean`
- import in `Gdbh.lean`
- public cardinal input:

```text
residuePrimeSet_card_le_self
residuePrimeSet_card_le_of_le
```

At-sqrt envelope applications:

```text
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_at_most
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_bound_mul_n_of_sqrt_le_ten_thousand
```

Linear finite-prefix worker:

```text
ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt
ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixWithConstant
residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit
residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixWithConstant_explicit
```

The theorem shape is:

```text
Nat.sqrt n <= N
  =>
residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n
  <= residueFilteredCoverSqrtAtMostEnvelope N * n
```

This is only a linear finite-prefix envelope.  It does not close the eventual
large-range log-squared filtered-cover worker.

Round 84 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverFilteredEnvelopeApplications.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 282 Lean files with no banned project assumptions or
placeholders.  The full audit reported 281 Lean files under `Gdbh/`, 237,128
lines, 7,460 theorem/lemma declarations, 3,099 definitions, zero genuine `sorry`
or `admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

Round 85 added finite-prefix log-squared absorption for the filtered cover:

- `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredFinitePrefix.lean`
- import in `Gdbh.lean`
- public finite log-loss:

```text
residueFilteredCoverFinitePrefixLogLoss N =
  (Real.log (((N + 1) * (N + 1) : Nat) : Real))^2
```

Elementary prefix/log monotonicity layer:

```text
nat_lt_succ_sq_of_sqrt_le
log_nat_sq_le_finitePrefixLogLoss
```

Log-squared finite-prefix worker:

```text
ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt
ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixWithConstant
```

Bridge and explicit envelopes:

```text
residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_of_linear
residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit
residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixWithConstant_explicit
residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_ten_thousand
```

The theorem shape is:

```text
Nat.sqrt n <= N
  =>
filtered cover at sqrt
  <= (residueFilteredCoverSqrtAtMostEnvelope N
        * residueFilteredCoverFinitePrefixLogLoss N)
     * n / (log n)^2
```

for `16 <= n`.  This is still only a bounded-prefix bridge because the
coefficient depends on `N`.

Round 85 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverFilteredFinitePrefix.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 283 Lean files with no banned project assumptions or
placeholders.  The full audit reported 282 Lean files under `Gdbh/`, 237,299
lines, 7,466 theorem/lemma declarations, 3,102 definitions, zero genuine `sorry`
or `admit`, zero axiom declarations, and both headline theorems exactly
`[propext, Classical.choice, Quot.sound]`.

Round 86 added the filtered-cover finite/tail threshold split:

- `Gdbh/PathC_ResidueRemainderWitnessCoverFilteredThresholdSplit.lean`
- import in `Gdbh.lean`
- full-range and threshold-split interfaces:

```text
ResidueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt
ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt
ResidueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit
```

Recombination and equivalence to the existing eventual tail worker:

```text
residueSharedPrimeWitnessFilteredCoverLogSquaredFixedAtSqrt_of_thresholdSplitAtSqrt
residueSharedPrimeWitnessFilteredCoverLogSquaredWithConstant_of_thresholdSplitAtSqrt
residueSharedPrimeWitnessFilteredCoverLogSquaredUpperEventually_of_thresholdSplit
residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplitAtSqrt_of_after
residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_of_eventually
residueSharedPrimeWitnessFilteredCoverLogSquaredThresholdSplit_iff_eventually
```

Final-chain adapter:

```text
ResidueCompatibleRemainderFilteredCoverThresholdSplitLogSquaredUpperEventually
residueCompatibleRemainderFilteredCoverSplitLogSquaredUpperEventually_of_thresholdSplit
pathC_kGoldbach_of_compatibleRemainderFilteredCoverThresholdSplit_and_countingInput
```

Meaning:

```text
existing tail worker at threshold N
  =>
Round85 explicit finite prefix at N + existing tail worker at N
  =>
threshold-split package
```

and the threshold-split package gives back the existing eventual filtered-cover
worker.  This closes the finite side of the split explicitly but leaves the
large-range analytic estimate honest and unchanged.

Round 86 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderWitnessCoverFilteredThresholdSplit.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The source audit scanned 284 Lean files with no banned project assumptions or
placeholders.  The full audit reported 283 Lean files under `Gdbh/`, 237,513
lines, 7,474 theorem/lemma declarations, 3,106 definitions, zero genuine `sorry`
or `admit`, zero axiom declarations, and both headline theorems exactly
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

## Suggested Next Round

Continue with Round 87.

Primary candidate:

```text
Candidate: filtered-cover tail decomposition
  Goal: decompose the remaining
        ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A
        into a strictly smaller weighted witness-prime tail estimate and a
        divisor-family cardinal estimate.
  ExpectedDelta: about 32-36
  Risk: moderate; must not use the crude finite cardinal envelope as a
        large-range log-squared proof
```

Reason:

Round86 proved the bounded-prefix/tail packaging:

```text
existing tail worker at threshold N
  <=>
threshold split with Round85 finite prefix closed
```

The remaining mathematical content is still the tail estimate.  The next useful
step is to decompose that tail into named smaller Props without pretending the
finite cardinal envelope is uniform in the large range.

Possible additive file:

```text
Gdbh/PathC_ResidueRemainderWitnessCoverFilteredTailDecomposition.lean
```

Possible public theorems:

```text
ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter
ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyTailAfter
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

Then start Round 87 with the master-controller workflow above.
