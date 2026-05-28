# Resume For cpudev Codex

Generated from local workspace `/Users/tommy/Downloads/gdbh`.

## Repository

- GitHub: `https://github.com/shatianming5/gdbh`
- Branch: `main`
- Latest local/remote commit at handoff: `767eebe Add Agent.md compatibility copy`
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

Latest verified mathematical round in the scoreboard is Round 75.

Round 75 added:

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

Round 75 verification passed:

- `lake env lean Gdbh/PathC_ResidueRemainderCoprimeSplit.lean`
- `lake build`
- `python3 audit_lean_source.py`
- `bash scripts/audit_full.sh`
- `python3 scripts/regenerate_agents_md.py`

The full audit reported 272 Lean files under `Gdbh/`, 234,906 lines, 7,382
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

No Lean mathematical change has been made after Round 75.

## Suggested Next Round

Continue with Round 76.

Primary candidate:

```text
Candidate: intersection/product support normalization for Round75 remainder
  Goal: expose gcd-product and compatibility conditions as intersection-of-primes conditions
  ExpectedDelta: about 40-45
  Risk: low, algebraic only
  Execute if Lean proof is small and additive
```

Reason:

`PathC_ResidueQuotientMainClosure.lean` already has private lemmas showing
that, for products of residue-prime subsets,

```text
gcd (d1.prod id) (d2.prod id) = (d1 ∩ d2).prod id
lcm (d1.prod id) (d2.prod id) = (d1 ∪ d2).prod id
```

Those facts are useful for the Round75 coprime/non-coprime compatible
remainder workers, but they are currently private inside the quotient-main
closure file. A score-positive additive next step is to create a new file,
for example:

```text
Gdbh/PathC_ResiduePrimeSetProductSupport.lean
```

Possible public theorems:

```text
residuePrimeSubset_prod_ne_zero
residuePrimeSubset_squarefree_prod
residuePrimeSubset_gcd_prod_eq_prod_inter
residuePrimeSubset_lcm_prod_eq_prod_union
residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd
residuePrimeSubset_prod_inter_eq_one_of_coprime
residuePrimeSubset_coprime_iff_inter_eq_empty
```

Then import it from `Gdbh.lean` and later reuse it in the Round75 remainder
split.

Secondary candidate:

```text
Candidate: non-coprime compatible remainder intersection split
  Goal: split shared-prime remainder by a nonempty intersection witness / product divisor of n
  Risk: moderate because it may need more finite-set lemmas
  Defer until the product-support facts are public
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
sed -n '5247,5380p' pathc_master_scoreboard.md
```

Then start Round 76 with the master-controller workflow above.
