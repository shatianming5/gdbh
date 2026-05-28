# Path C K-Goldbach Closure Execution Plan

Date: 2026-05-26

Objective: close the Path C K-Goldbach theorem in Lean without changing the
mathematical target by convenience.  The deliverable is a theorem with no
residual hypotheses:

```lean
theorem pathC_kGoldbach_FINAL :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n
```

This is not binary Goldbach.  It is the unconditional K-Goldbach Path C
closure.

## Gate 0: Build Coverage And Hygiene

Goal: make sure every Lean file that may be used in the closure is actually
checked.

Actions:

1. Run `lake build`.
2. Run `python3 audit_lean_source.py`.
3. Run `bash scripts/audit_full.sh`.
4. Run `bash scripts/audit_standalone_lean.sh`.
5. Treat any file failing standalone Lean as experimental until it is repaired
   or explicitly excluded from the closure route.

Acceptance:

```bash
source "$HOME/.elan/env"
lake build
python3 audit_lean_source.py
bash scripts/audit_full.sh
bash scripts/audit_standalone_lean.sh
```

Current known risk: `Gdbh/PathC_WeightedSchnirelmannClosure.lean` is not part
of the root barrel and currently fails standalone checking.  Do not import it
into the closure chain until repaired.

Current usable replacement:
`Gdbh/PathC_WeightedSchnirelmannSafeClosure.lean` compiles standalone and gives
a clean residual split for the weighted bridge.  If the old four-residual route
must be retained, use this safe file rather than the older failing draft.

Fast target listing:

```bash
bash scripts/audit_standalone_lean.sh --list-targets
bash scripts/audit_standalone_lean.sh --list-targets --exclude 'Certificate|PathA_'
```

## Phase 1: AtSqrt-Only Route

Goal: avoid unnecessary universal-in-z obligations in the final K-Goldbach
route.

Rationale: the downstream representation-count route uses the main-term bound
only at `zChoice n`.  In the canonical Path C route, `zChoice n = Nat.sqrt n`.
Therefore the final K-Goldbach chain should consume an AtSqrt main-term theorem
directly, not force a universal-in-z bridge.

New file:

```text
Gdbh/PathC_AtSqrtKGoldbachRoute.lean
```

Stable subgoals:

```lean
AtSqrtRepresentationBound
AtSqrtPositiveDensityBridge
pathC_kGoldbach_of_atSqrtFixAStrong
```

Preferred theorem shape:

```lean
theorem pathC_kGoldbach_of_atSqrt_fixAStrong
    (h : BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n
```

Fallback theorem shape:

```lean
theorem pathC_kGoldbach_of_atSqrt_loglog
    (h : ClassicalBrunGoldbachLogLog) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n
```

Files to inspect first:

- `Gdbh/PathC_GoldbachRBound.lean`
- `Gdbh/PathC_FinalClosedReductions.lean`
- `Gdbh/PathC_FixAStrongClosure.lean`
- `Gdbh/PathC_PairedMainTermAssembly.lean`

Acceptance:

- No import of `PathC_WeightedSchnirelmannClosure`.
- The theorem is axiom-clean with only `[propext, Classical.choice, Quot.sound]`.
- The theorem removes the need for `AtSqrtFixAStrongToUniversal` and
  `WeightedSchnirelmannResidualBridge` on the chosen final route.

## Phase 2: Singular Series Mertens-3 Closure

Goal: close:

```lean
Gdbh.PathCBrunGoldbachSingularSeries.SingularSeriesMertens3Bound
```

New file:

```text
Gdbh/PathC_SingularSeriesMertens3Closure.lean
```

Stable subgoals:

```lean
SingularSeries_le_oddPrimorialEnvelope
OddPrimorialEnvelope_loglog_control
OddPrimorialSingularSeries_mertens3
singularSeriesMertens3Bound_holds
```

Proof strategy:

1. Reduce `singularSeries n` to the product over odd primes dividing
   `rad n`.
2. Bound that product by the product over the largest odd primorial envelope
   associated to `n`.
3. Use existing Mertens-second/primorial material to prove a
   `K * log log n` upper bound.

Primary source files:

- `Gdbh/PathC_SingularSeriesPrimorialMertens.lean`
- `Gdbh/PathC_SingularSeriesPointwiseBound.lean`
- `Gdbh/PathC_ChebyshevPrimorial.lean`
- `Gdbh/PathC_MertensSecondUpper.lean`

Acceptance:

```lean
theorem singularSeriesMertens3Bound_holds :
    SingularSeriesMertens3Bound
```

with the required axiom set.

## Phase 3: HL/Brun Kernel Closure At Sqrt

Goal: close:

```lean
Gdbh.PathCLocalMainTermRefinedAtSqrtClosure.BrunGoldbachLocalMainTermRefinedAtSqrtKernel
```

This is definitionally:

```lean
GoldbachResidueSiftedRefinedUpperBoundAtSqrt
```

New files:

```text
Gdbh/PathC_Kernel_BonferroniResidue.lean
Gdbh/PathC_Kernel_CRTResidueCount.lean
Gdbh/PathC_Kernel_LocalFactorAssembly.lean
Gdbh/PathC_Kernel_TailAtSqrt.lean
Gdbh/PathC_Kernel_Final.lean
```

Subgoals:

```lean
ResidueBonferroniUpperAtSqrt
ResidueCRTMainTermAtSqrt
ResidueLocalFactorEulerProductAtSqrt
ResidueBonferroniTailAtSqrt
goldbachResidueSiftedRefinedUpperBoundAtSqrt_holds
```

Proof strategy:

1. Convert the residue-sifted count into truncated Bonferroni sums.
2. Evaluate residue CRT counts by the gcd/local-factor split.
3. Assemble the main term as `goldbachResidueMainFactor n (Nat.sqrt n)`.
4. Bound the truncation tail into `goldbachResidueRefinedError n (Nat.sqrt n)`.
5. Package constants and thresholds.

Primary source files:

- `Gdbh/PathC_PairedBonferroniGeneralK.lean`
- `Gdbh/PathC_PairedCRTSplitByGCD.lean`
- `Gdbh/PathC_PairedSumGCDSplit.lean`
- `Gdbh/PathC_LocalDensityEulerFactor.lean`
- `Gdbh/PathC_GoldbachResidues.lean`
- `Gdbh/PathC_WeightedBonferroniTail.lean`
- `Gdbh/PathC_StirlingExplicitPaired.lean`

Acceptance:

```lean
theorem brunGoldbachLocalMainTermRefinedAtSqrtKernel_holds :
    BrunGoldbachLocalMainTermRefinedAtSqrtKernel
```

with the required axiom set.

## Phase 4: Final Closed Headline

New file:

```text
Gdbh/PathC_KGoldbachFinalClosed.lean
```

If Phase 1 succeeds, final composition should use only:

```lean
brunGoldbachLocalMainTermRefinedAtSqrtKernel_holds
singularSeriesMertens3Bound_holds
pathC_kGoldbach_of_atSqrt_fixAStrong
```

If Phase 1 fails and the old four-residual route must be retained, final
composition requires:

```lean
brunGoldbachLocalMainTermRefinedAtSqrtKernel_holds
singularSeriesMertens3Bound_holds
atSqrtFixAStrongToUniversal_holds
weightedSchnirelmannResidualBridge_holds
```

For `weightedSchnirelmannResidualBridge_holds`, prefer the safe split:

```lean
FixAStrongReservoirAbsorption
∀ N_F, FixAStrongFiniteRangeAbsorptionAligned N_F
```

via `Gdbh.PathCWeightedSchnirelmannSafeClosure.weightedSchnirelmannResidualBridge_of_residuals`.

Acceptance:

```lean
theorem pathC_kGoldbach_FINAL :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n
```

Then import the final file into `Gdbh.lean`, run all gates, and regenerate
`AGENTS.md`.

## Execution Order

1. Gate 0.
2. Phase 1, because it may delete two residuals from the final route.
3. Phase 2, because it is the most isolated analytic closure.
4. Phase 3, because it is the largest proof and depends on the most local
   infrastructure.
5. Phase 4.

## Stop Conditions

Stop and write an obstruction note if any proposed theorem implies one of the
documented false-prop catches, especially:

- pointwise singular-series bounds too strong at primorials;
- naive `n / (log n)^2` Brun main term;
- universal-in-z monotonicity assumptions;
- finite-range absorption requiring a positive lower bound on
  `pairedBrunFactor z` for unbounded `z`.

## Final Verification Gate

```bash
source "$HOME/.elan/env"
lake build
python3 audit_lean_source.py
bash scripts/audit_full.sh
python3 scripts/regenerate_agents_md.py
```
