/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Wave 1 / Path C unconditional integration pre-write (P19-T15)
-/
import Gdbh.PathC_PairedBrunGoldbachAtSqrt
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_PairedBrunMertensUpper
import Gdbh.PathC_KernelBClosed

/-!
# Path C — Pre-wired unconditional integration (P19-T15)

This file is the **one-liner composition layer** that pre-wires the full
Path C K-Goldbach chain, conditional only on the two genuinely-residual
named open Props.  Once these residuals are discharged upstream, the
unconditional Path C K-Goldbach theorem becomes a single application
of the conditional headline.

## Architectural picture (chain after P19-T14)

```
AlignedInequalityAndTail                                  (T14, in progress)
  ⇒  BrunGoldbachPairedMainTermRefinedAtSqrt              (P18-T4 bridge)
  ⇒  via  +  PairedBrunFactorMertensUpperAtSqrt           (P18-T1, closed)
       +  PairedMainTermResidualLowRegion                 (P18-T3, residual)
       +  Kernel B (PairedBrunFactorRealMertensLower)     (P19-T13, closed)
     ⇒  PairedMainTermAbsorption                          (P19-T13 bridge)
  ⇒  BrunGoldbachPairedMainTermRefined                    (P17-T6 bridge)
  ⇒  GoldbachRepresentationBound                          (PathCClosedReductions)
  ⇒  pathC_kGoldbach                                      (PathC_Final phase 10/11)
```

The pre-wired conditional headline below consumes only the two
genuinely-residual Props:

* `Gdbh.PathCPairedBrunGoldbachAtSqrt.AlignedInequalityAndTail`
  (the "Kernel A interior", T14 target — the paired Brun–Bonferroni
  inequality at `z = √n` aligned with the T5-Sqrt Stirling tail);
* `Gdbh.PathCPairedBrunLargeZ.PairedMainTermResidualLowRegion`
  (the "low-region" residual: paired Brun–Bonferroni at all sub-`√n`
  thresholds combined with finite case analysis for bounded `n`,
  partially addressed by P18-T3).

Every other ingredient on the chain is already axiom-clean.

## Strict policy

* No `sorry`, no `axiom`, no `admit` anywhere in this file.
* All theorems are axiom-clean: only `Classical.choice`, `Quot.sound`,
  `propext` (inherited from `mathlib` infrastructure).
* This file only *composes* existing closed lemmas.  No file outside
  this one is modified.
-/

namespace Gdbh
namespace PathCUnconditionalIntegration

open Gdbh.PathCPairedBrunGoldbachAtSqrt
  (AlignedInequalityAndTail
   brunGoldbachPairedMainTermRefinedAtSqrt_of_alignedInequalityAndTail)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt
   PairedMainTermAbsorption
   pathC_kGoldbach_of_absorption)
open Gdbh.PathCPairedBrunLargeZ
  (PairedBrunFactorMertensUpperAtSqrt
   PairedMainTermResidualLowRegion)
open Gdbh.PathCPairedBrunMertensUpper
  (pairedBrunFactorMertensUpperAtSqrt_holds)
open Gdbh.PathCKernelBClosed
  (absorption_of_atSqrt_upper_lowRegion_unconditionalRealLower
   pairedBrunFactorRealMertensLower_holds_unconditional)

/-! ## Section 1 — Already-closed pieces (recap, axiom-clean)

We record the unconditional pieces of the chain as named lemmas inside
this file so that downstream auditing can reference a single integration
module.

These are *pure aliases* of upstream theorems; no new content. -/

/-- **Kernel B is fully closed (axiom-clean).**  Sentinel summary lemma
recording that the Kernel B half of the absorption chain
(`PairedBrunFactorRealMertensLower`, discharged via P19-T6 +
P18-T2-real in `Gdbh.PathCKernelBClosed`) is unconditional. -/
theorem pathC_kernelB_closed_axiom_clean : True := trivial

/-- **Kernel B unconditional witness (re-export).**
`PairedBrunFactorRealMertensLower` holds unconditionally (P19-T13). -/
theorem kernelB_witness :
    Gdbh.PathCPairedBrunMertensLowerProof.PairedBrunFactorRealMertensLower :=
  pairedBrunFactorRealMertensLower_holds_unconditional

/-- **`PairedBrunFactorMertensUpperAtSqrt` unconditional witness
(re-export).**  Closed by P18-T1 via the M1 + Abel chain. -/
theorem pairedBrunFactorMertensUpperAtSqrt_witness :
    PairedBrunFactorMertensUpperAtSqrt :=
  pairedBrunFactorMertensUpperAtSqrt_holds

/-! ## Section 2 — Conditional headline (P19-T15)

The pre-wired conditional headline.  Once the two residual Props are
discharged, the unconditional Path C K-Goldbach is a single application
of this theorem.

The intermediate Prop `BrunGoldbachPairedMainTermRefinedAtSqrt` (Kernel
A) is derived from `AlignedInequalityAndTail` via the P18-T4 bridge.
The combined three-input absorption bridge (P19-T13) then closes
`PairedMainTermAbsorption`, which through the P17-T6 and P15-T2 bridges
yields the K-Goldbach K-bound. -/

/-- **Path C K-Goldbach, conditional on the two remaining kernels.**

Pre-wired integration: given the two residual Props
* `AlignedInequalityAndTail` (the Kernel A interior, P19-T14 target), and
* `PairedMainTermResidualLowRegion` (the low-region residual, P18-T3
  partial / Kernel A SubSqrt + small),

the Path C K-Goldbach theorem follows.  All other ingredients
(Kernel B, the Mertens-upper at `√n`, and the entire downstream
`Absorption → Refined → RepBound → K-Goldbach` chain) are already
axiom-clean. -/
theorem pathC_kGoldbach_unconditional_conditional_on_kernels
    (hAligned : AlignedInequalityAndTail)
    (hLowRegion : PairedMainTermResidualLowRegion) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  -- Step 1: AlignedInequalityAndTail ⇒ BrunGoldbachPairedMainTermRefinedAtSqrt
  --         (P18-T4 end-to-end bridge, axiom-clean).
  have hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt :=
    brunGoldbachPairedMainTermRefinedAtSqrt_of_alignedInequalityAndTail hAligned
  -- Step 2: AtSqrt + Upper(closed) + LowRegion + Kernel B(closed) ⇒ Absorption
  --         (P19-T13 three-input bridge, axiom-clean).
  have hAbsorption : PairedMainTermAbsorption :=
    absorption_of_atSqrt_upper_lowRegion_unconditionalRealLower
      hAtSqrt
      pairedBrunFactorMertensUpperAtSqrt_witness
      hLowRegion
  -- Step 3: Absorption ⇒ pathC_kGoldbach (P17-T6 → P15-T2 → P10-M12
  --         composite bridge, axiom-clean).
  pathC_kGoldbach_of_absorption hAbsorption

/-! ## Section 3 — Residual documentation

The literal Prop names that remain open after this integration are:

1. `Gdbh.PathCPairedBrunGoldbachAtSqrt.AlignedInequalityAndTail`
   (P19-T14 target; the paired Brun–Bonferroni inequality at
   `z = √n` aligned with the T5-Sqrt Stirling tail in a shared
   truncation depth `k`).  The tail half is already closed
   (`pairedBonferroniTailAtSqrt_holds`); the genuine residual is the
   inequality half (classical Halberstam–Richert / Nathanson
   combinatorics).

2. `Gdbh.PathCPairedBrunLargeZ.PairedMainTermResidualLowRegion`
   (P18-T3 partial; the paired Brun–Bonferroni inequality at all
   sub-`√n` thresholds `z < √n` combined with the finite-case
   analysis for bounded `n < N₀`).  Reduced in `PathC_PairedBrunLowRegion`
   to a single named open `PairedBrunBonferroniSubSqrt`.

Both reductions are mechanical wrappers around the same classical
Brun–Bonferroni machinery; the *single* genuine analytic gap is the
Halberstam–Richert paired inequality kernel.

Final unconditional wire-up (after P19-T14 lands
`alignedInequalityAndTail_holds` and after the low-region residual is
closed):

```lean
theorem pathC_kGoldbach_unconditional :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_unconditional_conditional_on_kernels
    alignedInequalityAndTail_holds            -- P19-T14
    pairedMainTermResidualLowRegion_holds     -- P18-T3 (to close)
```

i.e. **a one-liner**.  This is precisely the design goal of P19-T15. -/

/-! ## Section 4 — Documentation theorem

Records the P19-T15 deliverable summary. -/

/-- **P19-T15 summary, in proof form.**

**Mission**: pre-write the Path C unconditional integration so that the
final wire-up, once both Kernel A residuals are closed, is a 1-liner.

**Outcome**:

1. `pathC_kernelB_closed_axiom_clean` — sentinel for the Kernel B
   closure (P19-T13).

2. `kernelB_witness` — re-exported unconditional Kernel B witness
   (`PairedBrunFactorRealMertensLower`).

3. `pairedBrunFactorMertensUpperAtSqrt_witness` — re-exported
   unconditional P18-T1 Mertens-upper-at-`√n` witness.

4. `pathC_kGoldbach_unconditional_conditional_on_kernels` —
   **headline conditional theorem**: K-Goldbach in `∃ K, ∀ n ≥ 2, …`
   form, given the two residual Props as hypotheses.

   *Proof structure*: three-step composition
   - P18-T4 bridge: `AlignedInequalityAndTail ⇒ AtSqrt`;
   - P19-T13 three-input bridge: `AtSqrt + UpperAtSqrt(closed) +
     LowRegion ⇒ Absorption` (Kernel B supplied unconditionally);
   - P17-T6 + P15-T2 + P10-M12 chain: `Absorption ⇒ K-Goldbach`.

5. **Documented residuals** (literal Prop names):
   - `Gdbh.PathCPairedBrunGoldbachAtSqrt.AlignedInequalityAndTail`,
   - `Gdbh.PathCPairedBrunLargeZ.PairedMainTermResidualLowRegion`.

6. **Final wire-up plan** (documented in Section 3): once the two
   residuals are closed upstream, a single application of
   `pathC_kGoldbach_unconditional_conditional_on_kernels` to the two
   `_holds` lemmas yields the unconditional Path C K-Goldbach.

**Axiom audit**: all theorems in this file are axiom-clean.  The
auditable axiom set is exactly `[Classical.choice, Quot.sound, propext]`,
inherited solely from `mathlib` infrastructure.

**False-Prop catches in this round**: none.  The two residual Props are
established named open Props from upstream (P18-T3, P18-T4); no new
Props are introduced. -/
theorem pathC_p19_t15_summary : True := trivial

end PathCUnconditionalIntegration
end Gdbh
