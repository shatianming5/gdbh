/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P29-T2 (Phase 29 / Path C — Wire through the FixA' chain from
        `BrunGoldbachLocalMainTermRefinedAtSqrtKernel` (P24-T1 kernel
        alias) all the way to the K-Goldbach K-bound conclusion).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_GoldbachResidues
import Gdbh.PathC_LocalMainTermRefinedAtSqrtClosure
import Gdbh.PathC_LocalMainTermRefinedAtSqrtFinal
import Gdbh.PathC_BrunGoldbachSingularSeries
import Gdbh.PathC_BrunGoldbachSingularClosure
import Gdbh.PathC_FixAStrongClosure
import Gdbh.PathC_FixAStrongReservoir
import Gdbh.PathC_PairedBrunMertensLowerReal
import Gdbh.PathC_MertensSecondUpper
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_FinalClosedReductions
import Gdbh.PathC_UnconditionalFixAStrong
import Gdbh.PathC_FullChainAudit

/-!
# Path C — P29-T2: full FixA' chain wire from the local-main-term kernel

## Mission

P29-T1 (parallel) handles the Halberstam-Richert §3.11 master ⇒ singular
series step.  This file (P29-T2) handles **the rest** — wiring the
entire chain

```
BrunGoldbachLocalMainTermRefinedAtSqrtKernel       (P24-T1 named alias)
   │
   ▼  (P22-T5 mechanical bridge:  kernel ⇒ local-main-term Prop)
BrunGoldbachLocalMainTermRefinedAtSqrt
   │
   ▼  (P23-T1 master assembly + P19-T6 closed Mertens lower gap)
BrunGoldbachWithSingularSeries
   │
   ▼  (P22-T2 Bridge A; consumes named open `SingularSeriesMertens3Bound`)
ClassicalBrunGoldbachLogLog
   │
   ▼  (P20-T4 AM-GM-style absorption at sieve threshold `z = √n`)
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
   │
   ▼  (consumes named open `AtSqrtFixAStrongToUniversal` from P24-T2)
BrunGoldbachPairedMainTermRefinedFixAStrong
   │
   ▼  (P21-T2 Schnirelmann residual bridge — named open `WeightedSchnirelmannResidualBridge`)
BrunGoldbachPairedMainTermRefined
   │
   ▼  (P17-T6 trivial unfolding via `iff_absorption.mp`)
PairedMainTermAbsorption
   │
   ▼  (P17-T6 K-Goldbach headline)
∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ... K-bound on prime-sum representations.
```

## Strict constraints (P29-T2 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* The file **only adds**; it does not modify any other file.
* `lake env lean Gdbh/PathC_FullFixAStrongWire.lean` succeeds.
* The headline theorem `pathC_kGoldbach_of_kernel` takes the kernel
  Prop as input and, additionally, accepts the three named open
  residuals on the chain (Steps 2/4/5 in the FullChainAudit numbering)
  as explicit parameters — per the task's "accept additional named
  open residuals where bridges aren't closed" rule.

## What this file provides

* `pathC_kGoldbach_of_kernel` — the headline theorem, composing the
  seven chain steps end-to-end from the kernel alias to the K-bound.

* A direct composition `pathC_kGoldbach_of_kernel_via_master_assembly`
  that bypasses the explicit `BrunGoldbachWithSingularSeries` step by
  using the P23-T1 master-assembly composed bridge.

* Six step-by-step bridge theorems
  (`step1_local_of_kernel`, `step2_brunGoldbachWithSingularSeries`,
  `step3_classicalLogLog`, `step4_atSqrt_fixAStrong`,
  `step5_universal_fixAStrong`, `step6_refined_main_term`,
  `step7_kGoldbach`) for downstream auditability.

* An axiom-audit block at the end.
-/

namespace Gdbh
namespace PathCFullFixAStrongWire

open Gdbh.PathCGoldbachLocalFactor (BrunGoldbachLocalMainTermRefinedAtSqrt)
open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel
   brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel)
open Gdbh.PathCBrunGoldbachSingularClosure
  (brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
   brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly
   classicalBrunGoldbachLogLog_of_master_assembly)
open Gdbh.PathCBrunGoldbachSingularSeries
  (BrunGoldbachWithSingularSeries SingularSeriesMertens3Bound
   classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries)
open Gdbh.PathCFixAStrongClosure
  (ClassicalBrunGoldbachLogLog
   brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog)
open Gdbh.PathCFixAStrongReservoir
  (BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
   BrunGoldbachPairedMainTermRefinedFixAStrong
   pathC_kGoldbach_of_fixAStrong_via_bridge)
open Gdbh.PathCPairedBrunMertensLowerReal (PairedBrunMertensThirdLowerGap)
open Gdbh.PathCMertensSecondUpper (pairedBrunMertensThirdLowerGap_holds)
open Gdbh.PathCBrunRefinedComposition (BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCPairedMainTermAssembly
  (PairedMainTermAbsorption brunGoldbachPairedMainTermRefined_iff_absorption
   pathC_kGoldbach_of_absorption)
open Gdbh.PathCUnconditionalFixAStrong (WeightedSchnirelmannResidualBridge)
open Gdbh.PathCFullChainAudit (AtSqrtFixAStrongToUniversal)

/-! ## Section 1 — Step-by-step bridges

We expose each chain step under a stable name so downstream auditors
can refer to it.  All steps below are axiom-clean
(`[Classical.choice, Quot.sound, propext]`). -/

/-- **Step 1 (closed, P22-T5 mechanical bridge):**
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel` ⇒
`BrunGoldbachLocalMainTermRefinedAtSqrt`.

The kernel sub-Prop is definitionally equal to the residue-sifted
refined upper bound at `z = √n`, and the P22-T5 stage gives the
mechanical bridge from residue-sifted to local-main-term form. -/
theorem step1_local_of_kernel
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    BrunGoldbachLocalMainTermRefinedAtSqrt :=
  brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel hKernel

/-- **Step 2 (closed, P23-T1 + P19-T6):**
`BrunGoldbachLocalMainTermRefinedAtSqrt` ⇒ `BrunGoldbachWithSingularSeries`.

Composes the P23-T1 master-assembly closure with the closed paired
Mertens lower gap `pairedBrunMertensThirdLowerGap_holds` (P19-T6). -/
theorem step2_brunGoldbachWithSingularSeries
    (hLocal : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    hLocal pairedBrunMertensThirdLowerGap_holds

/-- **Step 3 (conditional on Mertens-3, P22-T2 Bridge A):**
`BrunGoldbachWithSingularSeries` ⇒ `ClassicalBrunGoldbachLogLog`,
given `SingularSeriesMertens3Bound`. -/
theorem step3_classicalLogLog
    (hBG : BrunGoldbachWithSingularSeries)
    (hMertens3 : SingularSeriesMertens3Bound) :
    ClassicalBrunGoldbachLogLog :=
  classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries hBG hMertens3

/-- **Step 4 (closed, P20-T4 AM-GM absorption):**
`ClassicalBrunGoldbachLogLog` ⇒ `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`.

Applied at the sieve threshold `z = √n`. -/
theorem step4_atSqrt_fixAStrong
    (hLogLog : ClassicalBrunGoldbachLogLog) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong :=
  brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog hLogLog

/-- **Step 5 (conditional on AtSqrt → universal upgrade):**
`BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` ⇒
`BrunGoldbachPairedMainTermRefinedFixAStrong`,
given the named open `AtSqrtFixAStrongToUniversal` (P24-T2). -/
theorem step5_universal_fixAStrong
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)
    (hUniversal : AtSqrtFixAStrongToUniversal) :
    BrunGoldbachPairedMainTermRefinedFixAStrong :=
  hUniversal hAtSqrt

/-- **Step 6 (conditional on P21-T2 Schnirelmann residual):**
`BrunGoldbachPairedMainTermRefinedFixAStrong` ⇒
`BrunGoldbachPairedMainTermRefined`,
given the named open `WeightedSchnirelmannResidualBridge`. -/
theorem step6_refined_main_term
    (hFixAStrong : BrunGoldbachPairedMainTermRefinedFixAStrong)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    BrunGoldbachPairedMainTermRefined :=
  hSchnirelmann hFixAStrong

/-- **Step 7 (closed, P17-T6):**
`BrunGoldbachPairedMainTermRefined` ⇒ K-Goldbach K-bound.

The P17-T6 closed downstream chain composes the refined main term
through the absorption Prop into the K-bound on prime-sum
representations. -/
theorem step7_kGoldbach
    (hRefined : BrunGoldbachPairedMainTermRefined) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_absorption
    (brunGoldbachPairedMainTermRefined_iff_absorption.mp hRefined)

/-! ## Section 2 — The headline theorem

The P29-T2 deliverable.  Composes Steps 1-7 above into a single
chain wire from the kernel alias to the K-Goldbach K-bound. -/

/-- **P29-T2 headline.**  From the P24-T1 kernel alias
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel` together with the three
named open residuals on the chain
(`SingularSeriesMertens3Bound`, `AtSqrtFixAStrongToUniversal`,
`WeightedSchnirelmannResidualBridge`), derive the K-Goldbach K-bound.

**Proof structure.**  Literal 7-step composition:

1. `step1_local_of_kernel hKernel` ⇒ `BrunGoldbachLocalMainTermRefinedAtSqrt`.
2. `step2_brunGoldbachWithSingularSeries _` ⇒ `BrunGoldbachWithSingularSeries`.
3. `step3_classicalLogLog _ hMertens3` ⇒ `ClassicalBrunGoldbachLogLog`.
4. `step4_atSqrt_fixAStrong _` ⇒ `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`.
5. `step5_universal_fixAStrong _ hUniversal` ⇒
   `BrunGoldbachPairedMainTermRefinedFixAStrong`.
6. `step6_refined_main_term _ hSchnirelmann` ⇒
   `BrunGoldbachPairedMainTermRefined`.
7. `step7_kGoldbach _` ⇒ K-Goldbach K-bound.

**Honesty note.**  The task specification asks for the theorem with
**only** `hKernel` as a hypothesis.  Per the task's allowance to
"accept additional named open residuals where bridges aren't closed",
the three additional named residuals are taken as explicit parameters:

* `SingularSeriesMertens3Bound` (Step 3 input — classical Mertens-3
  absorption `S(n) ≤ K · log log n`),
* `AtSqrtFixAStrongToUniversal` (Step 5 input — AtSqrt to universal-in-z
  upgrade of the FixA' Prop),
* `WeightedSchnirelmannResidualBridge` (Step 6 input — P21-T2
  Schnirelmann residual bridge from FixA' to original Refined). -/
theorem pathC_kGoldbach_of_kernel
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hMertens3 : SingularSeriesMertens3Bound)
    (hUniversal : AtSqrtFixAStrongToUniversal)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  step7_kGoldbach
    (step6_refined_main_term
      (step5_universal_fixAStrong
        (step4_atSqrt_fixAStrong
          (step3_classicalLogLog
            (step2_brunGoldbachWithSingularSeries
              (step1_local_of_kernel hKernel))
            hMertens3))
        hUniversal)
      hSchnirelmann)

/-! ## Section 3 — Alternative shorter wire via the master-assembly composition

For audit completeness, we record an alternative composition that
bypasses the explicit `BrunGoldbachWithSingularSeries` intermediate
by using the P23-T1 master-assembly composed bridge
`brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly`. -/

/-- **Alternative wire via master assembly.**  Same headline theorem,
using the composed P23-T1 master-assembly bridge instead of routing
through the explicit `BrunGoldbachWithSingularSeries` intermediate. -/
theorem pathC_kGoldbach_of_kernel_via_master_assembly
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel)
    (hMertens3 : SingularSeriesMertens3Bound)
    (hUniversal : AtSqrtFixAStrongToUniversal)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_absorption
    (brunGoldbachPairedMainTermRefined_iff_absorption.mp
      (hSchnirelmann
        (hUniversal
          (brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly
            (step1_local_of_kernel hKernel)
            pairedBrunMertensThirdLowerGap_holds
            hMertens3))))

/-! ## Section 4 — Variant taking local-main-term directly (no kernel layer)

For callers that already have `BrunGoldbachLocalMainTermRefinedAtSqrt`
(rather than the strictly smaller kernel), expose a variant that
skips Step 1. -/

/-- **Headline variant.**  Same conclusion as `pathC_kGoldbach_of_kernel`
but taking the local-main-term Prop directly (bypassing the P24-T1
kernel layer). -/
theorem pathC_kGoldbach_of_local
    (hLocal : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hMertens3 : SingularSeriesMertens3Bound)
    (hUniversal : AtSqrtFixAStrongToUniversal)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  step7_kGoldbach
    (step6_refined_main_term
      (step5_universal_fixAStrong
        (step4_atSqrt_fixAStrong
          (step3_classicalLogLog
            (step2_brunGoldbachWithSingularSeries hLocal)
            hMertens3))
        hUniversal)
      hSchnirelmann)

/-! ## Section 5 — Variant taking `BrunGoldbachWithSingularSeries` directly

For callers using the P29-T1 output (which closes
`BrunGoldbachWithSingularSeries` from the HL master assembly via the
P23-T1 composition), expose a variant that takes this Prop directly. -/

/-- **Headline variant.**  Same conclusion as `pathC_kGoldbach_of_kernel`
but taking `BrunGoldbachWithSingularSeries` directly (skipping Steps 1
and 2; this is the variant matching the P29-T1 deliverable). -/
theorem pathC_kGoldbach_of_brunGoldbachWithSingularSeries
    (hBG : BrunGoldbachWithSingularSeries)
    (hMertens3 : SingularSeriesMertens3Bound)
    (hUniversal : AtSqrtFixAStrongToUniversal)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  step7_kGoldbach
    (step6_refined_main_term
      (step5_universal_fixAStrong
        (step4_atSqrt_fixAStrong
          (step3_classicalLogLog hBG hMertens3))
        hUniversal)
      hSchnirelmann)

/-! ## Section 6 — Honest summary

We document explicitly:

1. **Closed steps** in this file (axiom-clean,
   `[Classical.choice, Quot.sound, propext]`):
   * `step1_local_of_kernel` (P22-T5 mechanical bridge),
   * `step2_brunGoldbachWithSingularSeries` (P23-T1 + P19-T6),
   * `step4_atSqrt_fixAStrong` (P20-T4 AM-GM absorption),
   * `step7_kGoldbach` (P17-T6 K-Goldbach headline).

2. **Conditional steps** (consuming named open Props as parameters):
   * `step3_classicalLogLog` (consumes `SingularSeriesMertens3Bound`),
   * `step5_universal_fixAStrong` (consumes `AtSqrtFixAStrongToUniversal`),
   * `step6_refined_main_term` (consumes `WeightedSchnirelmannResidualBridge`).

3. **Headline composition** `pathC_kGoldbach_of_kernel`:
   axiom-clean given the three named open Props as parameters.

4. **The P29-T1 dependency hand-off**:  P29-T1 (parallel) provides the
   HL → `BrunGoldbachWithSingularSeries` step.  Our `step2` provides
   the same content axiom-clean via the local-main-term layer (it
   composes the P23-T1 closure with the closed Mertens lower gap).
   The `pathC_kGoldbach_of_brunGoldbachWithSingularSeries` variant
   above takes the P29-T1 output directly. -/

/-- **P29-T2 summary marker.**  The full FixA' chain wire from the
P24-T1 kernel alias to the K-Goldbach K-bound is complete, with
seven labelled chain steps and three named open residuals. -/
theorem pathC_p29_t2_summary : True := trivial

end PathCFullFixAStrongWire
end Gdbh

/-! ## Section 7 — Axiom audit

Each headline theorem and step bridge depends on at most
`[Classical.choice, Quot.sound, propext]`. -/

#print axioms Gdbh.PathCFullFixAStrongWire.step1_local_of_kernel
#print axioms Gdbh.PathCFullFixAStrongWire.step2_brunGoldbachWithSingularSeries
#print axioms Gdbh.PathCFullFixAStrongWire.step3_classicalLogLog
#print axioms Gdbh.PathCFullFixAStrongWire.step4_atSqrt_fixAStrong
#print axioms Gdbh.PathCFullFixAStrongWire.step5_universal_fixAStrong
#print axioms Gdbh.PathCFullFixAStrongWire.step6_refined_main_term
#print axioms Gdbh.PathCFullFixAStrongWire.step7_kGoldbach
#print axioms Gdbh.PathCFullFixAStrongWire.pathC_kGoldbach_of_kernel
#print axioms Gdbh.PathCFullFixAStrongWire.pathC_kGoldbach_of_kernel_via_master_assembly
#print axioms Gdbh.PathCFullFixAStrongWire.pathC_kGoldbach_of_local
#print axioms Gdbh.PathCFullFixAStrongWire.pathC_kGoldbach_of_brunGoldbachWithSingularSeries
#print axioms Gdbh.PathCFullFixAStrongWire.pathC_p29_t2_summary
