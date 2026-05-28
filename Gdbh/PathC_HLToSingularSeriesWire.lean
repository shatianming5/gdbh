/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P29-T1 (Phase 29 / Path C — Wire the Halberstam-Richert §3.11
        master assembly kernel forward to `BrunGoldbachWithSingularSeries`
        via the existing P23-T1 and P28-T2 bridges).
-/
import Gdbh.PathC_BrunGoldbachSingularClosure
import Gdbh.PathC_LocalMainTermRefinedAtSqrtFinal
import Gdbh.PathC_LocalMainTermRefinedAtSqrtClosure
import Gdbh.PathC_KernelBClosed
import Gdbh.PathC_MertensSecondUpper

/-!
# Path C — P29-T1: wire HL master kernel to `BrunGoldbachWithSingularSeries`

## Mission

P28-T2 reduced `BrunGoldbachLocalMainTermRefinedAtSqrt` to the strictly
smaller kernel sub-Prop

```
BrunGoldbachLocalMainTermRefinedAtSqrtKernel
  := GoldbachResidueSiftedRefinedUpperBoundAtSqrt
```

via the axiom-clean mechanical bridge
`brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel`
(from `Gdbh.PathCLocalMainTermRefinedAtSqrtClosure`).

P23-T1 already provided the master closure of
`BrunGoldbachWithSingularSeries` from the two named master inputs:

* `BrunGoldbachLocalMainTermRefinedAtSqrt` (the §3.11 local-factor
  main term), and
* `PairedBrunMertensThirdLowerGap` (the paired-Brun Mertens lower
  gap),

via
`brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap`
(from `Gdbh.PathCBrunGoldbachSingularClosure`).

Independently, P19-T6 (file `Gdbh.PathCMertensSecondUpper`) closed
`PairedBrunMertensThirdLowerGap` unconditionally as
`pairedBrunMertensThirdLowerGap_holds`.

Composing these three pieces yields the **single-input** wire:

```
BrunGoldbachLocalMainTermRefinedAtSqrtKernel
  →  BrunGoldbachWithSingularSeries .
```

This is the P29-T1 deliverable.

## The complete chain (P19-T6 + P23-T1 + P28-T2 + P29-T1)

```
   (kernel input)  BrunGoldbachLocalMainTermRefinedAtSqrtKernel
                             │
                             ▼  (P28-T2 / P24-T1 bridge — axiom-clean)
                  BrunGoldbachLocalMainTermRefinedAtSqrt
                             │
                             │  ⊕  PairedBrunMertensThirdLowerGap
                             │     (closed unconditionally by P19-T6:
                             │      `pairedBrunMertensThirdLowerGap_holds`)
                             ▼  (P23-T1 master closure — axiom-clean)
                  BrunGoldbachWithSingularSeries
```

## What this file provides

1. The headline single-input wire
   `brunGoldbachWithSingularSeries_of_kernel`, taking only the kernel
   sub-Prop and producing `BrunGoldbachWithSingularSeries`.

2. Two convenience corollaries factoring the composition through the
   intermediate Props (`BrunGoldbachLocalMainTermRefinedAtSqrt` and
   `HLMasterAssemblyAtSqrt`).

3. A "complete chain audit" theorem that explicitly composes the
   pieces.

4. `#print axioms` audits confirming only
   `[Classical.choice, Quot.sound, propext]` axioms are used.

## Strict constraints (P29-T1 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* This file **only adds**; it does not modify any other file.
* `lake env lean Gdbh/PathC_HLToSingularSeriesWire.lean` succeeds.
-/

namespace Gdbh
namespace PathCHLToSingularSeriesWire

open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel
   brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel)
open Gdbh.PathCLocalMainTermRefinedAtSqrtFinal
  (HLMasterAssemblyAtSqrt
   brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly
   kernel_of_hlMasterAssembly
   hlMasterAssembly_of_kernel)
open Gdbh.PathCGoldbachLocalFactor
  (BrunGoldbachLocalMainTermRefinedAtSqrt)
open Gdbh.PathCPairedBrunMertensLowerReal
  (PairedBrunMertensThirdLowerGap)
open Gdbh.PathCMertensSecondUpper
  (pairedBrunMertensThirdLowerGap_holds)
open Gdbh.PathCBrunGoldbachSingularSeries
  (BrunGoldbachWithSingularSeries)
open Gdbh.PathCBrunGoldbachSingularClosure
  (brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
   brunGoldbachWithSingularSeries_of_master_assembly
   reservoirAbsorbedBySingular_of_lowerGap)

/-! ## Section 1 — Headline wire: kernel ⇒ `BrunGoldbachWithSingularSeries`

The P29-T1 headline.  Compose:

1. (P28-T2 / P24-T1) `kernel → BrunGoldbachLocalMainTermRefinedAtSqrt`
   via `brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel`.
2. (P19-T6, unconditional) `PairedBrunMertensThirdLowerGap` is closed
   via `pairedBrunMertensThirdLowerGap_holds`.
3. (P23-T1) Combine (1) and (2) through
   `brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap`
   to yield `BrunGoldbachWithSingularSeries`.

The Mertens lower gap appears only as an *internal step* of the
composition; it is supplied unconditionally so the resulting wire
takes only the kernel as input. -/

/-- **P29-T1 headline.**  The §3.11 master kernel sub-Prop
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel` closes the singular-series
form `BrunGoldbachWithSingularSeries` through the existing
bridges.

Composition:

* `kernel → BrunGoldbachLocalMainTermRefinedAtSqrt`
  (P24-T1 / P28-T2: `brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel`),
* `PairedBrunMertensThirdLowerGap` is supplied unconditionally
  (P19-T6: `pairedBrunMertensThirdLowerGap_holds`),
* the two combine to `BrunGoldbachWithSingularSeries`
  (P23-T1: `brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap`).

Axiom-clean: `[Classical.choice, Quot.sound, propext]`. -/
theorem brunGoldbachWithSingularSeries_of_kernel
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    (brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel hKernel)
    pairedBrunMertensThirdLowerGap_holds

/-! ## Section 2 — Convenience entry points

Two alternative entry points expose the same composition under
different names:

* `brunGoldbachWithSingularSeries_of_hlMasterAssembly` takes
  the (definitionally equal) parametric HL master assembly Prop
  introduced in P28-T2;
* `brunGoldbachWithSingularSeries_of_localMainTermRefinedAtSqrt`
  takes the post-bridge target Prop, factoring out the kernel reduction.
-/

/-- **HL master assembly entry.**  The HL master assembly Prop at √n,
which is definitionally equal to the kernel sub-Prop, closes
`BrunGoldbachWithSingularSeries`. -/
theorem brunGoldbachWithSingularSeries_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_kernel (kernel_of_hlMasterAssembly hHL)

/-- **Local-main-term entry.**  The §3.11 master local-factor Prop at √n
closes `BrunGoldbachWithSingularSeries` (this is the P23-T1 closure with
the unconditional Mertens lower gap pre-supplied). -/
theorem brunGoldbachWithSingularSeries_of_localMainTermRefinedAtSqrt
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    hMain pairedBrunMertensThirdLowerGap_holds

/-! ## Section 3 — Complete chain audit

A single end-to-end composed theorem exhibiting all three steps. -/

/-- **Complete-chain audit theorem.**  This theorem explicitly exhibits
the three-step composition that closes `BrunGoldbachWithSingularSeries`
from the parametric `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`
input:

1. (P24-T1 / P28-T2) the kernel mechanically implies the §3.11 master
   local-factor Prop:
   `BrunGoldbachLocalMainTermRefinedAtSqrtKernel
      → BrunGoldbachLocalMainTermRefinedAtSqrt`,
2. (P19-T6) the paired-Brun Mertens lower gap is closed unconditionally:
   `pairedBrunMertensThirdLowerGap_holds : PairedBrunMertensThirdLowerGap`,
3. (P23-T1) the two combine to close the singular-series form:
   `BrunGoldbachLocalMainTermRefinedAtSqrt
      → PairedBrunMertensThirdLowerGap
      → BrunGoldbachWithSingularSeries`.

Composition of the three steps gives the conditional closure from the
single kernel input. -/
theorem complete_chain_audit
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    BrunGoldbachWithSingularSeries := by
  -- Step 1 (P24-T1 / P28-T2):  kernel → BrunGoldbachLocalMainTermRefinedAtSqrt.
  have hMain : BrunGoldbachLocalMainTermRefinedAtSqrt :=
    brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel hKernel
  -- Step 2 (P19-T6):  the Mertens lower gap is closed unconditionally.
  have hLower : PairedBrunMertensThirdLowerGap :=
    pairedBrunMertensThirdLowerGap_holds
  -- Step 3 (P23-T1):  combine via the master closure to obtain
  -- BrunGoldbachWithSingularSeries.
  exact brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    hMain hLower

/-! ## Section 4 — Honesty / scope audit

We record explicitly what this file delivers and what it relies on.

**Closed in this file (axiom-clean):**

* `brunGoldbachWithSingularSeries_of_kernel` — the headline single-input
  wire from the kernel sub-Prop to the singular-series form.
* `brunGoldbachWithSingularSeries_of_hlMasterAssembly` and
  `brunGoldbachWithSingularSeries_of_localMainTermRefinedAtSqrt` —
  convenience entry points.
* `complete_chain_audit` — explicit step-by-step composition.

**Inputs (all closed or parametric in this file):**

* `BrunGoldbachLocalMainTermRefinedAtSqrtKernel` — the single parametric
  input.  This is exactly the strictly-smaller kernel sub-Prop produced
  in P24-T1 (and taken as the parametric HL master assembly input
  in P28-T2).
* `PairedBrunMertensThirdLowerGap` — closed unconditionally by P19-T6
  (`pairedBrunMertensThirdLowerGap_holds`, axiom-clean), supplied
  internally by this file.

**Remaining open content:**

* exactly one named Prop:
  `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`,
  i.e. the kernel/HL master assembly deliverable.  No additional
  analytic content beyond that.

This file is therefore the **strongest conditional closure** of
`BrunGoldbachWithSingularSeries` derivable from the
P19-T6 + P23-T1 + P28-T2 infrastructure, parametrised only on the
single kernel input. -/

/-- **Honest summary** (informal sentinel).  This file is the P29-T1
deliverable: composes (parametrically) the P28-T2 kernel reduction with
the P23-T1 master closure and the unconditional P19-T6 lower gap to
close `BrunGoldbachWithSingularSeries` from the single kernel input. -/
theorem pathC_p29_t1_summary : True := trivial

/-! ## Section 5 — Axiom audit

`#print axioms` lines below verify that every exported theorem of this
file uses only `[Classical.choice, Quot.sound, propext]` axioms.
No `sorry`, no `axiom`, no `admit` is used anywhere in this file or in
any of its transitively imported dependencies (subject to the standing
project audit invariant). -/

#print axioms brunGoldbachWithSingularSeries_of_kernel
#print axioms brunGoldbachWithSingularSeries_of_hlMasterAssembly
#print axioms brunGoldbachWithSingularSeries_of_localMainTermRefinedAtSqrt
#print axioms complete_chain_audit
#print axioms pathC_p29_t1_summary

end PathCHLToSingularSeriesWire
end Gdbh
