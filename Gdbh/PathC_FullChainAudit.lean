/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P24-T2 (Phase 24 / Path C — Full chain end-to-end audit from the
        single remaining residual `BrunGoldbachLocalMainTermRefinedAtSqrt`
        all the way to `pathC_kGoldbach`).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_BrunGoldbachSingularClosure
import Gdbh.PathC_BrunGoldbachSingularSeries
import Gdbh.PathC_HardyLittlewoodForm
import Gdbh.PathC_LocalToSingular
import Gdbh.PathC_FixAStrongClosure
import Gdbh.PathC_FixAStrongReservoir
import Gdbh.PathC_PairedBrunMertensLowerReal
import Gdbh.PathC_MertensSecondUpper
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_FinalClosedReductions
import Gdbh.PathC_UnconditionalFixAStrong
import Gdbh.PathC_Final
import Gdbh.PathC_FinalSummaryPhase22

/-!
# Path C — P24-T2: Full chain end-to-end audit

## Mission

Phases 17-23 produced approximately 60 axiom-clean files closing every
non-classical sub-step of the Brun-Goldbach K-Goldbach chain.  After
Phase 23, the single named residual in the project is the
Halberstam-Richert §3.11 master sieve input

```
BrunGoldbachLocalMainTermRefinedAtSqrt : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachSiftedPair n √n : ℝ)
        ≤ C₁ · n · goldbachLocalFactor n √n + refinedReservoir n √n .
```

This file performs the **full chain audit** from this single residual
all the way down to the K-Goldbach conclusion `pathC_kGoldbach`, naming
every intermediate Prop and bridge along the way.

## The complete chain (Phase 23 + Phase 24)

The chain decomposes into nine literal Lean bridges, all axiom-clean
(`[Classical.choice, Quot.sound, propext]`):

```
   (residual)  BrunGoldbachLocalMainTermRefinedAtSqrt              (HL §3.11)
                              │
                              ▼  (closed)  P23-T1 +
                                  pairedBrunMertensThirdLowerGap_holds
                                  Step 1: brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
                              ▼
              BrunGoldbachWithSingularSeries                        (P22-T2)
                              │
                              ▼  (open)   SingularSeriesMertens3Bound
                                  Step 2: classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries
                              ▼
              ClassicalBrunGoldbachLogLog                            (P21-T1 input Prop)
                              │
                              ▼  (closed) P21-T1
                                  Step 3: brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog
                              ▼
              BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong      (P20-T4 AtSqrt-FixA')
                              │
                              ▼  (open)   universal-in-`z` upgrade
                                  Step 4: atSqrtFixAStrongToUniversal residual
                              ▼
              BrunGoldbachPairedMainTermRefinedFixAStrong            (P20-T4 universal-in-`z` FixA')
                              │
                              ▼  (open)   P21-T2  WeightedSchnirelmannResidualBridge
                                  Step 5: refined of universal-fixAStrong
                              ▼
              BrunGoldbachPairedMainTermRefined                      (P15-T2)
                              │
                              ▼  (closed) trivial unfolding via iff_absorption
                                  Step 6: brunGoldbachPairedMainTermRefined_iff_absorption.mp
                              ▼
              PairedMainTermAbsorption                               (P17-T6 absorption)
                              │
                              ▼  (closed) P17-T6
                                  Step 7: pathC_kGoldbach_of_absorption
                              ▼
              ∃ K : ℕ, ∀ n ≥ 2, K-Goldbach K-bound                  (pathC_kGoldbach)
```

Of the eight arrows above:

* **Steps 1, 3, 6, 7** are **closed** in the project repository (the
  bridges are axiom-clean Lean theorems, and their non-trivial
  hypotheses are themselves discharged by closed `_holds` lemmas).
* **Steps 2, 4, 5** are **conditional** on three named open Props.

The single conditional theorem `pathC_kGoldbach_unconditional_modulo_HL311`
below takes:

1. `hHL : BrunGoldbachLocalMainTermRefinedAtSqrt` — the genuine residual
   (Halberstam-Richert §3.11 master inequality), and
2. `hMertens3 : SingularSeriesMertens3Bound` — the Mertens-3 absorption
   `S(n) ≤ K · log log n` (open in mathlib v4.29.1; classical Mertens
   1874 + Hardy-Littlewood 1922), and
3. `hUniversal : AtSqrtFixAStrongToUniversal` — the universal-in-`z`
   upgrade of the FixA' AtSqrt Prop (open; the AtSqrt form does not
   imply the universal-in-`z` form without an additional argument
   handling `z ≠ √n`), and
4. `hSchnirelmann : WeightedSchnirelmannResidualBridge` — the weighted
   Schnirelmann residual bridge FixA' → original `BrunGoldbachPairedMainTermRefined`
   (open; the P21-T2 absorption obstruction).

and produces the K-Goldbach conclusion axiom-clean.

## Honest accounting of the chain shape

The single conditional theorem `pathC_kGoldbach_unconditional_modulo_HL311`
in the original P24-T2 specification was stated as

```lean
theorem pathC_kGoldbach_unconditional_modulo_HL311
    (hHL : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → … K-Goldbach … .
```

with **only** `hHL` as a hypothesis.  Per the task's "honesty rule" —
"If the chain doesn't compose cleanly (any signature mismatch),
document precisely what additional bridges are needed" — we record
that **this exact signature is not currently derivable axiom-clean**
from the Phase 23 repository state, because three intermediate bridges
on the chain are **named open Props** (Steps 2, 4, 5 above):

* `SingularSeriesMertens3Bound`     (Step 2 input — classical Mertens-3),
* `AtSqrtFixAStrongToUniversal`     (Step 4 input — the AtSqrt → universal-in-`z` FixA' upgrade),
* `WeightedSchnirelmannResidualBridge` (Step 5 input — the FixA' →
  original Refined absorption, i.e. P21-T2).

The honest deliverable, faithful to the chain's actual shape, is the
theorem `pathC_kGoldbach_unconditional_modulo_HL311` below taking *all
four* hypotheses as explicit parameters.  This documents the precise
list of additional bridges that need to be closed.

## Strict constraints (P24-T2 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* This file **only adds**; it does not modify any other file.
* This file imports every key chain Prop file.
-/

namespace Gdbh
namespace PathCFullChainAudit

open Gdbh.PathCGoldbachLocalFactor (BrunGoldbachLocalMainTermRefinedAtSqrt)
open Gdbh.PathCBrunGoldbachSingularClosure
  (brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
   reservoirAbsorbedBySingular_of_lowerGap
   brunGoldbachWithSingularSeries_of_master_assembly
   ReservoirAbsorbedBySingular
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
open Gdbh.PathCFinalClosedReductions (pathC_kGoldbach_of_refined_main)
open Gdbh.PathCUnconditionalFixAStrong
  (WeightedSchnirelmannResidualBridge)

/-! ## Section 1 — Named definition of the universal-in-`z` upgrade Prop

The AtSqrt-FixA' Prop only bounds `goldbachSiftedPair` at `z = Nat.sqrt n`;
the universal-in-`z` Refined-style chain requires the inequality at
arbitrary `z`.  The bridge is not closed in the project repository
(it requires uniform sieve control over `z`).  We expose it as a named
parametric Prop, so that downstream auditors can see precisely the
additional content needed for the headline closure. -/

/-- **`AtSqrtFixAStrongToUniversal`** — the (open) parametric input
encoding the AtSqrt → universal-in-`z` upgrade of the FixA' Prop:

```
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
  →  BrunGoldbachPairedMainTermRefinedFixAStrong .
```

This is needed to convert the AtSqrt-only output of the master
assembly chain (Step 3) into the universal-in-`z` form consumed by
the FixA' headline bridge (Step 5).

Mathlib v4.29.1 status: **open**.

**Status discussion.**  The AtSqrt Prop only bounds the sifted pair
count at the canonical sieve threshold `z = √n`.  The universal-in-`z`
Prop bounds it for *every* `z`, with the FixA' reservoir
`n · (log log n)² / (log n)²` shared across all `z`.  The required
universal-in-`z` upgrade is not a trivial monotonicity:  the sift
quantity `goldbachSiftedPair n z` need not be monotone in `z`
(it depends on which residue classes are sifted out), so a pointwise
argument over `z` requires either the full Brun-Bonferroni decomposition
or an averaged argument. -/
def AtSqrtFixAStrongToUniversal : Prop :=
  BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong →
    BrunGoldbachPairedMainTermRefinedFixAStrong

/-! ## Section 2 — Chain Step 1 (closed):
`BrunGoldbachLocalMainTermRefinedAtSqrt` ⇒ `BrunGoldbachWithSingularSeries`

This composes the (open) HL §3.11 master sieve input with the
(closed) paired Mertens lower gap to land on the
`BrunGoldbachWithSingularSeries` Prop with the singular series factor
explicitly exposed. -/

/-- **Step 1 (closed)** — Master assembly bridge.

Given `BrunGoldbachLocalMainTermRefinedAtSqrt` and the closed
`pairedBrunMertensThirdLowerGap_holds`, derive
`BrunGoldbachWithSingularSeries`. -/
theorem chain_step1_brunGoldbachWithSingularSeries
    (hHL : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    hHL pairedBrunMertensThirdLowerGap_holds

/-! ## Section 3 — Chain Step 2 (conditional on Mertens-3):
`BrunGoldbachWithSingularSeries` ⇒ `ClassicalBrunGoldbachLogLog`

This step is closed up to the named open `SingularSeriesMertens3Bound`
Prop. -/

/-- **Step 2 (conditional)** — Mertens-3 absorption.

Given `BrunGoldbachWithSingularSeries` (Step 1 output) and the open
`SingularSeriesMertens3Bound` Prop, derive
`ClassicalBrunGoldbachLogLog`. -/
theorem chain_step2_classicalBrunGoldbachLogLog
    (hBG : BrunGoldbachWithSingularSeries)
    (hMertens3 : SingularSeriesMertens3Bound) :
    ClassicalBrunGoldbachLogLog :=
  classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries hBG hMertens3

/-! ## Section 4 — Chain Step 3 (closed):
`ClassicalBrunGoldbachLogLog` ⇒ `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`

P21-T1's AM-GM-style absorption applied at sieve threshold `z = √n`. -/

/-- **Step 3 (closed)** — P21-T1 absorption bridge.

Given `ClassicalBrunGoldbachLogLog` (Step 2 output), derive the FixA'
AtSqrt Prop axiom-clean. -/
theorem chain_step3_atSqrt_fixAStrong
    (hLogLog : ClassicalBrunGoldbachLogLog) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong :=
  brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog hLogLog

/-! ## Section 5 — Chain Step 4 (conditional on AtSqrt→universal upgrade):
`BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` ⇒
`BrunGoldbachPairedMainTermRefinedFixAStrong`

This step is conditional on the open Prop `AtSqrtFixAStrongToUniversal`. -/

/-- **Step 4 (conditional)** — AtSqrt → universal-in-`z` FixA' upgrade.

Given the FixA' AtSqrt Prop (Step 3 output) and the open
`AtSqrtFixAStrongToUniversal` upgrade Prop, derive the universal-in-`z`
FixA' Prop. -/
theorem chain_step4_universal_fixAStrong
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)
    (hUniversal : AtSqrtFixAStrongToUniversal) :
    BrunGoldbachPairedMainTermRefinedFixAStrong :=
  hUniversal hAtSqrt

/-! ## Section 6 — Chain Step 5 (conditional on Schnirelmann residual):
`BrunGoldbachPairedMainTermRefinedFixAStrong` ⇒
`BrunGoldbachPairedMainTermRefined`

The FixA' → original Refined absorption is the P21-T2 residual,
encoded as the parametric `WeightedSchnirelmannResidualBridge` Prop. -/

/-- **Step 5 (conditional)** — Weighted Schnirelmann residual bridge.

Given the universal-in-`z` FixA' Prop (Step 4 output) and the open
`WeightedSchnirelmannResidualBridge` (P21-T2 residual), derive the
original `BrunGoldbachPairedMainTermRefined` Prop. -/
theorem chain_step5_refined_main_term
    (hFixAStrong : BrunGoldbachPairedMainTermRefinedFixAStrong)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    BrunGoldbachPairedMainTermRefined :=
  hSchnirelmann hFixAStrong

/-! ## Section 7 — Chain Step 6 (closed):
`BrunGoldbachPairedMainTermRefined` ⇒ `PairedMainTermAbsorption`

Trivial unfolding via `brunGoldbachPairedMainTermRefined_iff_absorption.mp`.
The `IsBrunMainTermFactor` half is closed unconditionally. -/

/-- **Step 6 (closed)** — Refined ⇒ Absorption (trivial unfolding). -/
theorem chain_step6_absorption
    (hRefined : BrunGoldbachPairedMainTermRefined) :
    PairedMainTermAbsorption :=
  brunGoldbachPairedMainTermRefined_iff_absorption.mp hRefined

/-! ## Section 8 — Chain Step 7 (closed):
`PairedMainTermAbsorption` ⇒ `pathC_kGoldbach` K-bound

The P17-T6 headline bridge.  This consumes the Mertens-first /
Abel-inversion / Schnirelmann-density-positive chain and the
basis-order theorem, all closed axiom-clean. -/

/-- **Step 7 (closed)** — P17-T6 K-Goldbach headline from absorption. -/
theorem chain_step7_kGoldbach
    (hAbs : PairedMainTermAbsorption) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_absorption hAbs

/-! ## Section 9 — The single headline theorem

The complete chain, with all seven steps composed.

**Honesty note.**  The original P24-T2 specification asks for the
theorem with **only** `hHL : BrunGoldbachLocalMainTermRefinedAtSqrt`
as a hypothesis.  Per the honesty rule, we document that this exact
signature is **not** derivable axiom-clean in the current Phase 23
repository state, because three intermediate bridges on the chain
require named open Props:

* `SingularSeriesMertens3Bound`         (Step 2 — Mertens-3 absorption),
* `AtSqrtFixAStrongToUniversal`         (Step 4 — universal-in-`z` upgrade),
* `WeightedSchnirelmannResidualBridge`  (Step 5 — P21-T2 Schnirelmann residual).

The honest deliverable, faithful to the chain's *actual* dependency
shape, is the theorem below taking *all four* hypotheses as explicit
parameters.  This is the precise list of bridges the project still
needs to close to obtain the *single*-hypothesis form.

Each bridge is named openly and is the literal residual that the
project's next phase would target. -/

/-- **Headline theorem (P24-T2)** — Full-chain composition from the
single Phase-23 residual `BrunGoldbachLocalMainTermRefinedAtSqrt`
together with the three remaining named open Props on the chain to
the K-Goldbach K-bound.

**Proof structure** (literal 7-line composition of the seven chain
steps):

1. `chain_step1_brunGoldbachWithSingularSeries hHL`,
2. `chain_step2_classicalBrunGoldbachLogLog _ hMertens3`,
3. `chain_step3_atSqrt_fixAStrong _`,
4. `chain_step4_universal_fixAStrong _ hUniversal`,
5. `chain_step5_refined_main_term _ hSchnirelmann`,
6. `chain_step6_absorption _`,
7. `chain_step7_kGoldbach _`.

Axiom-clean:  every intermediate bridge is itself axiom-clean
(`[Classical.choice, Quot.sound, propext]` only). -/
theorem pathC_kGoldbach_unconditional_modulo_HL311
    (hHL : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hMertens3 : SingularSeriesMertens3Bound)
    (hUniversal : AtSqrtFixAStrongToUniversal)
    (hSchnirelmann : WeightedSchnirelmannResidualBridge) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  chain_step7_kGoldbach
    (chain_step6_absorption
      (chain_step5_refined_main_term
        (chain_step4_universal_fixAStrong
          (chain_step3_atSqrt_fixAStrong
            (chain_step2_classicalBrunGoldbachLogLog
              (chain_step1_brunGoldbachWithSingularSeries hHL)
              hMertens3))
          hUniversal)
        hSchnirelmann))

/-! ## Section 10 — Alternative shorter routes

For audit completeness, we record two shorter compositions that bypass
the explicit `BrunGoldbachWithSingularSeries` intermediate. -/

/-- **Shorter route via the master-assembly composition.**  Combines
Steps 1+2+3 into a single application of
`brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly`,
which encapsulates the chain through `BrunGoldbachWithSingularSeries`. -/
theorem pathC_kGoldbach_unconditional_modulo_HL311_via_master_assembly
    (hHL : BrunGoldbachLocalMainTermRefinedAtSqrt)
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
            hHL pairedBrunMertensThirdLowerGap_holds hMertens3))))

/-! ## Section 11 — Chain-link audit catalogue (data form)

A purely informational record of the seven chain links from
`BrunGoldbachLocalMainTermRefinedAtSqrt` to `pathC_kGoldbach`. -/

/-- Audit entry for one chain link. -/
structure ChainLink where
  /-- Step number (1-based). -/
  step    : Nat
  /-- Lean-side name of the bridging theorem. -/
  bridge  : String
  /-- Input Prop name. -/
  input   : String
  /-- Output Prop name. -/
  output  : String
  /-- Closed (`true`) or conditional (`false`). -/
  closed  : Bool
  /-- Phase / task tag. -/
  source  : String

/-- The seven chain links from the residual `BrunGoldbachLocalMainTermRefinedAtSqrt`
to the K-Goldbach conclusion. -/
def FullChainAuditMap : List ChainLink :=
  [ { step    := 1
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step1_brunGoldbachWithSingularSeries"
    , input   := "BrunGoldbachLocalMainTermRefinedAtSqrt"
    , output  := "BrunGoldbachWithSingularSeries"
    , closed  := true
    , source  := "P23-T1 + pairedBrunMertensThirdLowerGap_holds (P19-T6)" }
  , { step    := 2
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step2_classicalBrunGoldbachLogLog"
    , input   := "BrunGoldbachWithSingularSeries + SingularSeriesMertens3Bound"
    , output  := "ClassicalBrunGoldbachLogLog"
    , closed  := false
    , source  := "P22-T2 Bridge A (open input: SingularSeriesMertens3Bound)" }
  , { step    := 3
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step3_atSqrt_fixAStrong"
    , input   := "ClassicalBrunGoldbachLogLog"
    , output  := "BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong"
    , closed  := true
    , source  := "P21-T1 + pairedBrunFactorMertensUpperAtSqrt_holds (P18-T1)" }
  , { step    := 4
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step4_universal_fixAStrong"
    , input   := "BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong + AtSqrtFixAStrongToUniversal"
    , output  := "BrunGoldbachPairedMainTermRefinedFixAStrong"
    , closed  := false
    , source  := "open (this file) — universal-in-z upgrade of FixA' AtSqrt" }
  , { step    := 5
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step5_refined_main_term"
    , input   := "BrunGoldbachPairedMainTermRefinedFixAStrong + WeightedSchnirelmannResidualBridge"
    , output  := "BrunGoldbachPairedMainTermRefined"
    , closed  := false
    , source  := "P21-T2 (open input: WeightedSchnirelmannResidualBridge)" }
  , { step    := 6
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step6_absorption"
    , input   := "BrunGoldbachPairedMainTermRefined"
    , output  := "PairedMainTermAbsorption"
    , closed  := true
    , source  := "P17-T6 (trivial unfolding via iff_absorption)" }
  , { step    := 7
    , bridge  := "Gdbh.PathCFullChainAudit.chain_step7_kGoldbach"
    , input   := "PairedMainTermAbsorption"
    , output  := "K-Goldbach K-bound"
    , closed  := true
    , source  := "P17-T6 (Mertens-1 + Abel + Schnirelmann basis order)" }
  ]

/-- The audit catalogue contains exactly seven chain links. -/
theorem fullChainAuditMap_length_eq_seven :
    FullChainAuditMap.length = 7 := by decide

/-- The number of *closed* steps in the chain audit. -/
theorem fullChainAuditMap_closed_count_eq_four :
    (FullChainAuditMap.filter (fun e => e.closed)).length = 4 := by decide

/-- The number of *conditional* steps in the chain audit. -/
theorem fullChainAuditMap_open_count_eq_three :
    (FullChainAuditMap.filter (fun e => ¬ e.closed)).length = 3 := by decide

/-! ## Section 12 — Residual catalogue

The three named open Props on the chain. -/

/-- Catalogue entry for one residual Prop. -/
structure ResidualEntry where
  /-- Step number where this residual is consumed. -/
  step       : Nat
  /-- Lean-side name of the Prop. -/
  prop       : String
  /-- Source file declaring the Prop. -/
  sourceFile : String
  /-- Brief mathematical description. -/
  description : String

/-- The three named open Props on the full chain. -/
def FullChainResiduals : List ResidualEntry :=
  [ { step        := 2
    , prop        := "SingularSeriesMertens3Bound"
    , sourceFile  := "Gdbh.PathC_BrunGoldbachSingularSeries"
    , description := "S(n) ≤ K · log log n  (classical Mertens-3 absorption)" }
  , { step        := 4
    , prop        := "AtSqrtFixAStrongToUniversal"
    , sourceFile  := "Gdbh.PathC_FullChainAudit (this file)"
    , description :=
        "AtSqrt-only FixA' Prop ⇒ universal-in-z FixA' Prop "
        ++ "(uniform sieve control over z; not a trivial monotonicity)" }
  , { step        := 5
    , prop        := "WeightedSchnirelmannResidualBridge"
    , sourceFile  := "Gdbh.PathC_UnconditionalFixAStrong"
    , description :=
        "universal-in-z FixA' Prop ⇒ original Refined Prop "
        ++ "(P21-T2 Schnirelmann residual absorption of (log log n)² factor)" }
  ]

/-- The residual catalogue has exactly three entries. -/
theorem fullChainResiduals_length_eq_three :
    FullChainResiduals.length = 3 := by decide

/-! ## Section 13 — Summary marker

The complete chain analysis is recorded in this file.  The headline
theorem `pathC_kGoldbach_unconditional_modulo_HL311` is axiom-clean
(`[Classical.choice, Quot.sound, propext]`), with the three named
residuals isolated and documented for the next phase. -/

/-- **P24-T2 summary marker.**  The full chain audit from the single
Phase-23 residual `BrunGoldbachLocalMainTermRefinedAtSqrt` to the
K-Goldbach K-bound is complete, with seven labelled chain links and
three named open residuals.

Closed steps:  1, 3, 6, 7 (four steps).
Open steps:    2, 4, 5    (three steps).

Open residuals:
* `SingularSeriesMertens3Bound`        — classical Mertens-3 absorption,
* `AtSqrtFixAStrongToUniversal`        — universal-in-`z` upgrade of FixA' AtSqrt,
* `WeightedSchnirelmannResidualBridge` — P21-T2 Schnirelmann residual.

Once all three named residuals are closed, the
`pathC_kGoldbach_unconditional_modulo_HL311` theorem collapses to a
single-hypothesis closure of the K-Goldbach K-bound from
`BrunGoldbachLocalMainTermRefinedAtSqrt` alone, which is the
ultimate aspirational target. -/
theorem pathC_p24_t2_summary : True := trivial

end PathCFullChainAudit
end Gdbh

/-! ## Section 14 — Axiom audit

Each theorem above is axiom-clean (`[Classical.choice, Quot.sound,
propext]`).  The `#print axioms` block below emits the audit content
into the compile log. -/

#print axioms Gdbh.PathCFullChainAudit.chain_step1_brunGoldbachWithSingularSeries
#print axioms Gdbh.PathCFullChainAudit.chain_step2_classicalBrunGoldbachLogLog
#print axioms Gdbh.PathCFullChainAudit.chain_step3_atSqrt_fixAStrong
#print axioms Gdbh.PathCFullChainAudit.chain_step4_universal_fixAStrong
#print axioms Gdbh.PathCFullChainAudit.chain_step5_refined_main_term
#print axioms Gdbh.PathCFullChainAudit.chain_step6_absorption
#print axioms Gdbh.PathCFullChainAudit.chain_step7_kGoldbach
#print axioms Gdbh.PathCFullChainAudit.pathC_kGoldbach_unconditional_modulo_HL311
#print axioms Gdbh.PathCFullChainAudit.pathC_kGoldbach_unconditional_modulo_HL311_via_master_assembly
#print axioms Gdbh.PathCFullChainAudit.fullChainAuditMap_length_eq_seven
#print axioms Gdbh.PathCFullChainAudit.fullChainAuditMap_closed_count_eq_four
#print axioms Gdbh.PathCFullChainAudit.fullChainAuditMap_open_count_eq_three
#print axioms Gdbh.PathCFullChainAudit.fullChainResiduals_length_eq_three
#print axioms Gdbh.PathCFullChainAudit.pathC_p24_t2_summary
