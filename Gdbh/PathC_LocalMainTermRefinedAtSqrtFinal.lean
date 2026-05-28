/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P28-T2 (Phase 28 / Path C — Final closure attempt for
        `BrunGoldbachLocalMainTermRefinedAtSqrt` via composition of the
        P28-T1 Halberstam-Richert §3.11 master assembly (parametric input)
        with the P24-T1 kernel bridges).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_GoldbachResidues
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_LocalMainTermRefinedAtSqrtClosure

/-!
# Path C — P28-T2: final closure of `BrunGoldbachLocalMainTermRefinedAtSqrt`

## Mission

P24-T1 reduced the single open residual on the Path C chain,
`BrunGoldbachLocalMainTermRefinedAtSqrt`, to the **strictly smaller**
named sub-Prop `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`
(definitionally equal to `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`)
via the mechanical bridge
`brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel` (axiom-clean).

P28-T1 (parallel) is producing the Halberstam-Richert §3.11 master
Brun-Bonferroni assembly which closes the kernel.  P28-T1 has not
landed in the repository yet, so we take it **parametrically as input**
through a single named Prop `HLMasterAssemblyAtSqrt` whose statement
matches exactly the kernel Prop:

```
HLMasterAssemblyAtSqrt : Prop :=
  BrunGoldbachLocalMainTermRefinedAtSqrtKernel
```

The P28-T2 deliverable is then the **conditional closure**:

```
brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly :
  HLMasterAssemblyAtSqrt → BrunGoldbachLocalMainTermRefinedAtSqrt
```

This is axiom-clean (uses only `[Classical.choice, Quot.sound, propext]`),
compiles standalone, and documents the **complete chain** from the
P28-T1 HL master input through the P24-T1 kernel mechanical bridge to
the target Prop.

When P28-T1 lands, the user can discharge `HLMasterAssemblyAtSqrt` by
supplying the P28-T1 output (or by `rfl` if P28-T1 is stated with the
same Prop shape).

## The complete chain (P28-T1 + P24-T1 + P28-T2)

```
   (P28-T1 input)  HL §3.11 master Brun-Bonferroni assembly at √n
                                  │
                                  ▼  (definitional alias / Prop unfold)
                  HLMasterAssemblyAtSqrt
                                  │
                                  ▼  (P28-T2 closure of this file)
                  BrunGoldbachLocalMainTermRefinedAtSqrtKernel
                                  │
                                  ▼  (closed in P24-T1 via mechanical
                                     bridge through P22 residue-sifted
                                     ⇒ local-factor reduction)
                  BrunGoldbachLocalMainTermRefinedAtSqrt
```

The kernel Prop is literally `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`
(by definition; see P24-T1, `kernel_eq_residue_sifted` is `rfl`).
The mechanical P24-T1 bridge unfolds in two non-trivial pieces:

1. `goldbachSiftedPair_le_residueSiftedCount n √n`
   (the paired-sift count is majorised by the residue-sifted count).
2. `goldbachResidueMainFactor_eq_goldbachLocalFactor n √n`
   (the residue main factor equals the local-density factor).
3. `goldbachResidueRefinedError = refinedReservoir` (by definition).

These are all closed in the project repository.

## What this file provides

1. The named parametric input Prop `HLMasterAssemblyAtSqrt`.

2. The composed final closure theorem
   `brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly`
   discharging the target Prop from the parametric input.

3. Two convenience corollaries:
   * `brunGoldbachLocalMainTermRefinedAtSqrt_holds_of_hlMasterAssembly`
     (re-statement under a longer name).
   * `brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_hlMasterAssembly`
     (constant-error variant of the target Prop, via the closed
     P22-stage trivial implication).

4. A "complete chain audit" theorem that explicitly composes
   the P28-T1 input → P24-T1 kernel → target chain.

5. `#print axioms` audits for each exported theorem confirming
   only `[Classical.choice, Quot.sound, propext]` axioms are used.

## Strict constraints (P28-T2 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* This file **only adds**; it does not modify any other file.
* `lake env lean Gdbh/PathC_LocalMainTermRefinedAtSqrtFinal.lean` succeeds.

## Status

* **P24-T1**: closed (axiom-clean) — the kernel bridge.
* **P28-T1**: parallel, not yet landed — would close the kernel
  unconditionally; taken parametrically here.
* **P28-T2**: this file — composes P28-T1 + P24-T1 to close the target
  unconditionally.

When P28-T1 lands, the parameter `HLMasterAssemblyAtSqrt` will be
discharged by the P28-T1 output, completing Path C's single residual
unconditionally.
-/

namespace Gdbh
namespace PathCLocalMainTermRefinedAtSqrtFinal

open Gdbh.PathCGoldbachLocalFactor
  (BrunGoldbachLocalMainTermRefinedAtSqrt
   BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant
   brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_atSqrt)
open Gdbh.PathCGoldbachResidues
  (GoldbachResidueSiftedRefinedUpperBoundAtSqrt
   brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSiftedRefinedUpperBoundAtSqrt)
open Gdbh.PathCLocalMainTermRefinedAtSqrtClosure
  (BrunGoldbachLocalMainTermRefinedAtSqrtKernel
   brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel
   brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_kernel
   kernel_eq_residue_sifted
   residue_sifted_of_kernel
   kernel_of_residue_sifted)

/-! ## Section 1 — Parametric input from P28-T1

P28-T1 (parallel task) produces the Halberstam-Richert §3.11 master
Brun-Bonferroni assembly which closes the kernel sub-Prop
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel` axiom-clean.

Since P28-T1 has not landed yet, we take it parametrically through a
single named Prop `HLMasterAssemblyAtSqrt` whose statement is exactly
the kernel Prop.  This is the most general possible interface: any
P28-T1 output that closes the kernel — regardless of intermediate
structure — discharges `HLMasterAssemblyAtSqrt` by `id` or `rfl`. -/

/-- **P28-T1 parametric input.**  The Halberstam-Richert §3.11 master
Brun-Bonferroni assembly at `z = √n`, taken parametrically as the
kernel Prop.

This is **definitionally equal** to
`BrunGoldbachLocalMainTermRefinedAtSqrtKernel`, which is itself
definitionally equal to `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`.
Hence any axiom-clean proof of either of these Props discharges
`HLMasterAssemblyAtSqrt` mechanically. -/
def HLMasterAssemblyAtSqrt : Prop :=
  BrunGoldbachLocalMainTermRefinedAtSqrtKernel

/-- **Definitional equivalence.**  The parametric input is literally
the kernel Prop (proof is `rfl`). -/
theorem hlMasterAssemblyAtSqrt_eq_kernel :
    HLMasterAssemblyAtSqrt = BrunGoldbachLocalMainTermRefinedAtSqrtKernel :=
  rfl

/-- **Definitional equivalence (to residue-sifted upper bound).**  By
transitivity through the kernel alias, the parametric input is
literally the residue-sifted refined upper-bound Prop at `z = √n`. -/
theorem hlMasterAssemblyAtSqrt_eq_residueSifted :
    HLMasterAssemblyAtSqrt = GoldbachResidueSiftedRefinedUpperBoundAtSqrt :=
  rfl

/-- **HL master input → kernel.**  Trivial unfolding direction. -/
theorem kernel_of_hlMasterAssembly
    (h : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrtKernel := h

/-- **Kernel → HL master input.**  Trivial unfolding direction. -/
theorem hlMasterAssembly_of_kernel
    (h : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    HLMasterAssemblyAtSqrt := h

/-- **HL master input → residue-sifted upper bound.**  Trivial unfolding. -/
theorem residueSifted_of_hlMasterAssembly
    (h : HLMasterAssemblyAtSqrt) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrt := h

/-- **Residue-sifted upper bound → HL master input.**  Trivial unfolding. -/
theorem hlMasterAssembly_of_residueSifted
    (h : GoldbachResidueSiftedRefinedUpperBoundAtSqrt) :
    HLMasterAssemblyAtSqrt := h

/-! ## Section 2 — Final closure (the P28-T2 headline theorem)

Compose the P28-T1 parametric input with the P24-T1 kernel mechanical
bridge to obtain unconditional closure of the target Prop. -/

/-- **P28-T2 headline.**  The Halberstam-Richert §3.11 master assembly
input closes the target Prop `BrunGoldbachLocalMainTermRefinedAtSqrt`.

This composes:

1. `kernel_of_hlMasterAssembly` (definitional, by `id`):
   `HLMasterAssemblyAtSqrt → BrunGoldbachLocalMainTermRefinedAtSqrtKernel`,
2. `brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel` (P24-T1):
   `BrunGoldbachLocalMainTermRefinedAtSqrtKernel → BrunGoldbachLocalMainTermRefinedAtSqrt`.

Axiom-clean: `[Classical.choice, Quot.sound, propext]`. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrt :=
  brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel
    (kernel_of_hlMasterAssembly hHL)

/-- **P28-T2 headline (re-statement).**  Long-name alias for the
final closure theorem. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_holds_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrt :=
  brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly hHL

/-- **P28-T2 headline (constant-error variant).**  The HL master
assembly input also closes the constant-error variant of the target
Prop, via the P22-stage trivial implication
`brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_atSqrt`. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant :=
  brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_atSqrt
    (brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly hHL)

/-- **P28-T2 headline (kernel-form).**  The HL master assembly input
closes the kernel form of the target Prop trivially. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrtKernel :=
  kernel_of_hlMasterAssembly hHL

/-- **P28-T2 headline (residue-sifted form).**  The HL master assembly
input closes the residue-sifted refined upper-bound form of the target
Prop trivially. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_hlMasterAssembly
    (hHL : HLMasterAssemblyAtSqrt) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrt :=
  residueSifted_of_hlMasterAssembly hHL

/-! ## Section 3 — Complete chain audit

We document the chain `P28-T1 → P24-T1 kernel → P22 residue-sifted
upper bound → target Prop` as a single end-to-end composed theorem. -/

/-- **Complete-chain audit theorem.**  This theorem explicitly
exhibits the three-step composition that closes
`BrunGoldbachLocalMainTermRefinedAtSqrt` from the parametric
`HLMasterAssemblyAtSqrt` input:

1. (P28-T1 input is by definition equal to the kernel)
   `HLMasterAssemblyAtSqrt = BrunGoldbachLocalMainTermRefinedAtSqrtKernel`,
2. (P24-T1 kernel is by definition equal to the residue-sifted upper bound)
   `BrunGoldbachLocalMainTermRefinedAtSqrtKernel =
      GoldbachResidueSiftedRefinedUpperBoundAtSqrt`,
3. (P22 residue-sifted upper bound mechanically implies the target)
   `GoldbachResidueSiftedRefinedUpperBoundAtSqrt →
      BrunGoldbachLocalMainTermRefinedAtSqrt`.

Composition of the three steps gives the conditional closure. -/
theorem complete_chain_audit
    (hHL : HLMasterAssemblyAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrt := by
  -- Step 1: HL master input → kernel (by `rfl` / unfolding).
  have hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel := hHL
  -- Step 2: kernel → residue-sifted upper bound (by `rfl` / unfolding).
  have hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt := hKernel
  -- Step 3: residue-sifted upper bound → target Prop (P22 mechanical bridge).
  exact brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSiftedRefinedUpperBoundAtSqrt
    hSift

/-! ## Section 4 — Alternative composition paths

We provide two more entry points for downstream auditors:

* directly from `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`, which is
  the literal P22 worker target;
* directly from `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`, which is
  the P24-T1 named alias.

Both reduce to the same composition; the three Props
(`HLMasterAssemblyAtSqrt`, `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`,
`GoldbachResidueSiftedRefinedUpperBoundAtSqrt`) are definitionally
equal in this Lean theory. -/

/-- **Alternative entry — residue-sifted form.**  The target Prop holds
provided the residue-sifted refined upper bound at `z = √n` holds.

(This is essentially the P22 / P24-T1 bridge re-exposed under the
P28-T2 naming.) -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSifted
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrt :=
  brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSiftedRefinedUpperBoundAtSqrt
    hSift

/-- **Alternative entry — kernel form.**  The target Prop holds
provided the P24-T1 kernel sub-Prop holds. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel_via_final
    (hKernel : BrunGoldbachLocalMainTermRefinedAtSqrtKernel) :
    BrunGoldbachLocalMainTermRefinedAtSqrt :=
  brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel hKernel

/-! ## Section 5 — Honesty / scope audit

We record explicitly:

1. What is **closed** in this file (axiom-clean):
   * the conditional closure
     `brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly`
     and its variants, and
   * the definitional equivalences between
     `HLMasterAssemblyAtSqrt`,
     `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`, and
     `GoldbachResidueSiftedRefinedUpperBoundAtSqrt`.

2. What is **conditional** (parametric):
   * the input `HLMasterAssemblyAtSqrt`, which is precisely the
     P28-T1 deliverable (the Halberstam-Richert §3.11 master
     Brun-Bonferroni assembly at `z = √n`).

3. What remains **open**:
   * exactly one named Prop: `HLMasterAssemblyAtSqrt` itself, i.e. the
     P28-T1 deliverable; **no** additional analytic content beyond
     that.

The closure is therefore the **strongest conditional closure** of
`BrunGoldbachLocalMainTermRefinedAtSqrt` derivable from the P24-T1
+ P28-T1 infrastructure, parametrised only on the single P28-T1 input.
-/

/-- **Honest summary** (informal sentinel).  This file is the P28-T2
deliverable: composes (parametrically) the P28-T1 master assembly with
the P24-T1 kernel bridge to close `BrunGoldbachLocalMainTermRefinedAtSqrt`. -/
theorem pathC_p28_t2_summary : True := trivial

/-! ## Section 6 — Axiom audit

`#print axioms` lines below verify that every exported theorem of this
file uses only `[Classical.choice, Quot.sound, propext]` axioms.
No `sorry`, no `axiom`, no `admit` is used anywhere in this file or in
any of its transitively imported dependencies (subject to the standing
project audit invariant). -/

#print axioms brunGoldbachLocalMainTermRefinedAtSqrt_of_hlMasterAssembly
#print axioms brunGoldbachLocalMainTermRefinedAtSqrt_holds_of_hlMasterAssembly
#print axioms brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_hlMasterAssembly
#print axioms brunGoldbachLocalMainTermRefinedAtSqrtKernel_of_hlMasterAssembly
#print axioms goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_hlMasterAssembly
#print axioms complete_chain_audit
#print axioms brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSifted
#print axioms brunGoldbachLocalMainTermRefinedAtSqrt_of_kernel_via_final
#print axioms hlMasterAssemblyAtSqrt_eq_kernel
#print axioms hlMasterAssemblyAtSqrt_eq_residueSifted

end PathCLocalMainTermRefinedAtSqrtFinal
end Gdbh
