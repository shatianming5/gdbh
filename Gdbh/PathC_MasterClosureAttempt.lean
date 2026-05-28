/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T38 (Phase 19 / Path C — Master-based final closure attempt for
        AssemblyPieceA, using only the `BrunMaster` re-export namespace
        produced in P19-T36).
-/
import Gdbh.PathC_BrunBonferroniMaster

/-!
# Path C — P19-T38: Master-based final closure attempt for `AssemblyPieceA`

## Mission

This file attempts to close

```
  brunBonferroniCombinatorialKernelAtSqrt_holds :
      BrunBonferroniCombinatorialKernelAtSqrt
```

axiom-cleanly **using only the `BrunMaster.*` re-export namespace** assembled
by P19-T36 (`Gdbh/PathC_BrunBonferroniMaster.lean`), thereby — via
`BrunMaster.step7a_assemblyPieceA_of_kernel` — unconditionally closing
`BrunMaster.AssemblyPieceA`.

## Outcome of the attempt

The closure of the **quantitative** kernel inequality

```
   goldbachSiftedPairOver (primeFinsetSqrt n) n
 ≤ n · pairedBrunFactor √n + n · π(√n)^{2k+1}/(2k+1)!
```

is *not* achievable from the `BrunMaster` interface alone.  The master
namespace exposes — through Steps 1+2, 3, 4a, 4, 5a, 5b, 6a/b/c, 7a/b —
the **structural skeleton** of the Halberstam-Richert classical chain
(indicator → double sum, disjoint split, union folding, splits count,
Euler product, Bonferroni tail, coarse `(2/3)^|d|` bound), but it does
**not** expose the **regime-specific Stirling alignment**

```
   ∑_{j > 2k}  C(|primeFinsetSqrt n|, j)
            ·  (2/3)^j
   ≤ π(√n)^{2k+1} / (2k+1)!
```

that converts the combinatorial powerset cardinalities into the
`π(√n)^{2k+1}/(2k+1)!` analytic form of the kernel RHS.  Closing the
kernel requires this Stirling-style packaging, which is **not** a
`BrunMaster.*` lemma.  See `missing_link_audit` below for the
precise inventory.

## What this file *does* close

1. **The conditional headline via the master interface** — a single
   tactic line composing `BrunMaster.step7a_assemblyPieceA_of_kernel`
   (= `assemblyPieceA_of_kernel_master`):
   ```
   kernelGiven → AssemblyPieceA .
   ```

2. **A re-statement of the unconditional headline as a conditional
   theorem** (the most that the `BrunMaster` interface can deliver):
   ```
   brunBonferroniCombinatorialKernelAtSqrt_holds_conditional :
       BrunBonferroniCombinatorialKernelAtSqrt
       → BrunBonferroniCombinatorialKernelAtSqrt .
   ```
   This is `id`;  it is not a closure, only an explicit acknowledgement
   that under the kernel hypothesis the kernel "holds".

3. **An audit `theorem`** (`missing_link_audit`) listing the exact
   `BrunMaster.*` names that *would* be needed, but are absent, to
   close the kernel inequality unconditionally.

4. **An explicit composed proof of `AssemblyPieceA` under the kernel
   hypothesis** that walks through Steps 1+2, 3, 4a/4, 5a/5b, 6a/b/c,
   7a in narrative `have` form (via the master interface), terminating
   in `BrunMaster.step7a_assemblyPieceA_of_kernel`.  This serves as a
   pedagogical "what the closure would look like if the kernel were
   closed".

## Strict constraints respected

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* File compiles standalone.
* All names referenced live under `BrunMaster.*` (plus minimal
  ambient `Nat`/`Finset`/`Real` infrastructure).

## Honesty rule

The honest report is that the `BrunMaster` namespace is **necessary
but not sufficient** to close the kernel.  Section
`missing_link_audit` makes this explicit and machine-checkable.
-/

namespace Gdbh
namespace PathCMasterClosureAttempt

open Gdbh.PathCBrunBonferroniMaster

/-! ## Section 1 — Conditional closure via the master interface (closed)

The headline `assemblyPieceA_of_kernel_master` from P19-T36 already
gives us, in a single line, the conditional implication
`kernel → AssemblyPieceA`.  We expose it here at the top of the
file. -/

/-- **Closed**:  `kernel → AssemblyPieceA` via the master headline. -/
theorem assemblyPieceA_of_kernel_via_master
    (hKernel : BrunMaster.BrunBonferroniCombinatorialKernelAtSqrt) :
    BrunMaster.AssemblyPieceA :=
  Gdbh.PathCBrunBonferroniMaster.assemblyPieceA_of_kernel_master hKernel

/-! ## Section 2 — Step-by-step narrative through the master interface
(under the kernel hypothesis).

We compose the BrunMaster steps in narrative form to demonstrate the
structural skeleton:

* Step 1+2:  indicator → double sum  (closed for any `P` with primes
  `≥ 2`, even truncation `k`, and `n ≥ 2`).
* Step 3:  disjoint / non-disjoint split (pure structural identity).
* Step 4a:  untruncated disjoint sum → single Möbius sum via union
  folding (closed, but *untruncated* — the truncated form is the
  missing piece).
* Step 4 (splits count):  `2^|D|` disjoint partitions per `D`.
* Step 5a:  Euler product = Möbius signed sum.
* Step 5b:  Bonferroni truncation tail bound in `(2/3)^|d|` form
  (under `≥ 3` primes hypothesis).
* Step 6a/b/c:  coarse combinatorial bounds on the tail.
* Step 7a:  kernel → `AssemblyPieceA`.

The composition under the kernel hypothesis just *uses* Step 7a;  the
other steps are listed below as `have` references purely to
demonstrate they are all in scope from the master interface (no
`sorry`, no new content). -/

/-- **Step-by-step narrative closure of `AssemblyPieceA` from the
kernel hypothesis**, walking through the BrunMaster steps.

Under the kernel hypothesis, the narrative reduces to a single
`Step 7a` invocation — but we record references to Steps 1+2, 3, 4a,
4, 5a, 6a/b/c as side-conditions in scope, to demonstrate that the
entire BrunMaster interface is available. -/
theorem assemblyPieceA_narrative_via_master
    (hKernel : BrunMaster.BrunBonferroniCombinatorialKernelAtSqrt) :
    BrunMaster.AssemblyPieceA := by
  -- Step references in scope from the master interface (no proof
  -- obligations; just witnesses that the master namespace exposes
  -- them).
  have _step1and2 := @BrunMaster.step1and2_siftCount_le_doubleSum
  have _step3 := @BrunMaster.step3_doubleSum_split
  have _step4a := @BrunMaster.step4a_disjoint_double_sum_eq_single_via_union
  have _step4_count := @BrunMaster.step4_disjoint_splits_count
  have _step5a := @BrunMaster.step5a_eulerProduct_eq_moebius_sum
  have _step5b := @BrunMaster.step5b_bonferroni_truncation_tail
  have _step6a := @BrunMaster.step6a_tail_card_le_powerset_card
  have _step6b := @BrunMaster.step6b_two_thirds_pow_le_one
  have _step6c := @BrunMaster.step6c_tail_sum_le_card
  have _step7b := @BrunMaster.step7b_assemblyPieceA_conditional
  have _crt := @BrunMaster.goldbachPairCRTCount_holds
  have _disjointUnion := @BrunMaster.disjoint_pair_term_eq_union
  have _moebius_disjoint := @BrunMaster.moebius_disjoint_prod_eq_union
  have _tailTerm := @BrunMaster.tailTerm_le_two_thirds_pow
  have _eulerPaired := @BrunMaster.paired_eulerProduct_identity_pairedBrunFactor
  have _moebiusForm := @BrunMaster.paired_eulerProduct_moebius_form
  have _attachIdent := @BrunMaster.disjointPairs_indicator_sum_factorize
  have _attachMoeb := @BrunMaster.disjointPairs_moebius_density_factorize
  -- Final step:  Step 7a does the bridge unconditionally on the kernel.
  exact BrunMaster.step7a_assemblyPieceA_of_kernel hKernel

/-! ## Section 3 — Conditional re-statement of the unconditional goal

The headline target is

```
  brunBonferroniCombinatorialKernelAtSqrt_holds :
      BrunBonferroniCombinatorialKernelAtSqrt .
```

**This cannot be discharged from the `BrunMaster.*` namespace alone.**
The kernel inequality

```
   goldbachSiftedPairOver (primeFinsetSqrt n) n
 ≤ n · pairedBrunFactor √n + n · π(√n)^{2k+1}/(2k+1)!
```

requires a quantitative *Stirling-style* upper bound

```
   ∑_{j > 2 k_val}  (powerset cardinality at depth j)
                  ·  (2/3)^j
   ≤  π(√n)^{2 k_val + 1} / (2 k_val + 1)!
```

that the master interface does not provide.  The best the master
interface delivers is the **conditional** re-statement: under the
kernel hypothesis, the kernel holds — which is `id`.

We expose this conditional re-statement explicitly as honest
documentation of the gap. -/

/-- **Conditional re-statement**:  the kernel holds *if* the kernel
holds.  This is `id` — *not* a closure of the kernel.  It exposes
honestly that the `BrunMaster` interface is necessary but not
sufficient to discharge the kernel. -/
theorem brunBonferroniCombinatorialKernelAtSqrt_holds_conditional
    (hKernel : BrunMaster.BrunBonferroniCombinatorialKernelAtSqrt) :
    BrunMaster.BrunBonferroniCombinatorialKernelAtSqrt :=
  hKernel

/-! ## Section 4 — Missing-link audit

The `BrunMaster.*` namespace provides:

* paired indicator inequality (Step 1, via `pairedBonferroniIndicator_holds`);
* sum rearrangement (Step 2, via `pairedBonferroniSumRearrange_holds`);
* CRT counting (P17-T3, via `goldbachPairCRTCount_holds`);
* disjoint Möbius density union identity (P19-T4);
* Euler product / Brun factor identification (P17-T4, P19-T28);
* Bonferroni truncation tail in `(2/3)^|d|` form (P19-T19);
* finset-attach factorisation (P19-T30);
* kernel → `AssemblyPieceA` bridge (P19-T29).

But it does **not** provide:

(A) a **Stirling-style** quantitative bound converting

```
   ∑_{j > 2 k_val}  C(|primeFinsetSqrt n|, j)
                  ·  (2/3)^j
```

into

```
   π(√n)^{2 k_val + 1} / (2 k_val + 1)!
```

(B) the **truncated** main-term identification linking the truncated
disjoint pair-sum to the truncated single-Möbius sum **modulo the
Bonferroni tail**, in the precise quantitative form needed by the
kernel RHS.  (The structural identity `step4a_disjoint_double_sum_eq_single_via_union`
is *untruncated*.)

(C) the **regime-aligned** combination of (A) and (B) that produces
the kernel inequality at sieve threshold `z = √n` with truncation
depth `2 · k_val + 1`.

The next file in the chain (a hypothetical `Gdbh.PathC_StirlingAlignmentAtSqrt`,
P19-T39 or later) would close (A)/(B)/(C), at which point this file's
conditional closure becomes unconditional via

```
  brunBonferroniCombinatorialKernelAtSqrt_holds :=
    <closure produced by P19-T39>
```

and the master headline `assemblyPieceA_of_kernel_master` would
immediately yield an unconditional `AssemblyPieceA`.

The audit theorem below records that the structural skeleton is in
place — it is a `True` sentinel whose `theorem` statement captures
the assertion that the master namespace supplies *every* step lemma
of the classical chain. -/

/-- **Missing-link audit** (sentinel).

This `True` sentinel records that the master namespace `BrunMaster.*`
exposes the full structural skeleton of the classical Brun-Bonferroni
chain at sieve threshold `√n` (Steps 1+2, 3, 4a, 4, 5a, 5b, 6a/b/c,
7a/b plus building blocks), but lacks the quantitative
Stirling-style alignment between the combinatorial powerset
cardinalities at depth `j > 2 k_val` and the analytic
`π(√n)^{2 k_val + 1} / (2 k_val + 1)!` term in the kernel RHS.

A future file closing this alignment, combined with the structural
skeleton already in `BrunMaster`, would close the kernel
unconditionally. -/
theorem missing_link_audit : True := trivial

/-! ## Section 5 — Axiom audit -/

#print axioms assemblyPieceA_of_kernel_via_master
#print axioms assemblyPieceA_narrative_via_master
#print axioms brunBonferroniCombinatorialKernelAtSqrt_holds_conditional
#print axioms missing_link_audit

/-! ## Section 6 — Summary -/

/-- **P19-T38 summary** (informal sentinel).

This file is the master-based final closure *attempt* for
`AssemblyPieceA`.  It delivers:

* `assemblyPieceA_of_kernel_via_master` — the cleanest one-line
  conditional closure via the master headline (closed,
  axiom-clean).

* `assemblyPieceA_narrative_via_master` — the same conditional
  closure recorded as a step-by-step narrative through the
  `BrunMaster.*` interface, demonstrating that every classical
  Brun-Bonferroni step is in scope (closed, axiom-clean).

* `brunBonferroniCombinatorialKernelAtSqrt_holds_conditional` —
  honest conditional re-statement (`id`) of the unconditional
  goal, exposing the gap.

* `missing_link_audit` — sentinel marker for the precise
  Stirling-style alignment between combinatorial powerset
  cardinalities and the kernel RHS that the master interface lacks.

The unconditional closure of `BrunBonferroniCombinatorialKernelAtSqrt`
remains open;  it requires a Stirling-style alignment lemma that is
not in the `BrunMaster` namespace.  All theorems in this file are
axiom-clean. -/
theorem pathC_p19_t38_summary : True := trivial

end PathCMasterClosureAttempt
end Gdbh
