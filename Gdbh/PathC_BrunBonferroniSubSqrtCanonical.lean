/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T16 (Phase 19 / Path C — Canonical Brun-Bonferroni assembly
        at the **SubSqrt** sieve range `z ∈ [3, √n)` with the
        Stirling-aligned truncation depth `k(n) := 2n`.  Exposes the
        GENUINE narrow analytic residual as a single parameterized
        named open Prop, and mechanically closes the surrounding
        bookkeeping.)
-/
import Gdbh.PathC_PairedBonferroniNaturalSubSqrt
import Gdbh.PathC_PairedBonferroniConstantAlign
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBonferroniSumRearrange
import Gdbh.PathC_GoldbachPairCRTCount
import Gdbh.PathC_PairedMainTermAtSqrtReduction
import Gdbh.PathC_PairedMainTermFromLocalDensity
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_PairedBrunStirlingSqrt
import Gdbh.PathC_PairedBrunSmallZ

/-!
# Path C — P19-T16: Canonical Brun-Bonferroni at the SubSqrt slice

This file is the **P19-T16 deliverable** in Phase 19 (Path C closure).
The target is the residual Prop exposed in P19-T12:

```
Gdbh.PathCPairedBonferroniNaturalSubSqrt.PairedBonferroniNaturalSubSqrtCombinatorialKernel
```

namely

```
∀ n z : ℕ, 10 ≤ n → 3 ≤ z → z < Nat.sqrt n →
  (goldbachSiftedPair n z : ℝ)
    ≤ (n : ℝ) * pairedBrunFactor z
      + (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * (2 * n) + 1)
                / ((2 * (2 * n) + 1).factorial : ℝ) .
```

This is the GENUINE classical Brun-Bonferroni inequality at the SubSqrt
slice, with the canonical Halberstam-Richert / Stirling-aligned
truncation depth `k(n) := 2n` **pre-substituted**.  The existential
witness `k(n) = 0` trick (used in P19-T11 to close
`PairedBonferroniNaturalAtSqrt`) is **not available** here — `k` is
fixed.

## Coordination with P19-T14 (AtSqrt)

The parallel task P19-T14 (separate file
`PathC_BrunBonferroniAtSqrtCanonical.lean`) attacks the AtSqrt slice
`z = √n` at the same canonical witness.  The combinatorial content is
**identical** up to specialisation of the threshold `z`.  We therefore
expose a **z-parameterized** named open Prop
`BrunBonferroniNatSubSqrtCanonicalKernel` that captures the genuine
residual at every threshold `z ∈ [3, √n)`, and reduce the canonical
kernel to it.

The single sub-Prop chosen is honestly parameterized: when restricted
to `z = √n` it would specialise to the AtSqrt residual (which P19-T14
exposes separately), modulo the `<` vs `≤` boundary at `z = √n`.

## Strategy: outcome (b) — mechanical assembly with one residual

We follow the same approach used in P19-T12:  the genuine analytic
content is concentrated in a single named open Prop.  Mechanical
surrounding closures are done axiom-cleanly.

### Closed pieces consumed (same as P19-T14)

1. `pairedBonferroniIndicator_holds` (P19-T1) — paired indicator at
   even truncation depth.
2. `pairedBonferroniSumRearrange_holds` (P19-T3) — sum-comm
   rearrangement.
3. `goldbachPairCRTCount_holds` (P17-T3) — paired CRT counting.
4. `paired_eulerProduct_identity_pairedBrunFactor` (P19-T4) — Euler
   product identity for `pairedBrunFactor`.
5. `pairedBrunFactor_pos`, `pairedBrunFactor_le_one`,
   `goldbachSiftedPair_le` — structural sift bounds.

### Mechanical pieces closed in this file

* **Vacuous regime** for `n ∈ [10, 15]`:  the range `z ∈ [3, √n)` is
  empty (already proven in P19-T12 as `subSqrt_range_empty_of_small_n`).
* **Non-negativity** of the RHS main term and truncation tail (already
  proven in P19-T12).
* **Trivial cardinal bound** `goldbachSiftedPair n z ≤ n`.
* **Bridge**:  kernel ⇐ z-parameterized canonical residual.

### Single named open sub-Prop (the genuine residual)

* `BrunBonferroniNatSubSqrtCanonicalKernel` — the z-parameterized
  Brun-Bonferroni assembly at threshold `z ∈ [3, √n)` with canonical
  witness `k(n) := 2n`.  Equivalent in content to the kernel residual
  from P19-T12, but **structured for sharing with P19-T14**.

## Axiom budget

Every theorem in this file is **axiom-clean**.  Transitively, only
`Classical.choice`, `Quot.sound`, and `propext` are used.  No `sorry`,
no `axiom`, no `admit`.  No new mathematical assumptions are
introduced.

## Honesty disclosure

The named open sub-Prop is *equivalent in mathematical strength* to
the P19-T12 kernel residual (`PairedBonferroniNaturalSubSqrtCombinatorialKernel`).
This file does **not** discharge that residual; it exposes it under a
shared name so that a downstream proof of the genuine
Halberstam-Richert sieve estimate would close both T14 and T16
simultaneously.

No existential witness exploitation (k=0 trick) is used.  The
canonical witness `k(n) = 2n` is fixed throughout.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2 (Brun's pure sieve, paired form).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  Theorem 3.11 (canonical paired Brun-Bonferroni at deep truncation).
-/

namespace Gdbh
namespace PathCBrunBonferroniSubSqrtCanonical

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCPairedBonferroniNaturalSubSqrt
  (PairedBonferroniNaturalSubSqrtCombinatorialKernel
   subSqrt_range_empty_of_small_n)

/-! ## Section 1 — The canonical witness `k(n) := 2n`

We bind the canonical Halberstam-Richert truncation depth as a
named definition for reuse.  This matches the choice fixed in the
P19-T12 SubSqrt kernel residual and in the P19-T14 AtSqrt canonical
file. -/

/-- The **canonical** Halberstam-Richert truncation depth at any
sieve threshold `z`.

* `canonicalK n := 2 * n`, so the truncation order `2 * canonicalK n + 1`
  equals `4n + 1` — the same depth handled by
  `pairedBrunStirlingTruncationErrorSqrt_holds` (P17-T5-Sqrt). -/
def canonicalK (n : ℕ) : ℕ := 2 * n

@[simp] lemma canonicalK_def (n : ℕ) : canonicalK n = 2 * n := rfl

/-- Unfolding lemma: `2 * canonicalK n + 1 = 4 * n + 1`. -/
@[simp] lemma canonicalK_exp (n : ℕ) :
    2 * canonicalK n + 1 = 4 * n + 1 := by
  unfold canonicalK
  ring

/-! ## Section 2 — Mechanical non-negativity helpers

These restatements of the natural non-negativity facts are re-exported
here for downstream convenience. -/

/-- **Trivial cardinal bound** (real-valued):
`goldbachSiftedPair n z ≤ n`. -/
theorem goldbachSiftedPair_le_real (n z : ℕ) :
    (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast goldbachSiftedPair_le n z

/-- **Non-negativity of the main term** at threshold `z`. -/
theorem main_term_nonneg (n z : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) * pairedBrunFactor z := by
  refine mul_nonneg ?_ ?_
  · exact Nat.cast_nonneg n
  · exact le_of_lt (pairedBrunFactor_pos z)

/-- **Non-negativity of the truncation tail term** at threshold `z`
and canonical witness `k(n) = 2n`. -/
theorem canonical_tail_nonneg (n z : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
                / ((2 * canonicalK n + 1).factorial : ℝ) := by
  refine div_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · exact Nat.cast_nonneg n
    · positivity
  · exact_mod_cast Nat.zero_le _

/-! ## Section 3 — Vacuous-regime closure

For `n ∈ [10, 15]`, the range `z ∈ [3, √n)` is empty (already proven
in P19-T12).  We package the closure of the kernel for this regime
directly. -/

/-- **Vacuous-regime closure** of the SubSqrt kernel for `n ∈ [10, 15]`.

In this regime `Nat.sqrt n ≤ 3`, so the hypothesis `z < Nat.sqrt n`
combined with `3 ≤ z` is impossible.  The conclusion of the kernel
inequality is therefore vacuously true. -/
theorem subSqrt_kernel_vacuous_of_small_n
    {n : ℕ} (hn_lo : 10 ≤ n) (hn_hi : n ≤ 15) :
    ∀ z : ℕ, 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor z
          + (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
                  / ((2 * canonicalK n + 1).factorial : ℝ) := by
  intro z hz_ge_3 hz_lt_sqrt
  -- Contradiction from P19-T12's `subSqrt_range_empty_of_small_n`.
  exfalso
  exact subSqrt_range_empty_of_small_n hn_lo hn_hi hz_ge_3 hz_lt_sqrt

/-! ## Section 4 — The z-parameterized canonical kernel sub-Prop

This is the genuine analytic residual, structured so that a single
proof would discharge both the SubSqrt slice (this file) and the
AtSqrt slice (P19-T14).

The Prop is **parameterized in z**:  it asserts the canonical
Brun-Bonferroni inequality for every `n ≥ 16` (so the SubSqrt range is
non-empty) and every `z ∈ [3, √n)`.  The truncation depth is fixed at
`canonicalK n = 2n`. -/

/-- **Canonical SubSqrt Brun-Bonferroni inequality** (z-parameterized).

The genuine residual:  for every `n ≥ 16` (so `√n ≥ 4 > 3`, guaranteeing
that the SubSqrt range is non-empty), and every `z ∈ [3, √n)`,

```
goldbachSiftedPair n z  ≤  n · pairedBrunFactor(z)
                              + n · π(z)^(4n+1) / (4n+1)! .
```

This is **the classical paired Brun-Bonferroni inequality** at SubSqrt
threshold and the Stirling-aligned truncation depth `k(n) = 2n`.  Closing
this is mathematically equivalent to closing the Halberstam-Richert
*Sieve Methods* §2.2 paired-sieve estimate.

**Mathlib v4.29.1 status:** named open Prop.  The closed pieces
(P19-T1, T3, T4, P17-T3, T4, T6) provide all components, but their
combined Lean assembly into this single inequality is the substantial
multi-task follow-up. -/
def BrunBonferroniNatSubSqrtCanonicalKernel : Prop :=
  ∀ n z : ℕ, 16 ≤ n → 3 ≤ z → z < Nat.sqrt n →
    (goldbachSiftedPair n z : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor z
        + (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
                / ((2 * canonicalK n + 1).factorial : ℝ)

/-! ## Section 5 — Reduction: kernel ⇐ z-parameterized canonical residual

We mechanically reduce the P19-T12 SubSqrt kernel residual
`PairedBonferroniNaturalSubSqrtCombinatorialKernel` to the
z-parameterized canonical residual
`BrunBonferroniNatSubSqrtCanonicalKernel` by:

1. Treating the vacuous regime `n ∈ [10, 15]` via Section 3.
2. Reducing the non-vacuous regime `n ≥ 16` to the canonical residual.

The depth match is `2 * (2 * n) + 1 = 2 * canonicalK n + 1` (by
`canonicalK_def` and `canonicalK_exp`), so the conclusions agree
definitionally. -/

/-- **Reduction theorem**:  the P19-T12 SubSqrt kernel residual
follows from the z-parameterized canonical residual.

Strategy.
* For `n ∈ [10, 15]`: vacuous regime (Section 3).
* For `n ≥ 16`: apply the canonical residual directly. -/
theorem pairedBonferroniNaturalSubSqrtCombinatorialKernel_of_canonical
    (hCan : BrunBonferroniNatSubSqrtCanonicalKernel) :
    PairedBonferroniNaturalSubSqrtCombinatorialKernel := by
  intro n z hn hz_ge_3 hz_lt_sqrt
  -- Normalise the truncation depth via `canonicalK`.
  -- `2 * (2 * n) + 1 = 2 * canonicalK n + 1`.
  have hExp : 2 * (2 * n) + 1 = 2 * canonicalK n + 1 := by
    unfold canonicalK; ring
  -- Case split on `n ≤ 15` (vacuous) vs `n ≥ 16` (canonical).
  by_cases hn_small : n ≤ 15
  · -- Vacuous regime.
    have hCon :
        (goldbachSiftedPair n z : ℝ)
          ≤ (n : ℝ) * pairedBrunFactor z
            + (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
                    / ((2 * canonicalK n + 1).factorial : ℝ) :=
      subSqrt_kernel_vacuous_of_small_n hn hn_small z hz_ge_3 hz_lt_sqrt
    -- Rewrite back to the original exponent form.
    rw [hExp]
    exact hCon
  · -- Non-vacuous regime:  `n ≥ 16`.
    push_neg at hn_small
    have hn_ge_16 : 16 ≤ n := by omega
    have hCon := hCan n z hn_ge_16 hz_ge_3 hz_lt_sqrt
    rw [hExp]
    exact hCon

/-- **Conditional closure** of `PairedBonferroniNaturalSubSqrtCombinatorialKernel`:
the kernel holds provided the z-parameterized canonical residual holds.

This is the **mechanical assembly** portion of the closure:  the
kernel is reduced to the genuine combinatorial content via case
splitting on the vacuous regime and depth-renormalisation. -/
theorem pairedBonferroniNaturalSubSqrtCombinatorialKernel_holds_of_canonical
    (hCan : BrunBonferroniNatSubSqrtCanonicalKernel) :
    PairedBonferroniNaturalSubSqrtCombinatorialKernel :=
  pairedBonferroniNaturalSubSqrtCombinatorialKernel_of_canonical hCan

/-! ## Section 6 — Forward bridges into the downstream chain

Composing the conditional closure above with the P19-T12 bridges, we
obtain conditional closures of:

* `Gdbh.PathCPairedBonferroniConstantAlign.PairedBonferroniNaturalSubSqrt`
  (the natural assembly Prop), and
* `Gdbh.PathCPairedBrunSubSqrtProof.PairedBonferroniInequalitySubSqrtAlignedWithTail`
  (the aligned-with-tail residual).

These mechanical bridges are exposed for downstream use. -/

/-- **Forward bridge**:  the z-parameterized canonical residual implies
the natural Bonferroni assembly Prop. -/
theorem pairedBonferroniNaturalSubSqrt_of_canonical
    (hCan : BrunBonferroniNatSubSqrtCanonicalKernel) :
    Gdbh.PathCPairedBonferroniConstantAlign.PairedBonferroniNaturalSubSqrt :=
  Gdbh.PathCPairedBonferroniNaturalSubSqrt.pairedBonferroniNaturalSubSqrt_of_kernel
    (pairedBonferroniNaturalSubSqrtCombinatorialKernel_holds_of_canonical hCan)

/-- **End-to-end forward bridge**:  the z-parameterized canonical
residual implies the aligned-with-tail residual from P18-T5. -/
theorem pairedBonferroniInequalitySubSqrtAlignedWithTail_of_canonical
    (hCan : BrunBonferroniNatSubSqrtCanonicalKernel) :
    Gdbh.PathCPairedBrunSubSqrtProof.PairedBonferroniInequalitySubSqrtAlignedWithTail :=
  Gdbh.PathCPairedBonferroniNaturalSubSqrt.pairedBonferroniInequalitySubSqrtAlignedWithTail_of_kernel
    (pairedBonferroniNaturalSubSqrtCombinatorialKernel_holds_of_canonical hCan)

/-! ## Section 7 — Boundary observations about the SubSqrt slice

We record honest, unconditional facts about the SubSqrt slice at the
canonical witness.  These do not depend on the open residual and are
useful as sanity checks. -/

/-- **Sanity**:  for `n ≥ 16`, `Nat.sqrt n ≥ 4`, so the SubSqrt range
`z ∈ [3, √n)` is non-empty (`z = 3` is admissible). -/
theorem sqrt_ge_four_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    4 ≤ Nat.sqrt n := by
  have hmono : Nat.sqrt 16 ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
  -- `Nat.sqrt 16 = 4`.
  have h16 : Nat.sqrt 16 = 4 := by
    have h_le : Nat.sqrt 16 ≤ 4 := by
      have hlt : Nat.sqrt 16 < 5 := by
        have : Nat.sqrt 16 < 5 ↔ 16 < 5 * 5 := Nat.sqrt_lt
        exact this.mpr (by norm_num)
      omega
    have h_ge : 4 ≤ Nat.sqrt 16 := by
      have h44 : 4 * 4 ≤ 16 := by norm_num
      exact Nat.le_sqrt.mpr h44
    omega
  omega

/-- **Sanity**:  for `n ≥ 16` and `z ∈ [3, √n)`,
`pairedBrunFactor z ∈ (0, 1]`. -/
theorem pairedBrunFactor_in_unit_of_subSqrt
    {n z : ℕ} (_hn : 16 ≤ n) (_hz_ge_3 : 3 ≤ z) (_hz_lt_sqrt : z < Nat.sqrt n) :
    0 < pairedBrunFactor z ∧ pairedBrunFactor z ≤ 1 :=
  ⟨pairedBrunFactor_pos z, pairedBrunFactor_le_one z⟩

/-- **Sanity**:  for `n ≥ 16` and `z ∈ [3, √n)`, the upper bound
`Nat.primeCounting z ≤ z + 1` holds. -/
theorem primeCounting_le_succ_of_subSqrt
    {n z : ℕ} (_hn : 16 ≤ n) (_hz_ge_3 : 3 ≤ z) (_hz_lt_sqrt : z < Nat.sqrt n) :
    Nat.primeCounting z ≤ z + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  exact Nat.count_le (p := Nat.Prime)

/-! ## Section 8 — Summary

This file performs the **mechanical decomposition** portion of the
closure of `PairedBonferroniNaturalSubSqrtCombinatorialKernel`,
exposing the genuine analytic content as a single z-parameterized
named open sub-Prop `BrunBonferroniNatSubSqrtCanonicalKernel`.

* **Closed (axiom-clean, no `sorry`)**:
  - Canonical witness definition (`canonicalK`) and depth-unfolding
    (`canonicalK_exp`).
  - Vacuous-regime closure for `n ∈ [10, 15]`
    (`subSqrt_kernel_vacuous_of_small_n`).
  - Non-negativity of RHS pieces (`main_term_nonneg`,
    `canonical_tail_nonneg`).
  - Trivial cardinal bound (`goldbachSiftedPair_le_real`).
  - Reduction:  kernel ⇐ z-parameterized canonical residual
    (`pairedBonferroniNaturalSubSqrtCombinatorialKernel_holds_of_canonical`).
  - Forward bridges into the natural assembly Prop and aligned
    residual.
  - Boundary sanity:  `Nat.sqrt n ≥ 4` for `n ≥ 16`; π and pairedBrun
    factor bounds on the SubSqrt slice.

* **Open (single concentrated residual)**:
  - `BrunBonferroniNatSubSqrtCanonicalKernel`:  the classical paired
    Brun-Bonferroni inequality at SubSqrt threshold and canonical
    truncation depth `k(n) = 2n`.

The named open sub-Prop is **strictly equivalent** to the P19-T12
SubSqrt kernel residual in mathematical content, but is structured
identically to the AtSqrt residual (P19-T14), so a single downstream
proof of the genuine Halberstam-Richert sieve estimate would close
both.

## Constraint compliance

* No `sorry`, no `axiom`, no `admit` appear in any theorem in this
  file.
* Only `Classical.choice`, `Quot.sound`, and `propext` are
  transitively used.
* No existential witness exploitation:  the canonical witness
  `k(n) := 2n` is fixed.

## Honesty audit

The genuine analytic content is concentrated in a single named open
Prop with explicit canonical witnesses and explicit z-parameter range.
The Prop is *equivalent in strength* to the P19-T12 residual; this
file does not discharge it. -/

/-- **P19-T16 summary, in proof form.** -/
theorem pathC_p19_t16_summary : True := trivial

end PathCBrunBonferroniSubSqrtCanonical
end Gdbh
