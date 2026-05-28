/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T18 (Phase 19 / Path C — Conditional closure of
        `PairedMainTermResidualLowRegion` from the P19-T12 SubSqrt
        combinatorial kernel together with the P19-T16 canonical
        Stirling tail residual.)
-/
import Gdbh.PathC_BrunBonferroniNatSubSqrtClosure
import Gdbh.PathC_BrunBonferroniSubSqrtCanonical
import Gdbh.PathC_PairedBonferroniNaturalSubSqrt
import Gdbh.PathC_PairedBrunLowRegion
import Gdbh.PathC_PairedBrunLargeZ

/-!
# Path C — P19-T18: Conditional closure of `PairedMainTermResidualLowRegion`

This file is the **P19-T18 deliverable** in Phase 19 (Path C closure).
It provides a mechanical bridge from the P19-T12 SubSqrt combinatorial
kernel `PairedBonferroniNaturalSubSqrtCombinatorialKernel` (with the
canonical truncation depth `k(n) = 2 * n` pre-substituted) together
with the P19-T16 Stirling tail residual `StirlingTailSubSqrtAtCanonicalK`
to the named open Prop
`Gdbh.PathCPairedBrunLargeZ.PairedMainTermResidualLowRegion`.

## Mathematical structure

The kernel provides, for every `n ≥ 10` and `z ∈ [3, √n)`,

```
goldbachSiftedPair n z
  ≤ n · pairedBrunFactor z
    + n · π(z)^(4n+1) / (4n+1)!
```

while the canonical Stirling tail residual provides, for every
`n ≥ 16` and `z ∈ [3, √n)`,

```
n · π(z)^(4n+1) / (4n+1)!  ≤  n / (2 (log n)²) .
```

Adding the two and using `n / (2 (log n)²) ≤ n / (log n)² = refinedReservoir n z`
yields the `PairedBrunBonferroniSubSqrt` Prop with the canonical
constant `C = 1`.  The forward bridge
`pairedMainTermResidualLowRegion_of_subSqrt` from P18-T3 then closes
`PairedMainTermResidualLowRegion`.

## Honesty disclosure

The deliverable spec asks for the SINGLE-input bridge

```
(hKernel : PairedBonferroniNaturalSubSqrtCombinatorialKernel)
  → PairedMainTermResidualLowRegion .
```

Such a kernel-only closure is **not** available axiom-cleanly through
the existing infrastructure: the kernel hardcodes the canonical
truncation depth `k(n) = 2 * n`, while the closed Stirling-tail
producer `pairedBrunStirlingTruncationErrorSqrt_holds` (P17-T5-Sqrt)
states its conclusion under an `∃ k`-witness whose value, post
`obtain`, is opaque (`Classical.choose` is non-reducible).  The two
truncation depths cannot be aligned via existing public infrastructure
without re-deriving the Stirling tail at the explicit canonical
witness, which would require re-exposing the private combinatorial
lemmas of `PathC_PairedBrunStirlingSqrt.lean` — outside the scope of
this task.

We therefore expose the missing alignment as the **single concentrated
named open Prop** `StirlingTailSubSqrtAtCanonicalK` from P19-T16,
and provide the closed conditional bridge

```
(hKernel : PairedBonferroniNaturalSubSqrtCombinatorialKernel)
(hStirling : StirlingTailSubSqrtAtCanonicalK)
  → PairedMainTermResidualLowRegion .
```

This is honest:  the named open residual is morally closed by P17-T5-Sqrt
at the explicit canonical witness, but its formal re-derivation is a
mechanical follow-up.  The bridge itself is **axiom-clean** and
contains no `sorry`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom budget: `[Classical.choice, Quot.sound, propext]` only.

## Phase atoms consumed

* P19-T12 `pairedBonferroniNaturalSubSqrt_of_kernel` —
  kernel ⇒ natural assembly (used for downstream cross-check).
* P19-T16 `StirlingTailSubSqrtAtCanonicalK` — the Stirling tail at
  the canonical witness `k(n) = 2 * n` (taken as a hypothesis).
* P18-T3 `pairedMainTermResidualLowRegion_of_subSqrt` —
  `PairedBrunBonferroniSubSqrt` ⇒ `PairedMainTermResidualLowRegion`.

## References

* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  Theorem 3.11 (paired Brun-Bonferroni at deep truncation).
-/

namespace Gdbh
namespace PathCResidualLowRegionClosed

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (refinedReservoir_nonneg)
open Gdbh.PathCPairedBonferroniNaturalSubSqrt
  (PairedBonferroniNaturalSubSqrtCombinatorialKernel)
open Gdbh.PathCBrunBonferroniSubSqrtCanonical
  (canonicalK canonicalK_def canonicalK_exp)
open Gdbh.PathCBrunBonferroniNatSubSqrtClosure
  (StirlingTailSubSqrtAtCanonicalK)
open Gdbh.PathCPairedBrunLargeZ
  (PairedMainTermResidualLowRegion)
open Gdbh.PathCPairedBrunLowRegion
  (PairedBrunBonferroniSubSqrt pairedMainTermResidualLowRegion_of_subSqrt)

/-! ## Section 1 — Auxiliary facts about `Nat.sqrt` in the low regime

The constraint `3 ≤ z < Nat.sqrt n` is unsatisfiable for `n ≤ 15`:
indeed `Nat.sqrt 15 = 3`, so `z < 3` and `3 ≤ z` together are
impossible.  We record this fact for the case-split below. -/

/-- For `n ≤ 15`, `Nat.sqrt n ≤ 3`. -/
private lemma sqrt_le_three_of_le_fifteen {n : ℕ} (hn : n ≤ 15) :
    Nat.sqrt n ≤ 3 := by
  -- Use `Nat.sqrt_lt` characterisation: `Nat.sqrt n < 4 ↔ n < 4 * 4`.
  have h_lt : Nat.sqrt n < 4 := by
    have : Nat.sqrt n < 4 ↔ n < 4 * 4 := Nat.sqrt_lt
    exact this.mpr (by omega)
  omega

/-- For `n ≤ 15`, `3 ≤ z < Nat.sqrt n` is impossible. -/
private lemma subSqrt_range_empty_low {n z : ℕ}
    (hn_hi : n ≤ 15) (hz_ge_3 : 3 ≤ z) (hz_lt_sqrt : z < Nat.sqrt n) :
    False := by
  have hsqrt : Nat.sqrt n ≤ 3 := sqrt_le_three_of_le_fifteen hn_hi
  omega

/-! ## Section 2 — Reservoir dominance over the Stirling tail bound

For `n ≥ 4`, `log n > 0`, hence `n / (2 (log n)²) ≤ n / (log n)² =
refinedReservoir n z`.  This is the elementary inequality used to
convert the Stirling tail bound (RHS `n/(2 (log n)²)`) into a
reservoir bound (RHS `refinedReservoir n z`). -/

/-- For `n ≥ 4` and any `z`, the Stirling RHS `n / (2 (log n)²)` is
bounded above by `refinedReservoir n z = n / (log n)²`. -/
private lemma stirling_rhs_le_reservoir {n : ℕ} (hn : 4 ≤ n) (z : ℕ) :
    (n : ℝ) / (2 * (Real.log (n : ℝ))^2)
      ≤ refinedReservoir n z := by
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn_real_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hn_real_ge_four : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    linarith
  have h_log_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have h_2logsq_pos : 0 < 2 * (Real.log (n : ℝ))^2 := by linarith
  -- `refinedReservoir n z = n / (log n)²`.
  rw [refinedReservoir_def]
  -- Goal: `n / (2 (log n)²) ≤ n / (log n)²`.
  -- Equivalently, `1 / (2 (log n)²) ≤ 1 / (log n)²` (after factoring out n ≥ 0).
  rw [div_le_div_iff₀ h_2logsq_pos h_log_sq_pos]
  -- Goal: `n * (log n)² ≤ n * (2 * (log n)²)`.
  have h_2sq_ge_sq : (Real.log (n : ℝ))^2 ≤ 2 * (Real.log (n : ℝ))^2 := by
    linarith [h_log_sq_pos]
  exact mul_le_mul_of_nonneg_left h_2sq_ge_sq hn_real_nn

/-! ## Section 3 — Main conditional closure

We prove the conditional closure of `PairedMainTermResidualLowRegion`
from the kernel and the Stirling tail at the canonical witness.

The proof builds `PairedBrunBonferroniSubSqrt` (the P18-T3 residual)
directly using the kernel + Stirling tail at canonical, then composes
with `pairedMainTermResidualLowRegion_of_subSqrt`. -/

/-- **Intermediate**: closure of the SubSqrt Brun-Bonferroni residual
from the kernel and Stirling tail at the canonical witness.

We use the canonical absorption constant `C := 1`.

* For `n ≤ 15`, the SubSqrt constraint `3 ≤ z < Nat.sqrt n` is
  vacuous (Section 1).
* For `n ≥ 16`, the kernel produces the inequality at the canonical
  truncation depth, and the Stirling tail bound at the canonical
  witness absorbs the tail into the reservoir (Section 2). -/
theorem pairedBrunBonferroniSubSqrt_of_kernel_and_stirling
    (hKernel : PairedBonferroniNaturalSubSqrtCombinatorialKernel)
    (hStirling : StirlingTailSubSqrtAtCanonicalK) :
    PairedBrunBonferroniSubSqrt := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro n z hn hz_ge_3 hz_lt_sqrt
  -- Case split on whether `n ≥ 16` (Stirling regime) or `n ≤ 15` (vacuous).
  by_cases hn_ge_16 : 16 ≤ n
  · -- Non-vacuous regime: combine kernel + Stirling tail.
    -- Hypothesis `10 ≤ n` for the kernel.
    have hn_ge_10 : 10 ≤ n := by omega
    have hn_ge_4 : 4 ≤ n := by omega
    -- Kernel inequality (with the literal exponent `2 * (2 * n) + 1`).
    have hKer := hKernel n z hn_ge_10 hz_ge_3 hz_lt_sqrt
    -- Stirling tail bound at canonical (with the exponent `2 * canonicalK n + 1`).
    have hSt := hStirling n z hn_ge_16 hz_ge_3 hz_lt_sqrt
    -- Reconcile exponents: `2 * (2 * n) + 1 = 2 * canonicalK n + 1`.
    have hExp : 2 * (2 * n) + 1 = 2 * canonicalK n + 1 := by
      unfold canonicalK
      ring
    -- Rewrite kernel's tail to the canonical-k form.
    rw [hExp] at hKer
    -- Stirling RHS `n/(2 (log n)²)` ≤ `refinedReservoir n z`.
    have hRes : (n : ℝ) / (2 * (Real.log (n : ℝ))^2) ≤ refinedReservoir n z :=
      stirling_rhs_le_reservoir hn_ge_4 z
    -- Combine: tail ≤ n/(2 (log n)²) ≤ refinedReservoir n z.
    have hTailRes :
        (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * canonicalK n + 1)
            / ((2 * canonicalK n + 1).factorial : ℝ)
          ≤ refinedReservoir n z :=
      le_trans hSt hRes
    -- Goal: `goldbachSiftedPair n z ≤ 1 * n * pairedBrunFactor z + refinedReservoir n z`.
    -- From kernel: `goldbachSiftedPair n z ≤ n * pairedBrunFactor z + tail`.
    -- Combining: ≤ n * pairedBrunFactor z + refinedReservoir n z.
    have hGoal_eq :
        1 * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z
          = (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
      ring
    rw [hGoal_eq]
    linarith
  · -- Vacuous regime: `n ≤ 15`, so `3 ≤ z < Nat.sqrt n` is impossible.
    have hn_le_15 : n ≤ 15 := by omega
    exact absurd hz_lt_sqrt (fun h =>
      subSqrt_range_empty_low hn_le_15 hz_ge_3 h)

/-! ## Section 4 — The headline conditional closure -/

/-- **P19-T18 conditional closure** (TWO-input bridge).

Given:
* `hKernel`:  the P19-T12 SubSqrt combinatorial kernel residual.
* `hStirling`:  the P19-T16 Stirling tail at the canonical witness
  `k(n) = 2 * n` (morally closed by P17-T5-Sqrt; formally exposed
  pending re-derivation at the explicit canonical witness).

the file's headline target `PairedMainTermResidualLowRegion` holds
**axiom-cleanly**.

Strategy:
1. Compose the kernel with the Stirling tail at canonical to produce
   `PairedBrunBonferroniSubSqrt` (the P18-T3 residual) with constant
   `C = 1`.
2. Apply the P18-T3 forward bridge
   `pairedMainTermResidualLowRegion_of_subSqrt`.

**Honesty disclosure**:  the deliverable spec asks for a SINGLE-input
bridge `(hKernel) → LowRegion`.  Such a closure is unavailable
axiom-cleanly through the existing public infrastructure because
`pairedBrunStirlingTruncationErrorSqrt_holds`'s witness becomes opaque
after `obtain` (`Classical.choose` is non-reducible), and the kernel
hardcodes the truncation depth `k = 2n` which cannot be aligned with
the opaque witness.  The single concentrated residual
`StirlingTailSubSqrtAtCanonicalK` exposes precisely the missing
witness alignment. -/
theorem pairedMainTermResidualLowRegion_of_subSqrtKernel
    (hKernel : PairedBonferroniNaturalSubSqrtCombinatorialKernel)
    (hStirling : StirlingTailSubSqrtAtCanonicalK) :
    PairedMainTermResidualLowRegion :=
  pairedMainTermResidualLowRegion_of_subSqrt
    (pairedBrunBonferroniSubSqrt_of_kernel_and_stirling hKernel hStirling)

/-! ## Section 5 — P19-T18 summary -/

/-- **P19-T18 summary, in proof form.**

**Mission**: deliver a conditional axiom-clean bridge

```
PairedBonferroniNaturalSubSqrtCombinatorialKernel
  → PairedMainTermResidualLowRegion .
```

**Outcome**: a TWO-input axiom-clean bridge

```
(hKernel : PairedBonferroniNaturalSubSqrtCombinatorialKernel)
(hStirling : StirlingTailSubSqrtAtCanonicalK)
  → PairedMainTermResidualLowRegion
```

where the second hypothesis `StirlingTailSubSqrtAtCanonicalK` exposes
the unique signature-mismatch residual:  the Stirling tail at the
explicit canonical witness `k(n) = 2 * n`.  This residual is morally
closed by P17-T5-Sqrt (`pairedBrunStirlingTruncationErrorSqrt_holds`),
whose proof uses exactly `k(n) := 2 * n`; however, the public
existence-form Prop only exposes the witness through `obtain`, after
which the function is abstract.

**Residual**:  the single named open Prop
`Gdbh.PathCBrunBonferroniNatSubSqrtClosure.StirlingTailSubSqrtAtCanonicalK`,
already exposed in P19-T16.

**Closed pieces consumed**:
* P19-T12's kernel residual (taken as hypothesis).
* P19-T16's canonical witness `k = 2 * n` and depth-renormalisation
  lemma `canonicalK_exp`.
* P18-T3's forward bridge `pairedMainTermResidualLowRegion_of_subSqrt`. -/
theorem pathC_p19_t18_summary : True := trivial

end PathCResidualLowRegionClosed
end Gdbh
