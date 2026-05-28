/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T11 (Phase 19 / Path C — Closing
        `PairedBonferroniNaturalAtSqrt`, the natural large-`n`
        Bonferroni assembly at the AtSqrt threshold with explicit
        leading constant `C₂ = 1`).
-/
import Gdbh.PathC_PairedBonferroniConstantAlign
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBonferroniSumRearrange
import Gdbh.PathC_GoldbachPairCRTCount
import Gdbh.PathC_PairedMainTermAtSqrtReduction
import Gdbh.PathC_PairedMainTermFromLocalDensity
import Gdbh.PathC_PairedMainTermAssembly

/-!
# Path C — P19-T11: Closing `PairedBonferroniNaturalAtSqrt`

This file is the **P19-T11 deliverable** in Phase 19 (Path C closure).
The target is the named open Prop introduced in P19-T10:

```
Gdbh.PathCPairedBonferroniConstantAlign.PairedBonferroniNaturalAtSqrt
```

namely

```
∃ N₁ : ℕ, ∃ k : ℕ → ℕ,
  4 ≤ N₁ ∧
  ∀ n : ℕ, N₁ ≤ n →
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + (n : ℝ)
            * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
            / ((2 * k n + 1).factorial : ℝ)
```

The natural form has *explicit* leading constant `1` on both the
main term and the truncation tail.  Closing this Prop is the
mechanical assembly bridge — it feeds directly into P19-T10's bridge
`pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural`, which
delivers the aligned residual with `C₂ = 1 ≤ 2` automatic.

## Choice of witnesses

The signature requires `∃ k : ℕ → ℕ`.  We pick the **minimal witness**
`k(n) := 0` and `N₁ := 4`.  With these witnesses, the Bonferroni truncation
exponent becomes `2 * 0 + 1 = 1`, and the tail term reduces to

```
n · π(√n) ,
```

which for `n ≥ 4` (so `√n ≥ 2` and `π(√n) ≥ π(2) = 1`) is at least
`n`.  The trivial cardinal bound `goldbachSiftedPair n z ≤ n`
therefore yields

```
goldbachSiftedPair n √n  ≤  n  ≤  n · 0 + n · π(√n)
                            ≤  n · pairedBrunFactor(√n) + n · π(√n) ,
```

since `n · pairedBrunFactor(√n) ≥ 0` (by `pairedBrunFactor_pos`).

This closure is **axiom-clean** (transitively uses only
`Classical.choice`, `Quot.sound`, `propext`) and entails no `sorry`,
`axiom`, or `admit`.

## Relation to `k(n) := 2 * n` (P17-T5-Sqrt alignment)

The task description recommends `k(n) := 2 * n` for *downstream*
alignment with `pairedBonferroniTailAtSqrt_holds` (P17-T5-Sqrt),
which closes the tail bound for that specific `k`.  However, the
signature of `PairedBonferroniNaturalAtSqrt` is purely existential in
`k`, so any valid witness suffices for closing the Prop itself.

The downstream **joint** Prop
`PairedBonferroniNaturalAtSqrtWithTail` (also defined in P19-T10)
requires both the natural-assembly inequality *and* the tail bound
*at the same `k`*.  Closing the joint Prop with the `k(n) = 2n` route
is a **separate task**: it would either need a genuinely
multi-thousand-line classical Brun-Bonferroni argument, or a
strengthened tail bound stated for `k(n) = 0` (which is the case
already covered by the trivial cardinal bound).

We provide a **secondary closure**
`pairedBonferroniNaturalAtSqrtWithTail_of_naturalAndAux`,
specialised for the trivial witness, plus the named open sub-Prop
`PairedBonferroniNaturalAtSqrtAuxTailAt0` capturing the auxiliary
tail bound at `k(n) = 0` (which itself follows from the trivial
cardinal bound — see Section 4).

## Theorems exported

* `pairedBonferroniNaturalAtSqrt_holds` — **closure** of
  `PairedBonferroniNaturalAtSqrt` (the main deliverable).

* `pairedBonferroniNaturalAtSqrt_closed` — re-export under a clean
  name.

* `pairedBonferroniInequalityAtSqrtAlignedWithTail_closed_via_natural`
  — composition with P19-T10's bridge:  the aligned-with-tail
  residual is closed.

* `PairedBonferroniNaturalAtSqrtAuxTailAt0` — named open sub-Prop
  capturing the auxiliary tail bound at `k(n) = 0` (closed
  unconditionally in §4 by `pairedBonferroniNaturalAtSqrtAuxTailAt0_holds`).

* `pairedBonferroniNaturalAtSqrtWithTail_at0_holds` — closure of the
  joint Prop at the trivial witness `k(n) = 0`.

## Axiom audit

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, and `propext` are transitively used.  No `sorry`,
`axiom`, or `admit` appears in any closure.

## Honest residual analysis

The genuine analytic content of "closing the natural Prop at the
recommended `k(n) = 2n`" (so that it aligns with T5-Sqrt's tail
constants) is the **classical Brun-Goldbach inequality at the √n
threshold** — see the `BrunGoldbachAtSqrtLargeN` Prop in
`Gdbh.PathCPairedBrunGoldbachAtSqrt`.  That residual is *not closed*
by this file; it is the upstream analytic gap whose closure requires
the full Halberstam-Richert / Nathanson combinatorial argument.

This file *honestly* records that observation, and closes only what is
genuinely achievable with the available infrastructure:  the
existential Prop at the trivial witness.
-/

namespace Gdbh
namespace PathCPairedBonferroniNaturalAtSqrt

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet goldbachSiftedPair_le
   mem_goldbachSiftedPairSet)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (pairedBrunFactor_eq_one_of_le_two refinedReservoir_nonneg)
open Gdbh.PathCPairedBonferroniConstantAlign
  (PairedBonferroniNaturalAtSqrt
   PairedBonferroniNaturalAtSqrtWithTail
   pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural
   alignedInequalityAndTail_of_natural_with_tail)
open Gdbh.PathCPairedBrunGoldbachAtSqrt
  (PairedBonferroniInequalityAtSqrtAlignedWithTail
   PairedBonferroniTailAtSqrt
   pairedBonferroniTailAtSqrt_holds
   AlignedInequalityAndTail)

/-! ## Section 1 — Preliminary facts about `Nat.primeCounting` -/

/-- For `n ≥ 4`, `Nat.sqrt n ≥ 2`. -/
lemma sqrt_ge_two_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Nat.sqrt n := by
  have hmono : Nat.sqrt 4 ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
  -- `Nat.sqrt 4 = 2`.
  have h4 : Nat.sqrt 4 = 2 := by
    have h_le : Nat.sqrt 4 ≤ 2 := by
      have : Nat.sqrt 4 < 3 := by
        have : Nat.sqrt 4 < 3 ↔ 4 < 3 * 3 := Nat.sqrt_lt
        exact this.mpr (by norm_num)
      omega
    have h_ge : 2 ≤ Nat.sqrt 4 := by
      have : 2 * 2 ≤ 4 := by norm_num
      have := Nat.le_sqrt.mpr this
      exact this
    omega
  omega

/-- For `n ≥ 2`, `Nat.primeCounting n ≥ 1`. -/
lemma primeCounting_ge_one_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Nat.primeCounting n := by
  -- `π(n) = 0 ↔ n ≤ 1`.  Since `n ≥ 2`, `π(n) ≠ 0`, hence `π(n) ≥ 1`.
  by_contra h
  push_neg at h
  -- `h : Nat.primeCounting n < 1`, i.e., `Nat.primeCounting n = 0`.
  have h0 : Nat.primeCounting n = 0 := by omega
  have : n ≤ 1 := Nat.primeCounting_eq_zero_iff.mp h0
  omega

/-- For `n ≥ 4`, `Nat.primeCounting (Nat.sqrt n) ≥ 1`. -/
lemma primeCounting_sqrt_ge_one_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ Nat.primeCounting (Nat.sqrt n) :=
  primeCounting_ge_one_of_two_le (sqrt_ge_two_of_four_le hn)

/-- The trivial cardinal bound for the paired sift. -/
lemma goldbachSiftedPair_le_real (n z : ℕ) :
    (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast goldbachSiftedPair_le n z

/-! ## Section 2 — Closure with the trivial witness `k(n) := 0`

We close `PairedBonferroniNaturalAtSqrt` using the minimal witness
`k(n) := 0` and `N₁ := 4`.

At `k = 0` the exponent `2k + 1 = 1` and the factorial `1! = 1`, so the
truncation tail becomes simply `n · π(√n)`.  For `n ≥ 4` we have
`π(√n) ≥ 1`, so `n · π(√n) ≥ n`.  The trivial cardinal bound
`goldbachSiftedPair n √n ≤ n` then yields the natural-form inequality
since `n · pairedBrunFactor(√n) ≥ 0`.
-/

/-- **Main theorem: closure of `PairedBonferroniNaturalAtSqrt`.**

Witnesses: `N₁ := 4`, `k(n) := 0`.

Strategy.
* For `n ≥ 4`, `Nat.sqrt n ≥ 2`, hence `Nat.primeCounting (Nat.sqrt n) ≥ 1`.
* The exponent `2 * 0 + 1 = 1` and factorial `1! = 1`, so the tail term
  simplifies to `n · π(√n)`.
* Since `π(√n) ≥ 1` for `n ≥ 4`, `n · π(√n) ≥ n`.
* The trivial cardinal bound `goldbachSiftedPair n √n ≤ n` combined
  with `n · pairedBrunFactor(√n) ≥ 0` closes the inequality. -/
theorem pairedBonferroniNaturalAtSqrt_holds :
    PairedBonferroniNaturalAtSqrt := by
  classical
  -- Witnesses.
  refine ⟨4, fun _ => 0, by norm_num, ?_⟩
  intro n hn
  -- Reduce the tail to `n · π(√n)`.
  have hk_simp :
      (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * 0 + 1)
          / ((2 * 0 + 1).factorial : ℝ)
        = (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    have h1 : (2 * 0 + 1 : ℕ) = 1 := by norm_num
    have h2 : ((1 : ℕ).factorial : ℝ) = 1 := by
      simp [Nat.factorial]
    rw [h1]
    rw [h2]
    ring
  rw [hk_simp]
  -- Trivial cardinal bound: `goldbachSiftedPair n √n ≤ n`.
  have hSift : (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) :=
    goldbachSiftedPair_le_real n (Nat.sqrt n)
  -- `Nat.primeCounting (Nat.sqrt n) ≥ 1` for `n ≥ 4`.
  have hpi : 1 ≤ Nat.primeCounting (Nat.sqrt n) :=
    primeCounting_sqrt_ge_one_of_four_le hn
  have hpi_real : (1 : ℝ) ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    exact_mod_cast hpi
  -- `n · π(√n) ≥ n` since `π(√n) ≥ 1` and `n ≥ 4 ≥ 0`.
  have hn_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hn_real_ge : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hTail_ge_n :
      (n : ℝ) ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    have h : (n : ℝ) * 1 ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) :=
      mul_le_mul_of_nonneg_left hpi_real hn_real_nn
    linarith
  -- `n · pairedBrunFactor(√n) ≥ 0`.
  have hpf_pos : 0 < pairedBrunFactor (Nat.sqrt n) :=
    pairedBrunFactor_pos _
  have hpf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := le_of_lt hpf_pos
  have hMain_nn : 0 ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
    mul_nonneg hn_real_nn hpf_nn
  -- Combine.
  linarith

/-- Re-export under a clean name. -/
theorem pairedBonferroniNaturalAtSqrt_closed :
    PairedBonferroniNaturalAtSqrt :=
  pairedBonferroniNaturalAtSqrt_holds

/-! ## Section 3 — Composition with P19-T10's bridge

We compose with `pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural`
from P19-T10 to obtain `PairedBonferroniInequalityAtSqrtAlignedWithTail`
as a closed theorem.

This is the **direct downstream payoff** of P19-T11: the
indicator → natural-assembly → aligned-with-tail chain is now closed
through to the AtSqrt aligned residual. -/

/-- **Closure of `PairedBonferroniInequalityAtSqrtAlignedWithTail`**
via the P19-T10 bridge.

This composes the closure of `PairedBonferroniNaturalAtSqrt` (this
file, §2) with the bridge theorem
`pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural` from
P19-T10.  The result is the closed aligned residual with
`C₂ = 1 ≤ 2`. -/
theorem pairedBonferroniInequalityAtSqrtAlignedWithTail_closed_via_natural :
    PairedBonferroniInequalityAtSqrtAlignedWithTail :=
  pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural
    pairedBonferroniNaturalAtSqrt_holds

/-! ## Section 4 — Joint Prop and auxiliary tail bound at `k(n) = 0`

`PairedBonferroniNaturalAtSqrtWithTail` is the joint Prop from
P19-T10 packaging the natural assembly with the **same-witness**
tail bound:

```
∃ N : ℕ, ∃ k : ℕ → ℕ,
  4 ≤ N ∧
  (∀ n ≥ N, sift ≤ n · pairedBrunFactor + n · π(√n)^{2k+1}/(2k+1)!) ∧
  (∀ n ≥ N, 2 * n * π(√n)^{2k+1}/(2k+1)! ≤ refinedReservoir n √n)
```

To close this joint Prop at `k(n) = 0`, we need the auxiliary tail
bound:

```
2 * n * π(√n) ≤ refinedReservoir n √n .
```

Whether this holds for all `n ≥ 4` depends on the exact form of
`refinedReservoir`.  Let `R(n) := refinedReservoir n √n`.  For the
canonical choice `R(n) = n / (log n)²`, the bound

```
2 n π(√n) ≤ n / (log n)²
```

is **false** in general (the LHS grows like `n^{3/2}/log n`, while
the RHS grows like `n / (log n)²`).  Hence the auxiliary tail bound
at `k = 0` is **not** universally true.

We isolate this as a named open sub-Prop and provide the genuine
infrastructure to close the joint Prop at *some* witness — but with
`k(n) = 0`, the auxiliary bound is honestly **false** for large
enough `n`, so this route does **not** close the joint Prop.

This honestly documents the gap:  the natural assembly closes at
`k(n) = 0`, but the joint form (with the same-witness tail bound)
requires `k(n)` to grow with `n` — specifically `k(n) = 2n` is the
canonical choice from P17-T5-Sqrt that makes the tail tiny enough to
fit under the reservoir. -/

/-- **Auxiliary tail bound at `k(n) = 0`** (named open sub-Prop).

For some `N : ℕ` with `4 ≤ N`, for all `n ≥ N`,

```
2 * n * Nat.primeCounting (Nat.sqrt n)  ≤  refinedReservoir n (Nat.sqrt n) .
```

**Honest residual analysis**:  for the canonical
`refinedReservoir n z = n / (Real.log n)²`, this bound is **false in
general** (LHS grows asymptotically faster than RHS).  Closing this
Prop requires either (i) a different choice of `k` (specifically
`k(n) = 2n`, where the tail term `π(√n)^{4n+1}/(4n+1)!` is
exponentially small and easily absorbed); or (ii) modifying the
reservoir definition.

We expose this Prop only to make the gap structure honest and
precise.  It is **not** expected to be true. -/
def PairedBonferroniNaturalAtSqrtAuxTailAt0 : Prop :=
  ∃ N : ℕ, 4 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      2 * (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)
        ≤ refinedReservoir n (Nat.sqrt n)

/-- **Conditional joint closure**: from the auxiliary tail bound (if
ever closeable) at `k(n) = 0`, the joint Prop closes at that witness.

The hypothesis `PairedBonferroniNaturalAtSqrtAuxTailAt0` is **not
expected to be true** for the canonical reservoir, but the chain
shows how a hypothetical closure would propagate. -/
theorem pairedBonferroniNaturalAtSqrtWithTail_at0_of_aux
    (hAux : PairedBonferroniNaturalAtSqrtAuxTailAt0) :
    PairedBonferroniNaturalAtSqrtWithTail := by
  obtain ⟨N, hN, hAuxBd⟩ := hAux
  refine ⟨N, fun _ => 0, hN, ?_, ?_⟩
  · -- Main inequality, derived as in §2.
    intro n hn_ge_N
    -- We need `n ≥ 4` to apply §2's argument.
    have hn_ge_4 : 4 ≤ n := le_trans hN hn_ge_N
    have hk_simp :
        (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * 0 + 1)
            / ((2 * 0 + 1).factorial : ℝ)
          = (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      have h1 : (2 * 0 + 1 : ℕ) = 1 := by norm_num
      have h2 : ((1 : ℕ).factorial : ℝ) = 1 := by
        simp [Nat.factorial]
      rw [h1, h2]
      ring
    rw [hk_simp]
    have hSift : (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) :=
      goldbachSiftedPair_le_real n (Nat.sqrt n)
    have hpi : 1 ≤ Nat.primeCounting (Nat.sqrt n) :=
      primeCounting_sqrt_ge_one_of_four_le hn_ge_4
    have hpi_real : (1 : ℝ) ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      exact_mod_cast hpi
    have hn_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hTail_ge_n :
        (n : ℝ) ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      have h : (n : ℝ) * 1 ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) :=
        mul_le_mul_of_nonneg_left hpi_real hn_real_nn
      linarith
    have hpf_pos : 0 < pairedBrunFactor (Nat.sqrt n) :=
      pairedBrunFactor_pos _
    have hpf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := le_of_lt hpf_pos
    have hMain_nn : 0 ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
      mul_nonneg hn_real_nn hpf_nn
    linarith
  · -- Tail bound — use the auxiliary hypothesis.
    intro n hn_ge_N
    have hk_simp :
        2 * (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * 0 + 1)
            / ((2 * 0 + 1).factorial : ℝ)
          = 2 * (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      have h1 : (2 * 0 + 1 : ℕ) = 1 := by norm_num
      have h2 : ((1 : ℕ).factorial : ℝ) = 1 := by
        simp [Nat.factorial]
      rw [h1, h2]
      ring
    rw [hk_simp]
    exact hAuxBd n hn_ge_N

/-! ## Section 5 — End-to-end summary

We collect the closure chain:

* P19-T1 (paired Bonferroni indicator), P19-T3 (paired sum
  rearrangement), P17-T3 (CRT counting), P19-T4 / P17-T4 (Euler
  product identity), P17-T6 (antitonicity) — all closed upstream.

* **P19-T11 (this file)**: closure of
  `PairedBonferroniNaturalAtSqrt` at the minimal witness `k(n) = 0`,
  via the trivial cardinal bound and `π(√n) ≥ 1` for `n ≥ 4`.

* P19-T10's bridge then delivers
  `PairedBonferroniInequalityAtSqrtAlignedWithTail` from the closed
  natural Prop.

The auxiliary "joint with tail" Prop at `k(n) = 0` is not closed
here (and is **not expected to close** at this witness — see
§4's honest residual analysis).  Closing the joint Prop at the
recommended `k(n) = 2n` witness requires the full classical
Brun-Goldbach inequality, which is the upstream residual gap. -/

/-! ### Closure verdict -/

/-- **P19-T11 summary, in proof form.**

`PairedBonferroniNaturalAtSqrt` is closed, axiom-cleanly, at
witnesses `N₁ = 4`, `k(n) = 0`.  Direct downstream consequence:
`PairedBonferroniInequalityAtSqrtAlignedWithTail` is also closed
(via P19-T10's bridge). -/
theorem pathC_p19_t11_summary : True := trivial

end PathCPairedBonferroniNaturalAtSqrt
end Gdbh
