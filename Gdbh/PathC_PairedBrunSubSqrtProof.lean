/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P18-T5 (Phase 18 / Path C — Mechanical assembly bridge for
        `PairedBrunBonferroniSubSqrt`, the paired Brun-Bonferroni
        bound at sub-`√n` sieve thresholds `z ∈ [3, √n)`).
-/
import Gdbh.PathC_PairedBrunLowRegion
import Gdbh.PathC_PairedBrunBonferroni
import Gdbh.PathC_GoldbachPairCRTCount
import Gdbh.PathC_PairedMainTermFromLocalDensity
import Gdbh.PathC_PairedBrunStirlingSqrt
import Gdbh.PathC_PairedBrunSmallZ
import Gdbh.PathC_PairedMainTermAssembly

/-!
# Path C — P18-T5: Mechanical assembly for `PairedBrunBonferroniSubSqrt`

This file is the **P18-T5 deliverable** in Phase 18 (Path C closure).
Its target is the named open Prop
`Gdbh.PathCPairedBrunLowRegion.PairedBrunBonferroniSubSqrt`, exposed by
P18-T3 as the honest residual of `PairedMainTermResidualLowRegion`:

```
∃ C : ℝ, 0 < C ∧ ∀ n z : ℕ, 0 < n → 3 ≤ z → z < Nat.sqrt n →
  (goldbachSiftedPair n z : ℝ)
    ≤ C · n · pairedBrunFactor z + refinedReservoir n z .
```

## Outcome of this file (mechanical assembly + named residual)

Full closure of the SubSqrt Prop is the classical paired Brun-Bonferroni
argument (Halberstam–Richert *Sieve Methods* §2.2; Nathanson *Additive
Number Theory* §7), uniformly over `z ∈ [3, √n)` and `k(n) = 2n`.  In
one session it is **not realistically** closable from scratch.

We therefore deliver the **mechanical assembly bridge**, in close parallel
to the P18-T4 file `Gdbh/PathC_PairedBrunGoldbachAtSqrt.lean` (which
treats the *same* combinatorial inequality at the single threshold
`z = √n`).  The structural difference here is that the residual must
be uniform over the *range* `z ∈ [3, √n)`, but the Stirling tail
bound from T5-Sqrt is available at every `z ≤ √n`, so the tail half
re-uses T5-Sqrt unchanged.

The deliverable is:

1.  An honest small-`n` vacuity argument: for `n ≤ 9`, the existential
    constraints `3 ≤ z` and `z < Nat.sqrt n` cannot both be satisfied,
    so the inequality is vacuously true.  **Closed here**, axiom-clean.

2.  A precisely-stated **large-`n` named open sub-Prop**
    `BrunGoldbachSubSqrtLargeN`: the SubSqrt inequality restricted to
    `n ≥ N₀`.  This is the genuine analytic residual.

3.  The **outer mechanical bridge** theorem
    `pairedBrunBonferroniSubSqrt_of_largeN`: the large-`n` Prop, combined
    with the (closed) small-`n` vacuity, implies the full SubSqrt Prop.
    **Closed here**, axiom-clean.

4.  A precisely-typed **interior named open sub-Prop**
    `PairedBonferroniInequalitySubSqrtAlignedWithTail`: the paired
    Brun-Bonferroni inequality at every `z ∈ [3, √n)`, **aligned**
    with T5-Sqrt's canonical tail constant `C₃ = 2` and the canonical
    truncation depth `k(n) = 2n`.

5.  A **closed** tail-absorption sub-Prop
    `PairedBonferroniTailSubSqrt`: the Stirling-tail bound for
    `z ∈ [3, √n)`.  This follows from T5-Sqrt with **no additional input**,
    since T5-Sqrt covers all `z ≤ √n`.

6.  The **joint** sub-Prop `AlignedSubSqrtInequalityAndTail` packaging
    both interior sub-Props with shared witnesses, and the corresponding
    interior bridge `brunGoldbachSubSqrtLargeN_of_alignedInequalityAndTail`.

7.  The **end-to-end** mechanical reduction
    `pairedBrunBonferroniSubSqrt_of_alignedInequalityAndTail`:  the joint
    sub-Prop axiom-cleanly implies the SubSqrt Prop.

## Reusability with T4

The structural parallel with `Gdbh/PathC_PairedBrunGoldbachAtSqrt.lean`
(P18-T4) is deliberate:  the **same** Phase 17 atoms (T2, T3, T4, T5-Sqrt)
feed both files; the **same** Stirling tail constant `C₃ = 2` and
canonical truncation depth `k(n) = 2n` are reused.  Closing the interior
Bonferroni inequality (which is the genuine residual in both files)
requires the *paired* Brun-Bonferroni argument, which would apply
uniformly at every `z ∈ [3, √n]`.  In particular, if such a unified
inequality were closed, both the AtSqrt and SubSqrt aligned residuals
would discharge simultaneously.

## Phase 17 atoms consumed

* **T2** `brunBonferroniIndicator_holds` (single-variable Brun-Bonferroni
  inequality at indicator level).  Used inside the interior residual.
* **T3** `goldbachPairCRTCount_holds` (paired CRT counting kernel).
  Used inside the interior residual.
* **T4** `paired_eulerProduct_identity_pairedBrunFactor` (Euler product
  algebraic identity for `pairedBrunFactor`).  Used inside the interior
  residual.
* **T5-Sqrt** `pairedBrunStirlingTruncationErrorSqrt_holds` (Stirling
  truncation tail at `z ≤ √n`).  Used **directly** in this file to close
  `PairedBonferroniTailSubSqrt`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* All theorems below are axiom-clean: only `Classical.choice`,
  `Quot.sound`, `propext`.

## Honest residual after this file

* `AlignedSubSqrtInequalityAndTail` — the joint statement of the paired
  Brun-Bonferroni inequality at sub-`√n` thresholds (aligned constants)
  and the Stirling tail absorption (T5-Sqrt) with a shared truncation
  depth.  The tail half is closed here; the Bonferroni half is the
  genuine analytic residual.

## Honesty note on Phase 17 atom strength

The Phase 17 atom T2 (`brunBonferroniIndicator_holds`) is the
**single-variable** Brun-Bonferroni inequality.  The classical
Brun-Goldbach argument over `z ∈ [3, √n)` uses a **paired** Bonferroni
inequality — one for each side of the additive split — applied at every
sub-`√n` threshold uniformly.  The paired version follows from two
applications of T2 plus a product expansion and an order-of-summation
argument (via T3) and the Euler product identity (T4).  The bookkeeping
is non-trivial, and the additional uniformity in `z` (relative to the
AtSqrt slice) is an extra requirement.  Closing
`PairedBonferroniInequalitySubSqrtAlignedWithTail` requires precisely
this paired upgrade with the uniformity built in, plus the constant
alignment to T5-Sqrt's `C₃ = 2`.  This is the precise irreducible
content of the residual exposed by P18-T5.
-/

namespace Gdbh
namespace PathCPairedBrunSubSqrtProof

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
open Gdbh.PathCPairedBrunLowRegion
  (PairedBrunBonferroniSubSqrt
   subSqrt_vacuous_on_small_n)

/-! ## Section 1 — Small-`n` vacuity

For `n ≤ 9`, the existential constraints `3 ≤ z < Nat.sqrt n` are
unsatisfiable (since `Nat.sqrt 9 = 3 ≤ 3`).  The SubSqrt inequality is
therefore vacuously true on this range, regardless of the choice of `C`.

This vacuity is established axiom-cleanly by
`subSqrt_vacuous_on_small_n` from `PathC_PairedBrunLowRegion`. -/

/-- **Small-`n` slice closure** (vacuous).  For `n ≤ 9`, no `z`
satisfies `3 ≤ z < Nat.sqrt n`, so the SubSqrt inequality is
vacuously true at any `C ≥ 0`. -/
theorem brunGoldbachSubSqrt_small_n
    {C : ℝ} {n z : ℕ} (_hC_nn : 0 ≤ C)
    (_hn : 0 < n) (h_n_le_9 : n ≤ 9)
    (hz_ge_3 : 3 ≤ z) (hz_lt_sqrt : z < Nat.sqrt n) :
    (goldbachSiftedPair n z : ℝ)
      ≤ C * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
  -- The hypotheses are jointly inconsistent.
  exact (subSqrt_vacuous_on_small_n h_n_le_9 hz_ge_3 hz_lt_sqrt).elim

/-! ## Section 2 — Large-`n` named open sub-Prop

The genuine analytic content of the SubSqrt Prop is concentrated on
`n ≥ N₀ ≥ 10` (so the constraint `z ∈ [3, √n)` is non-vacuous).  We
expose this slice as a named open sub-Prop. -/

/-- **`BrunGoldbachSubSqrtLargeN`** — the large-`n` slice of the SubSqrt Prop.

For some absolute constants `C > 0` and `N₀ : ℕ` (with `N₀ ≥ 10`), for
every `n ≥ N₀` and every `z` with `3 ≤ z < Nat.sqrt n`,

```
(goldbachSiftedPair n z : ℝ)
  ≤ C · n · pairedBrunFactor z + refinedReservoir n z .
```

**Status**: classical paired Brun-Bonferroni inequality at sub-`√n`
sieve thresholds, uniform in `z ∈ [3, √n)`.  Multi-thousand-line
classical sieve theory.  Mathlib v4.29.1 **open**. -/
def BrunGoldbachSubSqrtLargeN : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 10 ≤ N₀ ∧
    ∀ n z : ℕ, N₀ ≤ n → 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z

/-! ## Section 3 — Outer mechanical bridge: large-`n` ⇒ full SubSqrt Prop -/

/-- **Outer mechanical bridge**: `BrunGoldbachSubSqrtLargeN` ⇒ full
SubSqrt Prop.

Strategy: for `n ≥ N₀`, use the large-`n` hypothesis directly.  For
`1 ≤ n < N₀`, the SubSqrt constraint `3 ≤ z < Nat.sqrt n` forces
`n ≥ 10` (since otherwise `Nat.sqrt n ≤ 3` and no `z` exists), so all
remaining cases either have `n ≤ 9` (vacuous via Section 1) or
`10 ≤ n < N₀`.

For `10 ≤ n < N₀`, we use the trivial cardinal bound
`goldbachSiftedPair n z ≤ n` and absorb it into the main term via a
constant `M_bd` chosen as the maximum of `n / pairedBrunFactor z` over
the finite range `(n, z) ∈ [10, N₀ - 1] × [3, N₀ - 1]`. -/
theorem pairedBrunBonferroniSubSqrt_of_largeN
    (h : BrunGoldbachSubSqrtLargeN) :
    PairedBrunBonferroniSubSqrt := by
  classical
  obtain ⟨C₀, N₀, hC₀_pos, _hN₀_ge_10, hLarge⟩ := h
  -- Range for bounded `n`:  `n ∈ [10, max N₀ 10]`, `z ∈ [3, max N₀ 10]`.
  set M : ℕ := max N₀ 10 with hM_def
  have hM_ge_N₀ : N₀ ≤ M := le_max_left _ _
  have hM_ge_10 : (10 : ℕ) ≤ M := le_max_right _ _
  -- We build a finite cover of the bounded `(n, z)` cases and take a max.
  set S : Finset (ℕ × ℕ) := (Finset.Icc 10 M) ×ˢ (Finset.Icc 3 M) with hS_def
  have hS_ne : S.Nonempty := by
    rw [hS_def]
    refine Finset.Nonempty.product ?_ ?_
    · refine Finset.nonempty_Icc.mpr ?_; exact hM_ge_10
    · refine Finset.nonempty_Icc.mpr ?_; omega
  let f : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) / pairedBrunFactor p.2
  set fS : Finset ℝ := S.image f with hfS_def
  have hfS_ne : fS.Nonempty := by
    rw [hfS_def]; exact Finset.image_nonempty.mpr hS_ne
  set M_bd : ℝ := fS.max' hfS_ne with hM_bd_def
  have hM_bd_ge : ∀ p ∈ S, f p ≤ M_bd := by
    intro p hp
    rw [hM_bd_def]
    refine Finset.le_max' fS (f p) ?_
    rw [hfS_def]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  set C_eff : ℝ := max C₀ M_bd + 1 with hC_eff_def
  have hC_eff_ge_one : 1 ≤ C_eff := by
    rw [hC_eff_def]
    have : 0 ≤ max C₀ M_bd := le_max_of_le_left (le_of_lt hC₀_pos)
    linarith
  have hC_eff_pos : 0 < C_eff := by linarith
  have hC₀_le_eff : C₀ ≤ C_eff := by
    rw [hC_eff_def]
    have : C₀ ≤ max C₀ M_bd := le_max_left _ _
    linarith
  have hM_bd_le_eff : M_bd ≤ C_eff := by
    rw [hC_eff_def]
    have : M_bd ≤ max C₀ M_bd := le_max_right _ _
    linarith
  refine ⟨C_eff, hC_eff_pos, ?_⟩
  intro n z hn_pos hz_ge_3 hz_lt_sqrt
  by_cases hN : N₀ ≤ n
  · -- Case `n ≥ N₀`: use the large-`n` hypothesis with the original `C₀`.
    have hLargeN := hLarge n z hN hz_ge_3 hz_lt_sqrt
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hpf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos _)
    have h_prod_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
      mul_nonneg hn_nn hpf_nn
    have hMul_le :
        C₀ * (n : ℝ) * pairedBrunFactor z
          ≤ C_eff * (n : ℝ) * pairedBrunFactor z := by
      have : C₀ * ((n : ℝ) * pairedBrunFactor z)
          ≤ C_eff * ((n : ℝ) * pairedBrunFactor z) :=
        mul_le_mul_of_nonneg_right hC₀_le_eff h_prod_nn
      linarith
    linarith
  · -- Case `n < N₀`.
    have hn_lt : n < N₀ := by
      have := hN; omega
    by_cases hn_small : n ≤ 9
    · -- Sub-case: `n ≤ 9`, the constraints are vacuous.
      exact brunGoldbachSubSqrt_small_n (le_of_lt hC_eff_pos)
        hn_pos hn_small hz_ge_3 hz_lt_sqrt
    · -- Sub-case: `10 ≤ n < N₀`.  Bound the trivial cardinal `n` via `M_bd`.
      have hn_ge_10 : 10 ≤ n := by omega
      have hn_le_M : n ≤ M := by
        have : n ≤ N₀ := le_of_lt hn_lt
        omega
      -- Bound `z`: from `z < Nat.sqrt n ≤ Nat.sqrt M`.
      have hsqrt_le : Nat.sqrt n ≤ Nat.sqrt M := Nat.sqrt_le_sqrt hn_le_M
      -- `Nat.sqrt M ≤ M`, so `z ≤ M`.
      have hsqrt_M_le_M : Nat.sqrt M ≤ M := Nat.sqrt_le_self _
      have hz_le_M : z ≤ M := by
        have hz_lt_sqrt' : z < Nat.sqrt n := hz_lt_sqrt
        have : z < Nat.sqrt M := lt_of_lt_of_le hz_lt_sqrt' hsqrt_le
        omega
      -- `(n, z) ∈ S`.
      have hp_in_S : (n, z) ∈ S := by
        rw [hS_def, Finset.mem_product]
        refine ⟨?_, ?_⟩
        · exact Finset.mem_Icc.mpr ⟨hn_ge_10, hn_le_M⟩
        · exact Finset.mem_Icc.mpr ⟨hz_ge_3, hz_le_M⟩
      have hfp_le : f (n, z) ≤ M_bd := hM_bd_ge (n, z) hp_in_S
      have hfp_le_eff : f (n, z) ≤ C_eff := le_trans hfp_le hM_bd_le_eff
      have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have hpf_pos : 0 < pairedBrunFactor z := pairedBrunFactor_pos _
      have hpf_nn : 0 ≤ pairedBrunFactor z := le_of_lt hpf_pos
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
      have hres_nn : 0 ≤ refinedReservoir n z :=
        refinedReservoir_nonneg n z
      have hsift_le_n : (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast goldbachSiftedPair_le n z
      have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℕ) ≤ n := by omega
        exact_mod_cast this
      have h_f_pf_eq_n :
          f (n, z) * pairedBrunFactor z = (n : ℝ) := by
        change ((n : ℝ) / pairedBrunFactor z) * pairedBrunFactor z = (n : ℝ)
        field_simp
      have h_eff_pf_ge_n :
          (n : ℝ) ≤ C_eff * pairedBrunFactor z := by
        calc (n : ℝ) = f (n, z) * pairedBrunFactor z := h_f_pf_eq_n.symm
          _ ≤ C_eff * pairedBrunFactor z :=
              mul_le_mul_of_nonneg_right hfp_le_eff hpf_nn
      have h_n_mul :
          (n : ℝ) ≤ C_eff * (n : ℝ) * pairedBrunFactor z := by
        have h_mul := mul_le_mul_of_nonneg_left h_eff_pf_ge_n hn_nn
        have h_rhs_eq : (n : ℝ) * (C_eff * pairedBrunFactor z)
            = C_eff * (n : ℝ) * pairedBrunFactor z := by ring
        rw [h_rhs_eq] at h_mul
        have : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
          have h1 : (n : ℝ) * 1 ≤ (n : ℝ) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hn_ge_one hn_nn
          linarith
        linarith
      linarith

/-! ## Section 4 — Interior named open sub-Props

We expose the **aligned** paired Brun-Bonferroni inequality at every
`z ∈ [3, √n)`, where "aligned" means the inequality's constant is
bounded by `2`, the canonical Stirling-tail constant from T5-Sqrt.

This alignment is required so that the interior bridge closes
axiom-cleanly (i.e., without further analytic input).  The shape of
the inequality and tail is *identical* to the AtSqrt case in
`Gdbh/PathC_PairedBrunGoldbachAtSqrt.lean` — the only structural
difference is that the universal quantifier ranges over `z ∈ [3, √n)`
instead of `z = √n` only.  In particular, T5-Sqrt covers all
`z ≤ √n`, so the tail bound closes uniformly. -/

/-- **`PairedBonferroniInequalitySubSqrtAlignedWithTail`** — the
**aligned** paired Brun-Bonferroni inequality at every `z ∈ [3, √n)`.

For some constants `C₂ > 0` (with `C₂ ≤ 2`) and `N₁ : ℕ` (with
`N₁ ≥ 10`), and some function `k : ℕ → ℕ`, for every `n ≥ N₁` and
every `z` with `3 ≤ z < Nat.sqrt n`,

```
(goldbachSiftedPair n z : ℝ)
  ≤ C₂ · n · pairedBrunFactor z
    + C₂ · n · (π(z))^{2k(n)+1} / (2k(n)+1)! .
```

This is the genuine paired Brun-Bonferroni inequality, aligned with
T5-Sqrt's tail constant `C₃ = 2`:  apply the single-variable
Bonferroni (`T2 := brunBonferroniIndicator_holds`) to both
`1{m coprime to all p ≤ z}` and `1{(n-m) coprime to all p ≤ z}`,
then expand the product and apply the paired CRT counting kernel
(`T3 := goldbachPairCRTCount_holds`).  The first RHS term is the
"main term" via the Euler product identity
(`T4 := paired_eulerProduct_identity_pairedBrunFactor`); the second
is the "Bonferroni tail" bounded combinatorially.

**Status**: classical paired Brun-Bonferroni at sub-`√n` thresholds.
Uniformity over `z ∈ [3, √n)` is required.  Mathlib v4.29.1 **open**. -/
def PairedBonferroniInequalitySubSqrtAlignedWithTail : Prop :=
  ∃ C₂ : ℝ, ∃ N₁ : ℕ, ∃ k : ℕ → ℕ,
    0 < C₂ ∧ C₂ ≤ 2 ∧ 10 ≤ N₁ ∧
    ∀ n z : ℕ, N₁ ≤ n → 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₂ * (n : ℝ) * pairedBrunFactor z
          + C₂ * (n : ℝ)
              * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)

/-- **`PairedBonferroniTailSubSqrt`** — the **Stirling tail absorption**
at every `z ∈ [3, √n)`.

For some constants `C₃ > 0` and `N₂ : ℕ`, and some function `k : ℕ → ℕ`,

```
∀ n ≥ N₂, ∀ z with 3 ≤ z < Nat.sqrt n,
  C₃ · n · (π(z))^{2k(n)+1} / (2k(n)+1)! ≤ refinedReservoir n z .
```

**Status**: this Prop is **closed** from
`pairedBrunStirlingTruncationErrorSqrt_holds` (T5-Sqrt) — see
`pairedBonferroniTailSubSqrt_holds` below.  The closure uses the same
witnesses as T5-Sqrt:  T5-Sqrt covers all `z ≤ √n`, so the sub-`√n`
slice is automatic. -/
def PairedBonferroniTailSubSqrt : Prop :=
  ∃ C₃ : ℝ, ∃ k : ℕ → ℕ, ∃ N₂ : ℕ,
    0 < C₃ ∧ 10 ≤ N₂ ∧
    ∀ n z : ℕ, N₂ ≤ n → 3 ≤ z → z < Nat.sqrt n →
      C₃ * (n : ℝ)
          * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        ≤ refinedReservoir n z

/-! ## Section 5 — Closure of `PairedBonferroniTailSubSqrt` via T5-Sqrt

T5-Sqrt's content is:
```
∃ k, ∃ N₀, ∀ n z, N₀ ≤ n → z ≤ Nat.sqrt n →
  n · π(z)^{2k+1} / (2k+1)! ≤ n / (2 (log n)²) .
```

Note T5-Sqrt is stated with `z ≤ Nat.sqrt n`, so it covers our SubSqrt
range `z < Nat.sqrt n` immediately (`z < √n ⟹ z ≤ √n`).  Multiplying
by `2`, we get the sub-`√n` tail Prop with `C₃ = 2`, the same `k`,
and `N₀ = max(T5-Sqrt's N₀, 10)`. -/

/-- **Closure of `PairedBonferroniTailSubSqrt`** via T5-Sqrt. -/
theorem pairedBonferroniTailSubSqrt_holds : PairedBonferroniTailSubSqrt := by
  classical
  obtain ⟨k₀, N₀_S, hS⟩ :=
    Gdbh.PathCPairedBrunStirlingSqrt.pairedBrunStirlingTruncationErrorSqrt_holds
  refine ⟨2, k₀, max N₀_S 10, by norm_num, le_max_right _ _, ?_⟩
  intro n z hn hz_ge_3 hz_lt_sqrt
  have hn_NS : N₀_S ≤ n := le_trans (le_max_left _ _) hn
  have hn10 : 10 ≤ n := le_trans (le_max_right _ _) hn
  -- T5-Sqrt at `(n, z)`:  use `z ≤ Nat.sqrt n` from `z < Nat.sqrt n`.
  have hz_le_sqrt : z ≤ Nat.sqrt n := le_of_lt hz_lt_sqrt
  have hT5 := hS n z hn_NS hz_le_sqrt
  -- Unfold `refinedReservoir n z = n / (log n)²`.
  unfold refinedReservoir
  have h_n_real_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h_n_real_ge10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
  have h_log_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    linarith
  have h_log_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have h_2logsq_pos : 0 < 2 * (Real.log (n : ℝ))^2 := by linarith
  have hrhs_eq : 2 * ((n : ℝ) / (2 * (Real.log (n : ℝ))^2))
      = (n : ℝ) / (Real.log (n : ℝ))^2 := by
    field_simp
  have h2_mul :
      2 * ((n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k₀ n + 1)
            / ((2 * k₀ n + 1).factorial : ℝ))
        ≤ 2 * ((n : ℝ) / (2 * (Real.log (n : ℝ))^2)) :=
    mul_le_mul_of_nonneg_left hT5 (by norm_num : (0 : ℝ) ≤ 2)
  rw [hrhs_eq] at h2_mul
  have h_goal_eq :
      2 * (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k₀ n + 1)
              / ((2 * k₀ n + 1).factorial : ℝ)
        = 2 * ((n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k₀ n + 1)
                / ((2 * k₀ n + 1).factorial : ℝ)) := by
    ring
  rw [h_goal_eq]
  exact h2_mul

/-! ## Section 6 — Joint witness Prop and interior bridge

We expose the **joint** sub-Prop pairing the aligned inequality and the
(closed) tail with a *single* shared truncation depth `k` and a *single*
threshold `N`.  This is the precise residual whose closure delivers
`BrunGoldbachSubSqrtLargeN`. -/

/-- **`AlignedSubSqrtInequalityAndTail`** — the joint statement of the
aligned paired Brun-Bonferroni inequality and the (closed) Stirling tail
absorption at sub-`√n` thresholds, with shared witnesses. -/
def AlignedSubSqrtInequalityAndTail : Prop :=
  ∃ C₂ : ℝ, ∃ C₃ : ℝ, ∃ N : ℕ, ∃ k : ℕ → ℕ,
    0 < C₂ ∧ 0 < C₃ ∧ C₂ ≤ C₃ ∧ 10 ≤ N ∧
    (∀ n z : ℕ, N ≤ n → 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₂ * (n : ℝ) * pairedBrunFactor z
          + C₂ * (n : ℝ)
              * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)) ∧
    (∀ n z : ℕ, N ≤ n → 3 ≤ z → z < Nat.sqrt n →
      C₃ * (n : ℝ)
          * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        ≤ refinedReservoir n z)

/-- **Interior mechanical bridge**:
`AlignedSubSqrtInequalityAndTail` ⇒ `BrunGoldbachSubSqrtLargeN`. -/
theorem brunGoldbachSubSqrtLargeN_of_alignedInequalityAndTail
    (h : AlignedSubSqrtInequalityAndTail) : BrunGoldbachSubSqrtLargeN := by
  classical
  obtain ⟨C₂, C₃, N, k, hC₂_pos, _hC₃_pos, hCle, hN, hIneq, hTail⟩ := h
  refine ⟨C₂, N, hC₂_pos, hN, ?_⟩
  intro n z hn hz_ge_3 hz_lt_sqrt
  have hIneqN := hIneq n z hn hz_ge_3 hz_lt_sqrt
  have hTailN := hTail n z hn hz_ge_3 hz_lt_sqrt
  have h_pow_nn :
      (0 : ℝ) ≤ (Nat.primeCounting z : ℝ)^(2 * k n + 1) :=
    pow_nonneg (by exact_mod_cast Nat.zero_le _) _
  have h_fact_pos :
      (0 : ℝ) < ((2 * k n + 1).factorial : ℝ) := by
    have : 0 < (2 * k n + 1).factorial := Nat.factorial_pos _
    exact_mod_cast this
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  set T_n : ℝ := (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) with hT_n_def
  have hT_nn : 0 ≤ T_n := by
    rw [hT_n_def]
    exact div_nonneg (mul_nonneg hn_nn h_pow_nn) (le_of_lt h_fact_pos)
  have h_C_T_le : C₂ * T_n ≤ C₃ * T_n :=
    mul_le_mul_of_nonneg_right hCle hT_nn
  have h_C₃_T_eq :
      C₃ * (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        = C₃ * T_n := by
    rw [hT_n_def]; ring
  rw [h_C₃_T_eq] at hTailN
  have h_C₂_T_le_res : C₂ * T_n ≤ refinedReservoir n z :=
    le_trans h_C_T_le hTailN
  have h_C₂_T_eq :
      C₂ * (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        = C₂ * T_n := by
    rw [hT_n_def]; ring
  rw [h_C₂_T_eq] at hIneqN
  linarith

/-! ## Section 7 — End-to-end closure modulo `AlignedSubSqrtInequalityAndTail`

Combining the interior bridge with the outer mechanical bridge yields
the end-to-end closure of `PairedBrunBonferroniSubSqrt` modulo
`AlignedSubSqrtInequalityAndTail`.

Since `PairedBonferroniTailSubSqrt` is closed unconditionally
(`pairedBonferroniTailSubSqrt_holds`), the residual content is the
paired Brun-Bonferroni inequality at every `z ∈ [3, √n)`, **aligned**
with T5-Sqrt's witnesses. -/

/-- **End-to-end closure modulo `AlignedSubSqrtInequalityAndTail`**.

This is the **public deliverable** of P18-T5: the SubSqrt Prop is
reduced axiom-cleanly to the joint residual
`AlignedSubSqrtInequalityAndTail`. -/
theorem pairedBrunBonferroniSubSqrt_of_alignedInequalityAndTail
    (h : AlignedSubSqrtInequalityAndTail) :
    PairedBrunBonferroniSubSqrt :=
  pairedBrunBonferroniSubSqrt_of_largeN
    (brunGoldbachSubSqrtLargeN_of_alignedInequalityAndTail h)

/-! ## Section 8 — P18-T5 summary -/

/-- **P18-T5 summary, in proof form.**

**Mission**: close `PairedBrunBonferroniSubSqrt` from the Phase 17
atomic budget T1-T5.

**Outcome**:

1. **Small-`n` vacuity** (`brunGoldbachSubSqrt_small_n`): closed
   axiom-clean.  For `n ≤ 9`, the existential constraints on `z`
   are unsatisfiable.

2. **Large-`n` named open sub-Prop** (`BrunGoldbachSubSqrtLargeN`):
   exposed.  The genuine analytic residual.

3. **Outer mechanical bridge**
   (`pairedBrunBonferroniSubSqrt_of_largeN`):  closed axiom-clean.
   Combines small-`n` vacuity + large-`n` into full Prop.

4. **Tail-absorption sub-Prop** (`PairedBonferroniTailSubSqrt`):
   exposed and **closed unconditionally** from T5-Sqrt
   (`pairedBonferroniTailSubSqrt_holds`).  This is the key reuse of
   T5-Sqrt:  the Stirling tail bound covers all `z ≤ √n`, hence the
   strict sub-`√n` slice as well.

5. **Aligned inequality sub-Prop**
   (`PairedBonferroniInequalitySubSqrtAlignedWithTail`):  exposed.
   The genuine combinatorial residual, uniform in `z ∈ [3, √n)`.

6. **Joint witness Prop** (`AlignedSubSqrtInequalityAndTail`):
   exposed.  Combines both interior sub-Props with the alignment
   constraint `C₂ ≤ C₃` and a shared truncation depth `k`.

7. **Interior mechanical bridge**
   (`brunGoldbachSubSqrtLargeN_of_alignedInequalityAndTail`):  closed
   axiom-clean.

8. **End-to-end bridge**
   (`pairedBrunBonferroniSubSqrt_of_alignedInequalityAndTail`):
   closed axiom-clean.  Reduces the full SubSqrt Prop to
   `AlignedSubSqrtInequalityAndTail`.

**Residual**:  `AlignedSubSqrtInequalityAndTail` — the joint statement
of the paired Brun-Bonferroni inequality (aligned constants, uniform
in `z ∈ [3, √n)`) and the Stirling tail absorption (T5-Sqrt) with a
shared truncation depth.  The tail half is closed; the Bonferroni half
is the genuine analytic residual.

**Phase 17 atoms used**: T5-Sqrt (Stirling tail, directly closing the
tail sub-Prop here).
**Phase 17 atoms not directly used in mechanical pieces**: T2
(Bonferroni — needed inside the residual), T3 (CRT count — needed
inside the residual), T4 (Euler product — needed inside the residual).

**Relationship to P18-T4 (AtSqrt)**: The structural parallel is
deliberate.  The interior residual
`PairedBonferroniInequalitySubSqrtAlignedWithTail` is a uniform-in-`z`
strengthening of P18-T4's interior residual
`PairedBonferroniInequalityAtSqrtAlignedWithTail` (with `z ∈ [3, √n)`
instead of `z = √n` only).  Closing the uniform version closes both.

**False-Prop catches in this round**: none.

All non-deferred theorems are axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`. -/
theorem pathC_p18_t5_summary : True := trivial

end PathCPairedBrunSubSqrtProof
end Gdbh
