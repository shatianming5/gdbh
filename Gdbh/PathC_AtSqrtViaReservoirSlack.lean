/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T49 (Phase 19 / Path C — Closing `BrunGoldbachPairedMainTermRefinedAtSqrt`
        via the reservoir slack and the closed paired-Brun lower gap)
-/
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_MertensSecondUpper
import Gdbh.PathC_PairedBrunMertensLowerReal

/-!
# Path C — P19-T49: Closing `BrunGoldbachPairedMainTermRefinedAtSqrt`
                   via reservoir slack

## Headline result

The named refined sub-Prop
`Gdbh.PathCPairedMainTermAssembly.BrunGoldbachPairedMainTermRefinedAtSqrt`
reduces — **without any new `sorry`/`axiom`/`admit`** — to the
single classical input

```
BrunGoldbachClassicalBound : Prop :=
  ∃ K N₀ : ℕ, 0 < K ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (K : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 .
```

The bridge consumes the **already-closed** lower-Mertens gap
`Gdbh.PathCMertensSecondUpper.pairedBrunMertensThirdLowerGap_holds`,
which provides

```
∃ C > 0, ∃ z₀, ∀ z ≥ z₀, pairedBrunFactor z ≥ C / (log z)² .
```

## Mathematical strategy

Suppose `goldbachSiftedPair n √n ≤ K · n / (log n)²` for `n ≥ N₀`
(the classical Brun-Goldbach upper bound — Halberstam-Richert §3.3,
Nathanson §7.5).  We need

```
goldbachSiftedPair n √n ≤ C₁ · n · pairedBrunFactor (√n)
                          + refinedReservoir n √n .
```

* **Asymptotic regime** (`n ≥ max(N₀, z₀² + 1, 4)`):
  The closed lower gap gives `pairedBrunFactor (√n) ≥ C₀ / (log √n)²`
  for `√n ≥ z₀`.  Since `√n ≥ 2` (from `n ≥ 4`), `log √n > 0`.  Since
  `log √n ≤ log n`, this yields `pairedBrunFactor (√n) ≥ C₀ / (log n)²`.
  Multiplying by `n`, `n · pairedBrunFactor (√n) ≥ C₀ · n / (log n)²`.
  Hence `K · n / (log n)² ≤ (K / C₀) · n · pairedBrunFactor (√n)`, and
  we conclude with `C_large := K / C₀`.

* **Small-`n` regime** (`n < Nstar := max(N₀, z₀² + 1, 4)`):
  Use the trivial bound `goldbachSiftedPair n √n ≤ n` and the
  positivity of `pairedBrunFactor`.  The finite-range sum
  `C_small := ∑_{k ∈ [1, Nstar]} (1 + 1 / pairedBrunFactor (√k))`
  dominates `1 / pairedBrunFactor (√n)` for each `n ≤ Nstar`,
  giving `n ≤ C_small · n · pairedBrunFactor (√n)`.

Both regimes' constants are non-negative; their sum (plus a buffer
of 1) is a uniform `C₁` that works for all `n ≥ 1`.

## Honesty status

* `BrunGoldbachClassicalBound` is **still open** in mathlib v4.29.1.
  It is the uniform Brun-Goldbach upper bound (Halberstam-Richert
  §3.3, Nathanson §7.5).  This file does **not** close it.
* The bridge from `BrunGoldbachClassicalBound` to
  `BrunGoldbachPairedMainTermRefinedAtSqrt` **is** closed here
  axiom-cleanly.
* All theorems below are axiom-clean: only `Classical.choice`,
  `Quot.sound`, `propext`.

## Strategic significance

The reservoir `n / (log n)²` provides enormous additive slack —
already at `n = 30` it dominates the LHS.  This file documents
that the named Prop is reducible to a **single** classical input,
with no further analytic infrastructure needed: the closed lower
Mertens gap is the only auxiliary input, and it is already in the
repo.
-/

namespace Gdbh
namespace PathCAtSqrtViaReservoirSlack

open Real Finset
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (refinedReservoir_nonneg)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt)
open Gdbh.PathCPairedBrunMertensLowerReal
  (PairedBrunMertensThirdLowerGap)
open Gdbh.PathCMertensSecondUpper
  (pairedBrunMertensThirdLowerGap_holds)

/-! ## Section 1 — The classical Brun-Goldbach Prop -/

/-- **Classical Brun-Goldbach upper bound.**

There exist a positive constant `K` and a threshold `N₀` such that
for all `n ≥ N₀`,

```
goldbachSiftedPair n (Nat.sqrt n)  ≤  K · n / (log n)² .
```

This is the genuine open mathlib content treated in
Halberstam-Richert *Sieve Methods* §3.3 and Nathanson *Additive
Number Theory* §7.5.  Mathlib v4.29.1 status: **open**.

We use `K : ℕ` (cast to `ℝ`) for arithmetic convenience; the
formulation is equivalent to one with `K : ℝ` up to a `⌈·⌉`
substitution. -/
def BrunGoldbachClassicalBound : Prop :=
  ∃ K N₀ : ℕ, 0 < K ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (K : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2

/-! ## Section 2 — Small-range absorption constant -/

/-- A finite-range constant absorbing all `n ∈ [1, Nstar]`. -/
private noncomputable def smallRangeConst (Nstar : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Nstar, (1 + 1 / pairedBrunFactor (Nat.sqrt k))

private lemma smallRangeConst_nonneg (Nstar : ℕ) :
    0 ≤ smallRangeConst Nstar := by
  unfold smallRangeConst
  refine Finset.sum_nonneg ?_
  intro k _
  have h2 : 0 ≤ 1 / pairedBrunFactor (Nat.sqrt k) := by
    have hpf_pos : 0 < pairedBrunFactor (Nat.sqrt k) := pairedBrunFactor_pos _
    positivity
  linarith

/-- For each `k ∈ [1, Nstar]`,
`1 / pairedBrunFactor (Nat.sqrt k) ≤ smallRangeConst Nstar`. -/
private lemma smallRangeConst_ge_one_div_pBF
    {Nstar k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ Nstar) :
    1 / pairedBrunFactor (Nat.sqrt k) ≤ smallRangeConst Nstar := by
  unfold smallRangeConst
  have hk_mem : k ∈ Finset.Icc 1 Nstar := Finset.mem_Icc.mpr ⟨h1, h2⟩
  have h_term_le_sum :
      (1 + 1 / pairedBrunFactor (Nat.sqrt k))
        ≤ ∑ j ∈ Finset.Icc 1 Nstar,
            (1 + 1 / pairedBrunFactor (Nat.sqrt j)) := by
    refine Finset.single_le_sum (f := fun j =>
        (1 + 1 / pairedBrunFactor (Nat.sqrt j))) ?_ hk_mem
    intro j _
    have hpf_pos : 0 < pairedBrunFactor (Nat.sqrt j) := pairedBrunFactor_pos _
    have h2' : 0 ≤ 1 / pairedBrunFactor (Nat.sqrt j) := by positivity
    linarith
  have h_le_self : 1 / pairedBrunFactor (Nat.sqrt k)
      ≤ 1 + 1 / pairedBrunFactor (Nat.sqrt k) := by linarith
  linarith

/-! ## Section 3 — The bridge theorem -/

/-- **Bridge (P19-T49)**: the classical Brun-Goldbach bound implies the
refined paired main-term Prop specialised at `Nat.sqrt`.

The proof uses the **closed** lower Mertens gap
`pairedBrunMertensThirdLowerGap_holds` together with a small-range
absorption constant.  No `sorry`, no `axiom`, no `admit`. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrt_of_classicalBound
    (hCB : BrunGoldbachClassicalBound) :
    BrunGoldbachPairedMainTermRefinedAtSqrt := by
  -- Extract the classical bound.
  obtain ⟨K, N₀, hKpos, hCBbd⟩ := hCB
  -- Extract the closed lower Mertens gap.
  obtain ⟨C₀, z₀, hC₀pos, hMertensLB⟩ := pairedBrunMertensThirdLowerGap_holds
  -- Asymptotic-regime threshold: max(N₀, z₀² + 1, 4).
  set Nstar : ℕ := max (max N₀ (z₀ * z₀ + 1)) 4 with hNstar_def
  -- Large-n constant: K / C₀.
  set C_large : ℝ := (K : ℝ) / C₀ with hCl_def
  have hCl_pos : 0 < C_large := by
    rw [hCl_def]; exact div_pos (by exact_mod_cast hKpos) hC₀pos
  -- Small-n constant: smallRangeConst Nstar.
  set C_small : ℝ := smallRangeConst Nstar with hCs_def
  have hCs_nn : 0 ≤ C_small := smallRangeConst_nonneg Nstar
  -- Witness C₁ := C_large + C_small + 1 > 0.
  refine ⟨C_large + C_small + 1, by linarith, ?_⟩
  intro n hn
  -- Useful positivity facts.
  have hpf_pos : 0 < pairedBrunFactor (Nat.sqrt n) := pairedBrunFactor_pos _
  have hpf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := le_of_lt hpf_pos
  have hn_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hRes_nn : 0 ≤ refinedReservoir n (Nat.sqrt n) :=
    refinedReservoir_nonneg n (Nat.sqrt n)
  -- Case split: n ≤ Nstar or n > Nstar.
  by_cases hcase : n ≤ Nstar
  · -- ============ Small-n regime ============
    -- Trivial bound: goldbachSiftedPair n √n ≤ n.
    have hLHS_le_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
      have h_nat : goldbachSiftedPair n (Nat.sqrt n) ≤ n :=
        goldbachSiftedPair_le n (Nat.sqrt n)
      exact_mod_cast h_nat
    -- Small-range absorption: 1/pBF ≤ C_small.
    have hSmall : 1 / pairedBrunFactor (Nat.sqrt n) ≤ C_small :=
      smallRangeConst_ge_one_div_pBF hn hcase
    -- Multiply by pBF > 0: 1 ≤ C_small · pBF.
    have h1_le : (1 : ℝ) ≤ C_small * pairedBrunFactor (Nat.sqrt n) := by
      have := (div_le_iff₀ hpf_pos).mp hSmall
      linarith
    -- Multiply by n ≥ 0: n ≤ C_small · n · pBF.
    have h_n_le : (n : ℝ) ≤ C_small * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
      have hmul := mul_le_mul_of_nonneg_left h1_le hn_real_nn
      -- hmul : n * 1 ≤ n * (C_small * pBF)
      have hL : (n : ℝ) * 1 = (n : ℝ) := by ring
      have hR : (n : ℝ) * (C_small * pairedBrunFactor (Nat.sqrt n))
          = C_small * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by ring
      linarith [hmul, hL, hR]
    -- Other contributions non-negative.
    have hC_large_part_nn : 0 ≤ C_large * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
      have hCl_nn := le_of_lt hCl_pos
      positivity
    -- Decompose: (C_large + C_small + 1) · n · pBF = sum of three pieces.
    have h_split :
        (C_large + C_small + 1) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          = C_large * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + C_small * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by ring
    rw [h_split]
    -- Combine.
    have hExtra_nn : 0 ≤ 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by positivity
    linarith
  · -- ============ Asymptotic regime ============
    have hcase : Nstar < n := Nat.lt_of_not_le hcase
    -- Unpack n ≥ Nstar thresholds.
    have h_n_ge_N₀ : N₀ ≤ n := by
      have : N₀ ≤ Nstar := le_trans (le_max_left _ _) (le_max_left _ _)
      omega
    have h_n_ge_z0sq : z₀ * z₀ + 1 ≤ n := by
      have : z₀ * z₀ + 1 ≤ Nstar := le_trans (le_max_right _ _) (le_max_left _ _)
      omega
    have h_n_ge_4 : 4 ≤ n := by
      have : 4 ≤ Nstar := le_max_right _ _
      omega
    -- Apply classical Brun-Goldbach.
    have hCB_at_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (K : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 := hCBbd n h_n_ge_N₀
    -- z₀ ≤ Nat.sqrt n (from z₀² + 1 ≤ n).
    have h_sqrt_ge_z0 : z₀ ≤ Nat.sqrt n := by
      have hz_sq : z₀ * z₀ ≤ n := by omega
      exact Nat.le_sqrt.mpr hz_sq
    -- Nat.sqrt n ≥ 2 (from n ≥ 4).
    have h_sqrt_n_ge_two : 2 ≤ Nat.sqrt n := by
      have h_sq : 2 * 2 ≤ n := by omega
      exact Nat.le_sqrt.mpr h_sq
    have h_sqrt_n_ge_two_r : (2 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by
      exact_mod_cast h_sqrt_n_ge_two
    have h_sqrt_n_pos_r : (0 : ℝ) < ((Nat.sqrt n : ℕ) : ℝ) := by linarith
    have h_sqrt_n_gt_one_r : (1 : ℝ) < ((Nat.sqrt n : ℕ) : ℝ) := by linarith
    -- log(√n) > 0.
    have hlog_sqrt_pos : 0 < Real.log ((Nat.sqrt n : ℕ) : ℝ) := Real.log_pos h_sqrt_n_gt_one_r
    -- log(n) > 0.
    have hn_real_ge_4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_n_ge_4
    have hn_real_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
    have hlogN_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_real_gt_one
    have hlogN_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
    have hlog_sqrt_sq_pos : 0 < (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 := by positivity
    -- Mertens lower gap at z := √n.
    have h_pBF_lower :
        C₀ / (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2
          ≤ pairedBrunFactor (Nat.sqrt n) := hMertensLB (Nat.sqrt n) h_sqrt_ge_z0
    -- √n ≤ n, hence log √n ≤ log n.
    have h_sqrt_le_n : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
    have h_sqrt_le_n_r : ((Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_sqrt_le_n
    have h_log_sqrt_le_logN :
        Real.log ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log h_sqrt_n_pos_r h_sqrt_le_n_r
    -- (log √n)² ≤ (log n)².
    have hlog_sqrt_nn : 0 ≤ Real.log ((Nat.sqrt n : ℕ) : ℝ) := le_of_lt hlog_sqrt_pos
    have hlog_sq_le :
        (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 ≤ (Real.log (n : ℝ))^2 := by
      exact pow_le_pow_left₀ hlog_sqrt_nn h_log_sqrt_le_logN 2
    -- Hence C₀/(log n)² ≤ C₀/(log √n)².
    have h_div_ge : C₀ / (Real.log (n : ℝ))^2
        ≤ C₀ / (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 := by
      exact div_le_div_of_nonneg_left (le_of_lt hC₀pos) hlog_sqrt_sq_pos hlog_sq_le
    -- Combine: pBF(√n) ≥ C₀/(log n)².
    have h_pBF_ge_C0_logn :
        C₀ / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor (Nat.sqrt n) :=
      le_trans h_div_ge h_pBF_lower
    -- Rearrange: C₀ ≤ pBF · (log n)².
    have h_C0_le : C₀ ≤ pairedBrunFactor (Nat.sqrt n) * (Real.log (n : ℝ))^2 :=
      (div_le_iff₀ hlogN_sq_pos).mp h_pBF_ge_C0_logn
    -- Multiply by n: C₀ · n ≤ pBF · (log n)² · n.
    have h_C0_n_le : C₀ * (n : ℝ)
        ≤ pairedBrunFactor (Nat.sqrt n) * (Real.log (n : ℝ))^2 * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_right h_C0_le hn_real_nn
    -- Divide by (log n)² > 0: n · C₀ / (log n)² ≤ pBF · n.
    -- Equivalently: n / (log n)² ≤ (1/C₀) · n · pBF.
    have h_n_div_log_sq_le :
        (n : ℝ) / (Real.log (n : ℝ))^2
          ≤ (1 / C₀) * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) := by
      -- From: C₀ · n ≤ pBF · (log n)² · n, divide both sides by C₀ · (log n)² > 0.
      have hdenom_pos : 0 < C₀ * (Real.log (n : ℝ))^2 := mul_pos hC₀pos hlogN_sq_pos
      have h_n_le_div :
          (n : ℝ) ≤ pairedBrunFactor (Nat.sqrt n) * (Real.log (n : ℝ))^2 * (n : ℝ) / C₀ := by
        rw [le_div_iff₀ hC₀pos]
        linarith [h_C0_n_le]
      -- Now: n / (log n)² ≤ pBF · n / C₀.
      rw [div_le_iff₀ hlogN_sq_pos]
      have hC₀_ne : C₀ ≠ 0 := ne_of_gt hC₀pos
      have h_rhs_eq :
          (1 / C₀) * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) * (Real.log (n : ℝ))^2
            = (pairedBrunFactor (Nat.sqrt n) * (Real.log (n : ℝ))^2 * (n : ℝ)) / C₀ := by
        field_simp
      linarith [h_rhs_eq, h_n_le_div]
    -- Now: K · n / (log n)² ≤ K · (1/C₀) · n · pBF = (K/C₀) · n · pBF = C_large · n · pBF.
    have hK_real_nn : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_K_n_div :
        (K : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2
          ≤ C_large * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
      -- K · n / (log n)² = K · (n / (log n)²) ≤ K · (1/C₀) · n · pBF
      have h_eq_lhs :
          (K : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2
            = (K : ℝ) * ((n : ℝ) / (Real.log (n : ℝ))^2) := by
        field_simp
      have hC₀_ne : C₀ ≠ 0 := ne_of_gt hC₀pos
      have h_eq_rhs :
          (K : ℝ) * ((1 / C₀) * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)))
            = C_large * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
        rw [hCl_def]
        field_simp
      rw [h_eq_lhs]
      have hmul := mul_le_mul_of_nonneg_left h_n_div_log_sq_le hK_real_nn
      linarith [hmul, h_eq_rhs]
    -- Now: LHS ≤ K · n / (log n)² ≤ C_large · n · pBF.
    -- Goal: LHS ≤ (C_large + C_small + 1) · n · pBF + refinedReservoir.
    have h_split :
        (C_large + C_small + 1) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          = C_large * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + C_small * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by ring
    rw [h_split]
    have hC_small_part_nn : 0 ≤ C_small * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
      positivity
    have hExtra_nn : 0 ≤ 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by positivity
    linarith

/-! ## Section 4 — Documentation summary -/

/-- **P19-T49 summary marker** (no content theorem).

Deliverables (axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext`):

1. `BrunGoldbachClassicalBound` — named Prop encoding the classical
   uniform Brun-Goldbach upper bound (open in mathlib v4.29.1).

2. `brunGoldbachPairedMainTermRefinedAtSqrt_of_classicalBound` —
   bridge theorem reducing the named refined sub-Prop
   `BrunGoldbachPairedMainTermRefinedAtSqrt` to
   `BrunGoldbachClassicalBound`.  Uses the closed lower Mertens gap
   `pairedBrunMertensThirdLowerGap_holds` internally.

After P19-T49, `BrunGoldbachPairedMainTermRefinedAtSqrt` reduces to
the **single** classical input `BrunGoldbachClassicalBound`.  No
new Mertens-style infrastructure is required; the bridge proof
combines:

* The trivial cardinal bound `goldbachSiftedPair n √n ≤ n` (Lean's
  `goldbachSiftedPair_le`).
* The positivity of `pairedBrunFactor` (Lean's
  `pairedBrunFactor_pos`).
* The non-negativity of `refinedReservoir` (Lean's
  `refinedReservoir_nonneg`).
* The closed paired-Brun lower Mertens gap
  `pairedBrunMertensThirdLowerGap_holds` (P19-T6).

The factor `K / C₀` (where `K` is the Brun-Goldbach constant and
`C₀` is the lower-Mertens constant) gives the explicit witness
for `C₁` in the asymptotic regime; a finite-range sum absorbs the
small-`n` regime.

The reservoir term `refinedReservoir n √n = n / (log n)²` is
**not used** in the bridge — the inequality already holds without
it.  This documents the "reservoir slack" observation: the
refined main-term Prop has so much additive slack that the
reservoir is *strictly more than needed*. -/
theorem pathC_p19_t49_summary : True := trivial

end PathCAtSqrtViaReservoirSlack
end Gdbh
