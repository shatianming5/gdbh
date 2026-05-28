/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P23-T1 (Phase 23 / Path C — Close `BrunGoldbachWithSingularSeries`
        via the master assembly).
-/
import Gdbh.PathC_BrunGoldbachSingularSeries
import Gdbh.PathC_HardyLittlewoodForm
import Gdbh.PathC_LocalToSingular
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_PairedBrunMertensLowerReal

/-!
# Path C — P23-T1: closing `BrunGoldbachWithSingularSeries` via the master assembly

## Mission

This file attempts to close the named Prop

```
BrunGoldbachWithSingularSeries : Prop :=
  ∃ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (goldbachSiftedPair n √n : ℝ)
      ≤ C · n · pairedBrunFactor √n · singularSeries n
```

(from `Gdbh.PathC_BrunGoldbachSingularSeries`) via composition of the
existing Path C master assembly:

1. **Master sieve input (open Prop)**:
   `BrunGoldbachLocalMainTermRefinedAtSqrt`
   (`Gdbh.PathCGoldbachLocalFactor`).  This is the natural
   Halberstam-Richert §3.11 main term decomposed via the local-density
   factor `goldbachLocalFactor n √n`:

   ```
   r(n)  ≤  C₁ · n · goldbachLocalFactor n √n  +  refinedReservoir n √n .
   ```

2. **Identity (closed)**:
   `goldbachLocalFactor n √n = pairedBrunFactor √n · truncatedGoldbachSingularMultiplier n √n`.
   This is `Gdbh.PathCGoldbachLocalFactor.goldbachLocalFactor_eq_paired_mul_singularMultiplier`.

3. **CRT-locality monotonicity (closed in this file)**:
   `truncatedGoldbachSingularMultiplier n (Nat.sqrt n) ≤ singularSeries n`.
   The truncated multiplier is a sub-product of the full singular series
   (both are over odd-prime divisors of `n`; the truncated one is
   restricted to `p ≤ √n`).  Each factor `(p-1)/(p-2) ≥ 1`, so the
   truncated product is bounded by the full product.

4. **Reservoir absorption (open Prop)**:
   `PairedBrunMertensThirdLowerGap` from
   `Gdbh.PathCPairedBrunMertensLowerReal`.  The Mertens lower bound
   `pairedBrunFactor z ≥ C / (log z)²` for `z ≥ z₀` is the matching lower
   counterpart of the (closed) upper bound.  Composed at `z = √n`, it
   gives the absorption `n / (log n)² ≤ C' · n · pairedBrunFactor √n`,
   which combined with `singularSeries n ≥ 1` yields the reservoir
   absorption needed.

The composition of (1)–(4) directly yields
`BrunGoldbachWithSingularSeries`.

## Status

The closure presented here is **conditional** on two named open Props:

* `BrunGoldbachLocalMainTermRefinedAtSqrt` (the Halberstam-Richert §3.11
  master input — open in mathlib v4.29.1, this is the "outside" CRT-counting
  task).
* `PairedBrunMertensThirdLowerGap` (the sharp paired-Mertens lower
  asymptotic — open in mathlib v4.29.1).

Both inputs are explicitly named as Prop parameters in the closure
theorem `brunGoldbachWithSingularSeries_of_master_assembly`.  The
intermediate step (3) — `truncatedGoldbachSingularMultiplier ≤ singularSeries`
— is **closed unconditionally** in this file as `truncated_le_singularSeries`.
This is the precise content of the strategy's "CRT counting with singular
series naturally emerging":  the singular series indeed *emerges* as the
asymptotic limit of the truncated CRT multiplier, and the comparison
truncated ≤ full holds at finite stage.

## Strict constraints (P23-T1 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* The file **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCBrunGoldbachSingularClosure

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCHardyLittlewoodForm
  (singularSeries singularSeries_def singularSeries_pos one_le_singularSeries)
open Gdbh.PathCGoldbachLocalFactor
  (goldbachLocalFactor goldbachLocalFactor_eq_paired_mul_singularMultiplier
   truncatedGoldbachSingularMultiplier
   goldbachLocalFactor_pos
   BrunGoldbachLocalMainTermRefinedAtSqrt)
open Gdbh.PathCLocalToSingular
  (one_le_truncatedGoldbachSingularMultiplier)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunMertensLowerReal (PairedBrunMertensThirdLowerGap)
open Gdbh.PathCBrunGoldbachSingularSeries
  (BrunGoldbachWithSingularSeries SingularSeriesMertens3Bound
   classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries
   brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_brunGoldbachWithSingularSeries)
open Gdbh.PathCFixAStrongClosure (ClassicalBrunGoldbachLogLog)
open Gdbh.PathCFixAStrongReservoir (BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)

/-! ## Section 1 — CRT counting with singular series naturally emerging

The truncated Goldbach singular multiplier at sieve threshold `z = √n`
is bounded above by the full Hardy-Littlewood singular series:

```
truncatedGoldbachSingularMultiplier n √n  ≤  singularSeries n .
```

This is the **finite-stage shadow** of the CRT counting:  the sieve at
threshold `z = √n` only sees primes `p ≤ √n` dividing `n`, but the full
singular series sees *all* primes `p ≤ n` dividing `n`.  Since each
factor `(p-1)/(p-2) ≥ 1`, the truncated product is bounded by the full
product.

This closes the "CRT locality" sub-Prop of Strategy A from
`PathC_BrunGoldbachSingularSeries`. -/

/-- **The factor identification.**  For `p ≥ 3` a prime, the local
CRT-locality factor `1 + 1/(p-2)` equals the singular-series factor
`(p-1)/(p-2)`.  Both are `≥ 1` and positive. -/
private lemma factor_id_eq {p : ℕ} (hp : 3 ≤ p) :
    (1 + 1 / ((p : ℝ) - 2)) = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  field_simp
  ring

/-- Each "CRT-locality" factor `(if p ∣ n then (1 + 1/(p-2)) else 1)`
equals the "singular-series" factor `(if p ∣ n then (p-1)/(p-2) else 1)`
for `p ≥ 3`. -/
private lemma local_factor_eq_singular_factor {n p : ℕ} (hp : 3 ≤ p) :
    (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1)
      = (if p ∣ n then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, if_pos hpn, factor_id_eq hp]
  · simp [hpn]

/-- The truncated Goldbach singular multiplier at sieve level `z`, after
the factor identification, equals the partial singular-series product
over primes in `[3, z]` dividing `n`. -/
private lemma truncated_eq_partial_singular (n z : ℕ) :
    truncatedGoldbachSingularMultiplier n z
      = ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          (if p ∣ n then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_congr rfl ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  exact local_factor_eq_singular_factor (n := n) hp3

/-- The truncated Goldbach singular multiplier admits an equivalent form
as a product *only over divisors* of `n` in `[3, z]`. -/
private lemma truncated_eq_div_prod (n z : ℕ) :
    truncatedGoldbachSingularMultiplier n z
      = ∏ p ∈ ((Finset.Icc 3 z).filter Nat.Prime).filter (fun p => p ∣ n),
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  classical
  rw [truncated_eq_partial_singular n z]
  -- Collapse the `if`:  factors with `¬ (p ∣ n)` contribute 1.
  rw [← Finset.prod_filter]

/-- The Hardy-Littlewood singular series admits an equivalent form as a
product over primes in `[3, n]` filtered to those dividing `n`, with the
extra `prime` filter folded into the outer `filter` (re-expressing the
ambient definition). -/
private lemma singularSeries_eq_div_prod (n : ℕ) :
    singularSeries n
      = ∏ p ∈ ((Finset.Icc 3 n).filter Nat.Prime).filter (fun p => p ∣ n),
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  classical
  rw [singularSeries_def]
  -- The original filter is over `fun p => Nat.Prime p ∧ p ∣ n`.
  -- Decompose as a double filter:  first by `Nat.Prime`, then by `p ∣ n`.
  rw [show ((Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n))
        = ((Finset.Icc 3 n).filter Nat.Prime).filter (fun p => p ∣ n) by
        ext p
        simp [and_assoc]]

/-- **CRT-locality monotonicity (closed).**  The truncated multiplier at
sieve level `z ≤ n` is bounded by the full singular series:

```
truncatedGoldbachSingularMultiplier n z  ≤  singularSeries n .
```

**Proof.**  After identification, both are products of factors
`(p-1)/(p-2) ≥ 1` over primes in respective intervals dividing `n`.  The
truncated one is restricted to `p ≤ z ≤ n`, hence is a sub-product of
the full one.  Sub-products of factors `≥ 1` are bounded by the full
product. -/
theorem truncated_le_singularSeries (n z : ℕ) (hz : z ≤ n) :
    truncatedGoldbachSingularMultiplier n z ≤ singularSeries n := by
  classical
  rw [truncated_eq_div_prod n z, singularSeries_eq_div_prod n]
  -- Now both are products of `(p-1)/(p-2)` over filtered sets;  the
  -- truncated index set is a subset of the full one.
  refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    refine ⟨⟨⟨hp.1.1.1, le_trans hp.1.1.2 hz⟩, hp.1.2⟩, hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp3 : 3 ≤ p := hp.1.1.1
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hnum_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact le_of_lt (div_pos hnum_pos hden_pos)
  · intro p hp _hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp3 : 3 ≤ p := hp.1.1.1
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hnum_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden_le_num : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
    exact (one_le_div hden_pos).mpr hden_le_num

/-- The Goldbach local factor is bounded by the paired Brun factor
times the full singular series:

```
goldbachLocalFactor n √n  ≤  pairedBrunFactor √n · singularSeries n .
```

This packages the CRT-locality identification (Section 1) with the
factorisation
`goldbachLocalFactor n z = pairedBrunFactor z · truncatedGoldbachSingularMultiplier n z`. -/
theorem goldbachLocalFactor_le_paired_mul_singularSeries (n : ℕ) :
    goldbachLocalFactor n (Nat.sqrt n)
      ≤ pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
  rw [goldbachLocalFactor_eq_paired_mul_singularMultiplier]
  have h_pbf_nn : (0 : ℝ) ≤ pairedBrunFactor (Nat.sqrt n) :=
    le_of_lt (pairedBrunFactor_pos _)
  have h_trunc_le_sing :
      truncatedGoldbachSingularMultiplier n (Nat.sqrt n) ≤ singularSeries n :=
    truncated_le_singularSeries n (Nat.sqrt n) (Nat.sqrt_le_self n)
  exact mul_le_mul_of_nonneg_left h_trunc_le_sing h_pbf_nn

/-! ## Section 2 — Reservoir absorption sub-Prop

The reservoir `refinedReservoir n √n = n / (log n)²` is the
Brun-Bonferroni truncation error.  It must be absorbed into the main
term `n · pairedBrunFactor √n · singularSeries n` to land in the
`BrunGoldbachWithSingularSeries` shape.

The required absorption is

```
n / (log n)²  ≤  K · n · pairedBrunFactor √n · singularSeries n
```

for `n ≥ N₀`, with a fixed `K > 0`.  Since `singularSeries n ≥ 1` and
`pairedBrunFactor √n ≥ C₀ / (log n)²` (by the
`PairedBrunMertensThirdLowerGap` Mertens lower bound), the required
absorption holds with `K = 1 / C₀`. -/

/-- **`ReservoirAbsorbedBySingular`.**  The reservoir absorption Prop:

```
∃ K > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  refinedReservoir n (Nat.sqrt n)
    ≤ K · n · pairedBrunFactor √n · singularSeries n .
```

This Prop is **closable** from `PairedBrunMertensThirdLowerGap` (the
named open Mertens lower bound), combined with `singularSeries ≥ 1`. -/
def ReservoirAbsorbedBySingular : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧
    ∀ n : ℕ, N₀ ≤ n →
      refinedReservoir n (Nat.sqrt n)
        ≤ K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n

/-- **Reservoir absorption from the Mertens lower bound.**  Given the
`PairedBrunMertensThirdLowerGap` Mertens lower bound, the reservoir is
absorbed into the natural main-term shape.

**Proof sketch.**  From `pairedBrunFactor z ≥ C / (log z)²` at
`z = √n` for `n ≥ z₀² + 1` (roughly), and `log √n = (log n)/2` so
`(log √n)² = (log n)²/4`, we obtain
`pairedBrunFactor √n ≥ 4C / (log n)²`.
Combined with `singularSeries n ≥ 1`, this gives
`n · pairedBrunFactor √n · singularSeries n ≥ (4C) · n / (log n)²
                                          = (4C) · refinedReservoir n √n`,
so the reservoir is absorbed with `K = 1 / (4C)`. -/
theorem reservoirAbsorbedBySingular_of_lowerGap
    (hLower : PairedBrunMertensThirdLowerGap) :
    ReservoirAbsorbedBySingular := by
  -- Extract the Mertens lower bound:  `C / (log z)² ≤ pairedBrunFactor z` for `z ≥ z₀`.
  obtain ⟨C, z₀, hC_pos, hLower_bd⟩ := hLower
  -- We need `Nat.sqrt n ≥ z₀`.  This holds when `n ≥ z₀²` (i.e.
  -- `(z₀ + 1)²` to avoid edge cases).  We also need `n ≥ 2` so that
  -- `log n > 0`, and `Nat.sqrt n ≥ 2` so that `log (Nat.sqrt n) > 0`.
  refine ⟨1 / C, max ((z₀ + 1)^2) 4, by positivity, ?_⟩
  intro n hn
  -- Unpack thresholds.
  have hn_sq : (z₀ + 1)^2 ≤ n := le_trans (le_max_left _ _) hn
  have hn_four : 4 ≤ n := le_trans (le_max_right _ _) hn
  -- `Nat.sqrt n ≥ z₀ + 1 > z₀`.
  have h_sqrt_ge_z0_succ : z₀ + 1 ≤ Nat.sqrt n := by
    refine Nat.le_sqrt.mpr ?_
    have h_sq_eq : (z₀ + 1) * (z₀ + 1) = (z₀ + 1)^2 := by ring
    rw [h_sq_eq]
    exact hn_sq
  have h_sqrt_ge_z0 : z₀ ≤ Nat.sqrt n := by omega
  have h_sqrt_ge_two : 2 ≤ Nat.sqrt n := by
    refine Nat.le_sqrt.mpr ?_
    have : (2 : ℕ) * 2 ≤ 4 := by norm_num
    exact this.trans hn_four
  -- Apply the Mertens lower bound at `z = √n`.
  have h_lower : C / (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2
                  ≤ pairedBrunFactor (Nat.sqrt n) :=
    hLower_bd (Nat.sqrt n) h_sqrt_ge_z0
  -- `log √n > 0` since `√n ≥ 2`.
  have h_sqrt_real_ge_two : (2 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast h_sqrt_ge_two
  have h_sqrt_gt_one : (1 : ℝ) < (Nat.sqrt n : ℝ) := by linarith
  have h_log_sqrt_pos : 0 < Real.log (Nat.sqrt n : ℝ) := Real.log_pos h_sqrt_gt_one
  have h_log_sqrt_sq_pos : 0 < (Real.log (Nat.sqrt n : ℝ))^2 := by positivity
  -- `log n > 0` too.
  have h_n_ge_two : 2 ≤ n := by omega
  have h_n_real_ge_two : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_n_ge_two
  have h_n_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
  have h_log_n_pos : 0 < Real.log (n : ℝ) := Real.log_pos h_n_gt_one
  have h_log_n_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  -- `Nat.sqrt n ≤ n`, so `log √n ≤ log n`, so `(log √n)² ≤ (log n)²`.
  have h_sqrt_le_n : (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le_self n
  have h_log_sqrt_le_log_n : Real.log (Nat.sqrt n : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log
    · linarith
    · exact h_sqrt_le_n
  have h_log_sqrt_nn : 0 ≤ Real.log (Nat.sqrt n : ℝ) := le_of_lt h_log_sqrt_pos
  have h_log_sq_mono :
      (Real.log (Nat.sqrt n : ℝ))^2 ≤ (Real.log (n : ℝ))^2 := by
    nlinarith [h_log_sqrt_le_log_n, h_log_sqrt_nn]
  -- Combine:  `C / (log n)² ≤ C / (log √n)² ≤ pairedBrunFactor √n`.
  have h_div_mono :
      C / (Real.log (n : ℝ))^2 ≤ C / (Real.log (Nat.sqrt n : ℝ))^2 := by
    apply div_le_div_of_nonneg_left (le_of_lt hC_pos) h_log_sqrt_sq_pos h_log_sq_mono
  have h_pbf_lower_log_n :
      C / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor (Nat.sqrt n) :=
    le_trans h_div_mono h_lower
  -- Multiply by `n`:  `C · n / (log n)² ≤ n · pairedBrunFactor √n`.
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_step1 :
      (n : ℝ) * (C / (Real.log (n : ℝ))^2)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
    exact mul_le_mul_of_nonneg_left h_pbf_lower_log_n h_n_nn
  -- Multiply by `singularSeries n ≥ 1`:
  have h_sing_one : (1 : ℝ) ≤ singularSeries n := one_le_singularSeries n
  have h_sing_nn : (0 : ℝ) ≤ singularSeries n := by linarith
  have h_pbf_n_nn :
      (0 : ℝ) ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
    mul_nonneg h_n_nn (le_of_lt (pairedBrunFactor_pos _))
  have h_step2 :
      (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
    have := le_mul_of_one_le_right h_pbf_n_nn h_sing_one
    linarith
  -- Combine:  `n · (C / (log n)²) ≤ n · pairedBrunFactor √n · singularSeries n`.
  have h_combined :
      (n : ℝ) * (C / (Real.log (n : ℝ))^2)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n :=
    le_trans h_step1 h_step2
  -- Convert to the reservoir form.  `refinedReservoir n √n = n / (log n)²`.
  rw [refinedReservoir_def]
  -- Goal:  `n / (log n)² ≤ (1/C) · n · pairedBrunFactor √n · singularSeries n`.
  -- From h_combined:  `n · C / (log n)² ≤ n · pairedBrunFactor √n · singularSeries n`.
  -- Divide both sides by C > 0:  `n / (log n)² ≤ (1/C) · n · pairedBrunFactor √n · singularSeries n`.
  have h_LHS_eq : (n : ℝ) * (C / (Real.log (n : ℝ))^2)
                    = C * ((n : ℝ) / (Real.log (n : ℝ))^2) := by ring
  rw [h_LHS_eq] at h_combined
  -- h_combined : C * (n / (log n)²) ≤ n · pairedBrunFactor √n · singularSeries n
  have h_div : (n : ℝ) / (Real.log (n : ℝ))^2
                  ≤ (1 / C) * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n) := by
    rw [div_mul_eq_mul_div, one_mul]
    rw [le_div_iff₀ hC_pos]
    linarith
  -- Match the goal's associativity:
  have h_goal_eq :
      (1 / C) * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n)
        = 1 / C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
    ring
  linarith [h_div, h_goal_eq.symm.le, h_goal_eq.le]

/-! ## Section 3 — The master closure

Given:

* `BrunGoldbachLocalMainTermRefinedAtSqrt` (open Prop: the
  Halberstam-Richert §3.11 master sieve input, in local-factor form),
* `ReservoirAbsorbedBySingular` (closable from `PairedBrunMertensThirdLowerGap`),

we derive `BrunGoldbachWithSingularSeries`.

The proof composes:

```
r(n) ≤ C₁ · n · goldbachLocalFactor n √n + reservoir          (hMain)
     ≤ C₁ · n · pairedBrunFactor √n · singularSeries n + reservoir
                                  (goldbachLocalFactor_le_paired_mul_singularSeries)
     ≤ C₁ · n · pairedBrunFactor √n · singularSeries n
       + K · n · pairedBrunFactor √n · singularSeries n              (hAbs)
     = (C₁ + K) · n · pairedBrunFactor √n · singularSeries n .
``` -/

/-- **Master closure of `BrunGoldbachWithSingularSeries`.**

Given the two named master inputs:

* `BrunGoldbachLocalMainTermRefinedAtSqrt` (the local-factor §3.11 main
  term — open in mathlib v4.29.1),
* `ReservoirAbsorbedBySingular` (the reservoir absorption — closable
  from `PairedBrunMertensThirdLowerGap`),

we derive `BrunGoldbachWithSingularSeries`. -/
theorem brunGoldbachWithSingularSeries_of_master_assembly
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hAbs : ReservoirAbsorbedBySingular) :
    BrunGoldbachWithSingularSeries := by
  obtain ⟨C₁, N_main, hC₁_pos, hMain_bd⟩ := hMain
  obtain ⟨K, N_abs, hK_pos, hAbs_bd⟩ := hAbs
  refine ⟨C₁ + K, max (max N_main N_abs) 3, by linarith, ?_⟩
  intro n hn
  have hn_main : N_main ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_abs : N_abs ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_three : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn_two : 2 ≤ n := by omega
  -- Apply the master local main-term bound.
  have h1 : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
              ≤ C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
                + refinedReservoir n (Nat.sqrt n) :=
    hMain_bd n hn_main hn_two
  -- Local-factor ≤ paired · singular.
  have h_localFactor_le :
      goldbachLocalFactor n (Nat.sqrt n)
        ≤ pairedBrunFactor (Nat.sqrt n) * singularSeries n :=
    goldbachLocalFactor_le_paired_mul_singularSeries n
  have h_C₁_n_nn : (0 : ℝ) ≤ C₁ * (n : ℝ) := by
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg (le_of_lt hC₁_pos) h_n_nn
  have h2 : C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
              ≤ C₁ * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * singularSeries n) :=
    mul_le_mul_of_nonneg_left h_localFactor_le h_C₁_n_nn
  -- Reservoir absorption.
  have h3 : refinedReservoir n (Nat.sqrt n)
              ≤ K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n :=
    hAbs_bd n hn_abs
  -- Combine.
  have h_C₁_form :
      C₁ * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * singularSeries n)
        = C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
    ring
  have h_sum_form :
      C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
        + K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
        = (C₁ + K) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
    ring
  calc (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n) := h1
    _ ≤ C₁ * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * singularSeries n)
          + refinedReservoir n (Nat.sqrt n) := by linarith
    _ = C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
          + refinedReservoir n (Nat.sqrt n) := by rw [h_C₁_form]
    _ ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
          + K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by linarith
    _ = (C₁ + K) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n :=
        h_sum_form

/-- **Master closure via the explicit Mertens lower gap.**  The
two-input closure, with the reservoir-absorption sub-Prop already
expanded via `reservoirAbsorbedBySingular_of_lowerGap`. -/
theorem brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hLower : PairedBrunMertensThirdLowerGap) :
    BrunGoldbachWithSingularSeries :=
  brunGoldbachWithSingularSeries_of_master_assembly hMain
    (reservoirAbsorbedBySingular_of_lowerGap hLower)

/-! ## Section 4 — Documentation:  what is genuinely needed

The closure `brunGoldbachWithSingularSeries_of_master_assembly`
depends on **two** named open Props (both standard classical inputs,
both open in mathlib v4.29.1):

1. **`BrunGoldbachLocalMainTermRefinedAtSqrt`** — the
   Halberstam-Richert §3.11 master sieve input, in local-density form.
   This is the genuine open content:  it requires the full
   Brun-Bonferroni / CRT-counting machinery at sieve level `z = √n`,
   with the local-density factor `goldbachLocalFactor n √n` (containing
   the truncated singular multiplier) on the main term, and the
   `n / (log n)²` reservoir on the error.

2. **`PairedBrunMertensThirdLowerGap`** — the matching lower bound to
   the (closed) paired-Brun Mertens upper bound:
   `pairedBrunFactor z ≥ C / (log z)²` for `z ≥ z₀`.  This is the sharp
   paired-Mertens asymptotic, which the project already separately
   addresses in `Gdbh/PathC_PairedBrunMertensLowerReal.lean`.

The **CRT counting with singular series naturally emerging** — the
strategy's headline content — is closed unconditionally in this file as
`truncated_le_singularSeries`:  the truncated multiplier (the
"CRT-locality" factor that the sieve actually sees at level `√n`) is
bounded by the full singular series (which is the asymptotic limit).
The singular series indeed *emerges* from CRT counting at finite sieve
threshold.

The **reservoir absorption** is closed in this file from
`PairedBrunMertensThirdLowerGap` as
`reservoirAbsorbedBySingular_of_lowerGap`.

Hence the residual content of the closure reduces to **only**
`BrunGoldbachLocalMainTermRefinedAtSqrt` and
`PairedBrunMertensThirdLowerGap` — both of which are *named* open Props
in the project, both of which represent classical results in mathlib's
"open mathematical content" gap, and neither of which requires the
construction of new Props in this file. -/

/-! ## Section 5 — Composed bridge to the LogLog form and FixA'

For convenience, we expose the composed bridge:

```
BrunGoldbachLocalMainTermRefinedAtSqrt
  + PairedBrunMertensThirdLowerGap
  + SingularSeriesMertens3Bound
  ⇒ ClassicalBrunGoldbachLogLog .
```

This composes our `BrunGoldbachWithSingularSeries`-closure with the
existing Bridge A
(`classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries` from
`PathC_BrunGoldbachSingularSeries`), giving a full closure path of the
LogLog form from named master inputs. -/

/-- **Composed bridge to LogLog form.**  From the three master inputs,
land on `ClassicalBrunGoldbachLogLog`. -/
theorem classicalBrunGoldbachLogLog_of_master_assembly
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hLower : PairedBrunMertensThirdLowerGap)
    (hMertens3 : SingularSeriesMertens3Bound) :
    ClassicalBrunGoldbachLogLog :=
  classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries
    (brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap hMain hLower)
    hMertens3

/-- **Composed bridge to FixA' AtSqrt Prop.**  From the three master
inputs, land on the FixA' Prop. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hLower : PairedBrunMertensThirdLowerGap)
    (hMertens3 : SingularSeriesMertens3Bound) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong :=
  brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_brunGoldbachWithSingularSeries
    (brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap hMain hLower)
    hMertens3

/-! ## Section 6 — Headline summary

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. **`truncated_le_singularSeries`** — the closed comparison
   `truncatedGoldbachSingularMultiplier n √n ≤ singularSeries n`,
   i.e. the *CRT counting with singular series naturally emerging*
   content from the strategy.

2. **`goldbachLocalFactor_le_paired_mul_singularSeries`** — the closed
   inequality `goldbachLocalFactor n √n ≤ pairedBrunFactor √n · singularSeries n`,
   packaging (1) with the local-factor decomposition.

3. **`ReservoirAbsorbedBySingular`** — the named sub-Prop encoding
   reservoir absorption into the natural §3.11 main-term shape.

4. **`reservoirAbsorbedBySingular_of_lowerGap`** — closes (3) from
   `PairedBrunMertensThirdLowerGap`.

5. **`brunGoldbachWithSingularSeries_of_master_assembly`** — the
   master closure theorem:  from `BrunGoldbachLocalMainTermRefinedAtSqrt`
   and `ReservoirAbsorbedBySingular`, derive
   `BrunGoldbachWithSingularSeries`.

6. **`brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap`**
   — the cleaner variant, with the reservoir-absorption sub-Prop
   expanded into the Mertens lower gap.

7. **`classicalBrunGoldbachLogLog_of_master_assembly`** and
   **`brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly`**
   — composed bridges to the LogLog form and FixA' Prop.

The remaining open mathlib gaps are exactly:

* `BrunGoldbachLocalMainTermRefinedAtSqrt` — the open Halberstam-Richert
  §3.11 master sieve input.
* `PairedBrunMertensThirdLowerGap` — the open paired-Mertens lower bound.
* `SingularSeriesMertens3Bound` — the open Mertens-3 upper bound on
  the singular series (only needed for the LogLog/FixA' composition).

All three are classical and addressed elsewhere in the project at the
Prop-axiom level. -/

/-! ## Section 7 — Axiom audit -/

#print axioms truncated_le_singularSeries
#print axioms goldbachLocalFactor_le_paired_mul_singularSeries
#print axioms reservoirAbsorbedBySingular_of_lowerGap
#print axioms brunGoldbachWithSingularSeries_of_master_assembly
#print axioms brunGoldbachWithSingularSeries_of_master_assembly_via_lowerGap
#print axioms classicalBrunGoldbachLogLog_of_master_assembly
#print axioms brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_master_assembly

end PathCBrunGoldbachSingularClosure
end Gdbh
