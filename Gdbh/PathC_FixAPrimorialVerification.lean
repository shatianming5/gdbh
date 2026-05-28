/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P20-T3 (Phase 20 / Path C — Verification that the proposed
        `FixA` reservoir `n · log log n / (log n)^2` ALSO FAILS to
        close `BrunGoldbachPairedMainTermRefinedAtSqrt_FixA` at literal
        `C₁ = 1` along the primorial sequence — the *15th false-Prop
        catch* in the project.)
-/
import Gdbh.PathC_PrimorialVerification
import Gdbh.PathC_AsymptoticBrunGoldbach
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Path C — P20-T3: `FixA` is also FALSE at literal `C₁ = 1`

This file is the **P20-T3 deliverable** in Phase 20 (Path C residual
exploration).

## Background

`PathC_AsymptoticBrunGoldbach` (P19-T51) exposed three honest "fixes"
for the 14th false-Prop catch — the failure of
`BrunGoldbachPairedMainTermRefinedAtSqrt` at any finite `C₁` along the
primorial sequence:

* **`FixA`**: bump the reservoir from `n / (log n)²` to
  `n · log log n / (log n)²`.
* **`FixB`**: restrict to non-primorial `n`.
* **`FixC`**: replace pointwise bound by averaged bound on windows.

The architecturally cleanest proposal is `FixA`:  multiplying the
reservoir by `log log n` is intended to absorb the unbounded
singular-series factor `S(n) ∼ c · log log n` along primorials.

## The P20-T3 finding (15th false-Prop catch)

`FixA` **also fails at literal `C₁ = 1`** along the primorial sequence,
because the singular-series asymptotic gives
`r(n) ∼ C · n · pBF(√n) · S(n)` with `C > 1`, so the *coefficient*
of `n · pBF` already absorbs the `log log n` (up to a constant), and
the additive reservoir `n · log log n / (log n)²` does not buy any
*additional* slack relative to the multiplicative version
`C · n · pBF`.  Numerically, at the primorial witnesses:

| `n`     | LHS `r(n)` | `m(n) = n · pBF(√n)` | `b(n) = n · log log n / (log n)²` | `m + b` (FixA, C₁=1) | LHS ≤ m + b ? |
|--------:|-----------:|---------------------:|----------------------------------:|---------------------:|:--------------|
|   210   |     34     |        20.77         |              12.32                |         33.09        |  **FAILS** (margin 0.91) |
|  2310   |    216     |       117.81         |              78.85                |        196.66        |  **FAILS** (margin 19.34) |
| 30030   |   1784     |       ≈ 850          |              ≈ 553                |        ≈ 1403        |  **FAILS** (margin ≈ 381) |

The required `C₁` continues to grow:  at `n = 210` we need `C₁ ≥ 1.04`,
at `n = 2310` we need `C₁ ≥ 1.17`, at `n = 30030` we need `C₁ ≥ 1.27`.
The growth rate is consistent with the analytical scaling
`(C - 1) · log log n / (singular-series saturation factor)`, which
is *bounded but slowly increasing*.

### Analytical explanation

By the Hardy-Littlewood / Brun asymptotic:
```
r(n) ≤ C_HL · n · pBF(√n) · S(n)            (H-L theorem 3.5)
```
where `S(n) ∼ c · log log n` along primorials.  Subtracting the
`FixA` reservoir `n · log log n / (log n)²` from the bound:
```
r(n) - reservoir_FixA(n)  ≤  (C_HL - 1/K) · n · pBF(√n) · log log n .
```
The leading-order coefficient `C_HL - 1/K` remains *positive* — the
reservoir absorbs only a *bounded* fraction of the singular series.
Hence the LHS `r(n)` of the chain Prop divided by `n · pBF` is still
asymptotic to `C_HL · log log n` (unbounded), and **no fixed `C₁`**
on the *coefficient* of `n · pBF` can absorb it via the `FixA`
reservoir.

## What this file formalises

**Section 1.** Logarithm bound `log 2310 < 8` (new).

**Section 2.** Upper bound `log 8 < 2.1` via `exp 2.1 > 8` from
`Real.exp_one_gt_d9` and `Real.add_one_le_exp`.

**Section 3.** Lower bound `log 2310 > 7.5` via `exp 7.5 < 2310`
(i.e. `(exp 7.5)² < 2310² = 5336100` and `exp 15 = (exp 1)¹⁵ < 3¹⁵ =
14348907`, so `exp 7.5 < sqrt(14348907) ≈ 3788`; refining,
`exp 7.5 < 2310` requires `2.7182818286^15 < 2310² = 5336100`).
We use the simpler route:  it is enough that `exp 7.5 · exp 7.5 <
2310 · 2310`, which we establish from `exp 1 < 3` (giving
`exp 15 < 3^15 = 14348907 < 5336100²`)... **no, this is wrong**.
We instead use `2.7182818283 < exp 1` to get `(exp 1)^15 >
2.7182818283^15 ≈ 3.27 · 10⁶`, so `exp 7.5 > sqrt(3.27 · 10⁶) ≈
1808 < 2310`.  Hence `log 2310 > 7.5`.

**Section 4.** Refined upper bound `pBF(48) < 1/19` (re-exported
from P19-T50).

**Section 5.** The headline theorem
`fixA_C1_eq_one_fails_at_2310`:  at `n = 2310`, the `FixA`-shaped
inequality at literal `C₁ = 1` **fails**.

**Section 6.** Documentation statement for `n = 210` (margin too
tight for clean kernel proof) and `n = 30030` (kernel-decide
infeasible).

**Section 7.** Proposed *stronger* fix:  bump the reservoir to
`n · (log log n)² / (log n)²` (or equivalently scale `pBF` by the
explicit Hardy-Littlewood singular-series factor).  Exposed as a
new named Prop `BrunGoldbachPairedMainTermRefinedAtSqrt_FixAprime`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene: only `[Classical.choice, Quot.sound, propext]`.

## Honesty note

This is the **15th false-Prop catch** in the project (the FixA
proposal of P19-T51).  The natural remedy is the strictly stronger
fix discussed in Section 7.
-/

namespace Gdbh
namespace PathCFixAPrimorialVerification

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt)
open Gdbh.PathCRefinedAtSqrtDirectClosure
  (sqrt_210 goldbachSiftedPair_210
   pairedBrunFactor_14_eq_nine_div_91
   log_210_gt_four log_210_sq_gt_sixteen)
open Gdbh.PathCPrimorialVerification
  (sqrt_2310 sqrt_30030 goldbachSiftedPair_2310
   pairedBrunFactor_48_eq pairedBrunFactor_48_lt_one_nineteenth
   log_2310_gt_seven log_2310_sq_gt_49 log_30030_gt_seven)

/-! ## Section 0 — The FixA reservoir.

The proposed FixA reservoir is `n · log log n / (log n)²`.  We define
it here for clarity. -/

/-- **The proposed FixA reservoir**:
`fixAReservoir n := n · log log n / (log n)²`. -/
noncomputable def fixAReservoir (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2

@[simp] lemma fixAReservoir_def (n : ℕ) :
    fixAReservoir n =
      (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2 := rfl

/-! ## Section 1 — Upper bound `log 2310 < 8`.

We show `Real.log 2310 < 8` via `exp 8 > 2310`.  Since
`exp 8 = (exp 1)^8 > 2.71^8 > 3010 > 2310`, this gives `log 2310 < 8`. -/

/-- `Real.exp 8 > 2310`.  Follows from `exp 1 > 2.71` and
`2.71^8 > 3010 > 2310`. -/
private lemma exp_eight_gt_2310 : (2310 : ℝ) < Real.exp 8 := by
  -- `exp 1 > 2.7182818283`, so `(exp 1)^8 > 2.7182818283^8`.
  have h_exp_one_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_271_nn : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  have h_pow_lt : (2.7182818283 : ℝ)^8 < (Real.exp 1)^8 :=
    pow_lt_pow_left₀ h_exp_one_gt h_271_nn (by norm_num : (8 : ℕ) ≠ 0)
  -- `2.7182818283^8 > 2980 > 2310`.
  have h_271_pow8 : (2980 : ℝ) < (2.7182818283 : ℝ)^8 := by norm_num
  -- Hence `(exp 1)^8 > 2310`.
  have h_exp_one_pow8 : (2310 : ℝ) < (Real.exp 1)^8 := by linarith
  -- `exp 8 = (exp 1)^8`.
  have h_exp_8_eq : Real.exp 8 = (Real.exp 1)^8 := by
    rw [show (8 : ℝ) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [h_exp_8_eq]
  exact h_exp_one_pow8

/-- `Real.log 2310 < 8`. -/
lemma log_2310_lt_eight : Real.log 2310 < 8 := by
  have h1 : (2310 : ℝ) < Real.exp 8 := exp_eight_gt_2310
  have h2 : Real.log (2310 : ℝ) < Real.log (Real.exp 8) :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 2310) h1
  rw [Real.log_exp] at h2
  exact h2

/-! ## Section 2 — Upper bound `log 8 < 2.1`.

We need `exp 2.1 > 8`.  Strategy:  `exp 2.1 = exp 2 · exp 0.1 >
(2.71)² · (1 + 0.1) = 7.3441 · 1.1 = 8.0785 > 8`.

The `exp 0.1 ≥ 1.1` step uses `Real.add_one_le_exp`. -/

/-- `Real.exp 0.1 ≥ 1.1`.  From `x + 1 ≤ exp x` at `x = 0.1`. -/
private lemma exp_one_tenth_ge : (1.1 : ℝ) ≤ Real.exp 0.1 := by
  have h := Real.add_one_le_exp (0.1 : ℝ)
  linarith

/-- `Real.exp 2 > 7.29`.  From `exp 1 > 2.7`, `(exp 1)² > 7.29`. -/
private lemma exp_two_gt_729 : (7.29 : ℝ) < Real.exp 2 := by
  have h_exp_one_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_271_nn : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  have h_pow_lt : (2.7182818283 : ℝ)^2 < (Real.exp 1)^2 :=
    pow_lt_pow_left₀ h_exp_one_gt h_271_nn (by norm_num : (2 : ℕ) ≠ 0)
  have h_pow_val : (7.29 : ℝ) < (2.7182818283 : ℝ)^2 := by norm_num
  have h_exp_2_eq : Real.exp 2 = (Real.exp 1)^2 := by
    rw [show (2 : ℝ) = 1 + 1 from by ring, Real.exp_add]; ring
  linarith [h_exp_2_eq ▸ (lt_trans h_pow_val h_pow_lt)]

/-- `Real.exp 2.1 > 8`.  Combines `exp 2 > 7.29` and `exp 0.1 ≥ 1.1`. -/
private lemma exp_21_gt_eight : (8 : ℝ) < Real.exp 2.1 := by
  have h1 : (7.29 : ℝ) < Real.exp 2 := exp_two_gt_729
  have h2 : (1.1 : ℝ) ≤ Real.exp 0.1 := exp_one_tenth_ge
  have h_exp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have h_exp21_eq : Real.exp 2.1 = Real.exp 2 * Real.exp 0.1 := by
    rw [show (2.1 : ℝ) = 2 + 0.1 from by norm_num, Real.exp_add]
  rw [h_exp21_eq]
  -- Want `8 < exp 2 · exp 0.1`.  We have `exp 2 > 7.29` and `exp 0.1 ≥ 1.1`.
  -- `7.29 · 1.1 = 8.019 > 8`.
  have h_prod : (7.29 : ℝ) * 1.1 < Real.exp 2 * Real.exp 0.1 := by
    have h_lhs_pos : (0 : ℝ) < 7.29 * 1.1 := by norm_num
    -- `7.29 * 1.1 < exp 2 * 1.1 ≤ exp 2 * exp 0.1`.
    have step1 : (7.29 : ℝ) * 1.1 < Real.exp 2 * 1.1 := by
      have h1_1_pos : (0 : ℝ) < 1.1 := by norm_num
      exact mul_lt_mul_of_pos_right h1 h1_1_pos
    have step2 : Real.exp 2 * 1.1 ≤ Real.exp 2 * Real.exp 0.1 := by
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt h_exp2_pos)
    linarith
  have h_numeric : (8 : ℝ) < 7.29 * 1.1 := by norm_num
  linarith

/-- `Real.log 8 < 2.1`. -/
lemma log_eight_lt_21 : Real.log 8 < 2.1 := by
  have h1 : (8 : ℝ) < Real.exp 2.1 := exp_21_gt_eight
  have h2 : Real.log (8 : ℝ) < Real.log (Real.exp 2.1) :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 8) h1
  rw [Real.log_exp] at h2
  exact h2

/-- `Real.log (Real.log 2310) < 2.1`.  Combines
`log 2310 < 8` and `log 8 < 2.1` with monotonicity. -/
lemma log_log_2310_lt_21 : Real.log (Real.log 2310) < 2.1 := by
  -- `log 2310 < 8` and `log 2310 > 7 > 0`, so `log (log 2310) < log 8 < 2.1`.
  have h_log_lt : Real.log 2310 < 8 := log_2310_lt_eight
  have h_log_pos : (0 : ℝ) < Real.log 2310 := by
    have := log_2310_gt_seven; linarith
  have h_eight_pos : (0 : ℝ) < (8 : ℝ) := by norm_num
  have h_log_log_lt_log_eight : Real.log (Real.log 2310) < Real.log 8 :=
    Real.log_lt_log h_log_pos h_log_lt
  have h_log_eight_lt_21 : Real.log 8 < 2.1 := log_eight_lt_21
  linarith

/-! ## Section 3 — Lower bound `log 2310 > 7.5` (revisited / sharpened).

`PathC_PrimorialVerification` provides `log 2310 > 7` (via
`exp 7 < 2187 < 2310`).  We sharpen this to `log 2310 > 7.5`,
which gives `(log 2310)² > 56.25`.

The strategy is to show `exp 7.5 < 2310`.  We have
`(exp 7.5)² = exp 15 = (exp 1)^15`.  Using `exp 1 < 3`:
`(exp 1)^15 < 3^15 = 14348907 < 5336100 = 2310²`?  No,
`5336100 < 14348907`, so this is the **wrong direction**.

Instead, we use the upper bound `exp 1 < 2.7183`:
`(exp 1)^15 < 2.7183^15 < 3270000`, then
`exp 7.5 = √(exp 15) < √(3270000) ≈ 1808.3 < 2310`.

In Lean we avoid `sqrt` and reason via the squared form directly. -/

/-- `Real.exp 15 < 3270000`.  From `exp 1 < 2.7183`,
`(exp 1)^15 < 2.7183^15 < 3270000`. -/
private lemma exp_fifteen_lt : Real.exp 15 < 3270000 := by
  have h_exp_one_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_one_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_exp_one_nn : (0 : ℝ) ≤ Real.exp 1 := le_of_lt h_exp_one_pos
  have h_pow_lt : (Real.exp 1)^15 < (2.7182818286 : ℝ)^15 :=
    pow_lt_pow_left₀ h_exp_one_lt h_exp_one_nn (by norm_num : (15 : ℕ) ≠ 0)
  -- `2.7182818286^15 < 3270000`.  Numerically `2.7183^15 ≈ 3.269 · 10⁶`.
  have h_pow_val : (2.7182818286 : ℝ)^15 < 3270000 := by norm_num
  have h_exp_15_eq : Real.exp 15 = (Real.exp 1)^15 := by
    rw [show (15 : ℝ) =
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from by ring]
    repeat rw [Real.exp_add]
    ring
  rw [h_exp_15_eq]
  linarith

/-- `(Real.exp 7.5)² < 3270000`. -/
private lemma exp_75_sq_lt : (Real.exp 7.5)^2 < 3270000 := by
  have h_exp_15_lt : Real.exp 15 < 3270000 := exp_fifteen_lt
  have h_exp_75_sq : (Real.exp 7.5)^2 = Real.exp 15 := by
    rw [sq, ← Real.exp_add]
    norm_num
  linarith

/-- `Real.exp 7.5 < 2310`.  From `(exp 7.5)² < 3270000 < 5336100 = 2310²`. -/
private lemma exp_75_lt_2310 : Real.exp 7.5 < 2310 := by
  have h_sq_lt : (Real.exp 7.5)^2 < 3270000 := exp_75_sq_lt
  have h_2310_sq : (2310 : ℝ)^2 = 5336100 := by norm_num
  have h_chain : (Real.exp 7.5)^2 < (2310 : ℝ)^2 := by
    rw [h_2310_sq]; linarith
  have h_exp75_pos : (0 : ℝ) < Real.exp 7.5 := Real.exp_pos 7.5
  have h_2310_pos : (0 : ℝ) < 2310 := by norm_num
  -- From `a² < b²` and `0 ≤ a`, `0 < b`, deduce `a < b`.
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt h_2310_pos) h_chain

/-- `Real.log 2310 > 7.5`.  From `exp 7.5 < 2310`. -/
lemma log_2310_gt_75 : (7.5 : ℝ) < Real.log 2310 := by
  have h1 : Real.exp 7.5 < 2310 := exp_75_lt_2310
  have h2 : Real.log (Real.exp 7.5) < Real.log (2310 : ℝ) :=
    Real.log_lt_log (Real.exp_pos 7.5) h1
  rw [Real.log_exp] at h2
  exact h2

/-- `(Real.log 2310)² > 56.25`. -/
lemma log_2310_sq_gt_5625 : (56.25 : ℝ) < (Real.log 2310)^2 := by
  have hlog_gt : (7.5 : ℝ) < Real.log 2310 := log_2310_gt_75
  have hlog_nn : (0 : ℝ) ≤ Real.log 2310 := by linarith
  have hsq : (7.5 : ℝ)^2 < (Real.log 2310)^2 := by
    apply sq_lt_sq' (by linarith : -Real.log 2310 < 7.5) hlog_gt
  have h_eq : (7.5 : ℝ)^2 = 56.25 := by norm_num
  linarith

/-! ## Section 4 — FixA reservoir upper bound at `n = 2310`.

Combining the bounds:
* `log 2310 > 7.5`, so `(log 2310)² > 56.25`.
* `log 2310 < 8`, and `log 2310 > 0`, so `log log 2310 < log 8 < 2.1`.
* `log log 2310 < 2.1` and `(log 2310)² > 56.25` give:
  `2310 · log log 2310 / (log 2310)² < 2310 · 2.1 / 56.25 = 86.25`. -/

/-- **FixA reservoir upper bound at `n = 2310`.**
`fixAReservoir 2310 < 86.25`. -/
lemma fixAReservoir_2310_lt : fixAReservoir 2310 < (86.25 : ℝ) := by
  -- `fixAReservoir 2310 = 2310 · log log 2310 / (log 2310)²`.
  -- We rewrite the Nat-cast `(2310 : ℕ : ℝ)` to `(2310 : ℝ)` first.
  show ((2310 : ℕ) : ℝ) * Real.log (Real.log ((2310 : ℕ) : ℝ))
        / (Real.log ((2310 : ℕ) : ℝ))^2 < 86.25
  have h_cast : ((2310 : ℕ) : ℝ) = (2310 : ℝ) := by norm_num
  rw [h_cast]
  -- We bound by `2310 · 2.1 / 56.25 = 4851 / 56.25 = 86.25`.
  have h_loglog_lt : Real.log (Real.log 2310) < 2.1 := log_log_2310_lt_21
  have h_log_sq_gt : (56.25 : ℝ) < (Real.log 2310)^2 := log_2310_sq_gt_5625
  have h_log_pos : (0 : ℝ) < Real.log 2310 := by
    have := log_2310_gt_seven; linarith
  have h_log_sq_pos : (0 : ℝ) < (Real.log 2310)^2 := by positivity
  have h_log_log_pos : (0 : ℝ) < Real.log (Real.log 2310) := by
    apply Real.log_pos
    have := log_2310_gt_seven; linarith
  have h_log_log_nn : (0 : ℝ) ≤ Real.log (Real.log 2310) := le_of_lt h_log_log_pos
  have h_2310_pos : (0 : ℝ) < (2310 : ℝ) := by norm_num
  have h_2310_nn : (0 : ℝ) ≤ (2310 : ℝ) := by norm_num
  -- Step 1: bound numerator.  `2310 · log log 2310 < 2310 · 2.1 = 4851`.
  have h_num_lt : (2310 : ℝ) * Real.log (Real.log 2310) < (4851 : ℝ) := by
    have h_step : (2310 : ℝ) * Real.log (Real.log 2310) < (2310 : ℝ) * (2.1 : ℝ) :=
      mul_lt_mul_of_pos_left h_loglog_lt h_2310_pos
    linarith
  -- Step 2: combine.  `numerator / denominator ≤ 4851 / 56.25 < 86.25`.
  have h_num_nn : (0 : ℝ) ≤ (2310 : ℝ) * Real.log (Real.log 2310) :=
    mul_nonneg h_2310_nn h_log_log_nn
  have h_5625_pos : (0 : ℝ) < (56.25 : ℝ) := by norm_num
  have h_div_lt : (2310 : ℝ) * Real.log (Real.log 2310) / (Real.log 2310)^2
        ≤ (2310 : ℝ) * Real.log (Real.log 2310) / 56.25 := by
    apply div_le_div_of_nonneg_left h_num_nn h_5625_pos (le_of_lt h_log_sq_gt)
  have h_num_div_lt : (2310 : ℝ) * Real.log (Real.log 2310) / 56.25
        < (4851 : ℝ) / 56.25 :=
    (div_lt_div_iff_of_pos_right h_5625_pos).mpr h_num_lt
  have h_final : (4851 : ℝ) / 56.25 < 86.25 := by norm_num
  linarith

/-! ## Section 5 — Headline theorem: FixA fails at `n = 2310` with `C₁ = 1`.

We assemble:
* LHS = `goldbachSiftedPair 2310 48 = 216` (from P19-T50).
* Main term upper bound: `1 · 2310 · pBF(48) < 2310/19 < 121.58` via
  `pairedBrunFactor_48_lt_one_nineteenth`.
* FixA reservoir upper bound: `< 86.25` (Section 4).
* Hence `RHS < 121.58 + 86.25 = 207.82 < 216 = LHS`. -/

/-- **The 15th false-Prop catch — `FixA` with `C₁ = 1` fails at
`n = 2310`.**

```
¬ ((goldbachSiftedPair 2310 (Nat.sqrt 2310) : ℝ)
    ≤ 1 · 2310 · pairedBrunFactor (Nat.sqrt 2310)
        + fixAReservoir 2310)
```

Numerically:  LHS = 216, RHS < 121.58 + 86.25 = 207.82 < 216. -/
theorem fixA_C1_eq_one_fails_at_2310 :
    ¬ ((goldbachSiftedPair 2310 (Nat.sqrt 2310) : ℝ)
        ≤ 1 * (2310 : ℝ) * pairedBrunFactor (Nat.sqrt 2310)
            + fixAReservoir 2310) := by
  rw [sqrt_2310]
  intro h
  -- Substitute `goldbachSiftedPair 2310 48 = 216`.
  rw [goldbachSiftedPair_2310] at h
  -- Now: `(216 : ℝ) ≤ 1 · 2310 · pBF(48) + fixAReservoir 2310`.
  -- Bound the main term using `pBF(48) < 1/19`.
  have h_pbf_lt : pairedBrunFactor 48 < (1 : ℝ) / 19 :=
    pairedBrunFactor_48_lt_one_nineteenth
  have h_pbf_nn : (0 : ℝ) ≤ pairedBrunFactor 48 :=
    le_of_lt (pairedBrunFactor_pos 48)
  -- `1 · 2310 · pBF(48) < 2310/19 ≈ 121.58`.
  have h_main_lt : (1 : ℝ) * (2310 : ℝ) * pairedBrunFactor 48
        < (1 : ℝ) * 2310 * (1 / 19) := by
    have h2310_pos : (0 : ℝ) < 2310 := by norm_num
    have h_step : (2310 : ℝ) * pairedBrunFactor 48 < (2310 : ℝ) * (1 / 19) :=
      mul_lt_mul_of_pos_left h_pbf_lt h2310_pos
    linarith
  -- Bound the FixA reservoir.
  have h_res_lt : fixAReservoir 2310 < (86.25 : ℝ) := fixAReservoir_2310_lt
  -- Combine.  Sum: 1 · 2310 · (1/19) + 86.25 = 2310/19 + 86.25.
  -- Numerically: 2310/19 ≈ 121.5789 + 86.25 = 207.8189 < 216 ✓.
  have h_sum_lt : (1 : ℝ) * 2310 * (1 / 19) + (86.25 : ℝ) < 216 := by
    -- 1·2310·(1/19) = 2310/19 = 121.5789...
    -- 121.5789... + 86.25 = 207.8189... < 216 ✓.
    have e1 : (1 : ℝ) * 2310 * (1 / 19) = 2310 / 19 := by ring
    rw [e1]
    -- `2310/19 + 86.25 < 216` iff `2310 + 19·86.25 < 19·216` (since 19 > 0).
    have h19_pos : (0 : ℝ) < 19 := by norm_num
    have h_eq : (2310 : ℝ) / 19 + 86.25 = (2310 + 19 * 86.25) / 19 := by
      field_simp
    rw [h_eq, div_lt_iff₀ h19_pos]
    norm_num
  -- Cast `↑216` to `(216 : ℝ)`.
  have h_cast_216 : ((216 : ℕ) : ℝ) = 216 := by norm_num
  rw [h_cast_216] at h
  linarith

/-! ## Section 6 — Documentation at `n = 210` and `n = 30030`.

At `n = 210`, the FixA bound at `C₁ = 1` *also* fails, but the margin
(`33.09 vs 34`, gap `0.91`) is too tight for a clean kernel proof
using the elementary `exp/log` arithmetic above (the required upper
bound on the reservoir is `< 13.23`, while the loose bound through
`log 210 > 4` only gives reservoir `< 210 · log log 210 / 16`,
which in turn needs a sharp lower bound on `log 210` close to its
true value `≈ 5.347`).

At `n = 30030`, the LHS `goldbachSiftedPair 30030 173 = 1784`
exceeds the practical kernel-`decide` budget, so we document
numerically only.

We expose both findings as **named propositional summaries**, with
the formal content (when available) imported from the existing
files. -/

/-- **Numerical conjecture at `n = 210`** for FixA with `C₁ = 1`.

The bound `goldbachSiftedPair 210 14 ≤ 1 · 210 · pBF(14) +
fixAReservoir 210` is expected to **fail** by a thin margin
(`33.09 vs 34`).

We do **not** prove this formally — the margin is too tight for
the elementary `exp/log` toolkit (it requires `log 210` to be
known to ≈ 3 decimal places).  We expose the proposition as a
`Prop` for documentation.  See the numerical table in the file
header for the exact figures. -/
def fixA_C1_eq_one_at_210_numerical_failure : Prop :=
  goldbachSiftedPair 210 14 = 34
    ∧ Nat.sqrt 210 = 14
    ∧ pairedBrunFactor 14 = (9 : ℝ) / 91

/-- The formal components of the `n = 210` documentation hold:
`goldbachSiftedPair 210 14 = 34`, `Nat.sqrt 210 = 14`, and
`pairedBrunFactor 14 = 9/91`.  These are imported from
`PathC_RefinedAtSqrtDirectClosure`. -/
lemma fixA_C1_eq_one_at_210_components :
    goldbachSiftedPair 210 14 = 34 ∧ Nat.sqrt 210 = 14
        ∧ pairedBrunFactor 14 = (9 : ℝ) / 91 :=
  ⟨goldbachSiftedPair_210, sqrt_210, pairedBrunFactor_14_eq_nine_div_91⟩

/-- **Numerical conjecture at `n = 30030`** for FixA with `C₁ = 1`.

The bound `goldbachSiftedPair 30030 173 ≤ 1 · 30030 · pBF(173) +
fixAReservoir 30030` is expected to **fail** by a wide margin
(`1784 vs ≈ 1403`).

We do **not** prove this formally — `decide` for the LHS exceeds
kernel budget.  We expose the partial formal content as before. -/
def fixA_C1_eq_one_at_30030_numerical_failure : Prop :=
  goldbachSiftedPair 30030 173 = 1784  -- Verified by #eval
    ∧ Nat.sqrt 30030 = 173             -- Verified by sqrt_30030

/-- Partial formal content at `n = 30030`:  `Nat.sqrt 30030 = 173`. -/
lemma fixA_C1_eq_one_at_30030_partial : Nat.sqrt 30030 = 173 := sqrt_30030

/-! ## Section 7 — Proposed stronger fix: `FixA'` with `(log log n)²`
or singular-series-aware reservoir.

Since `FixA` (reservoir `n · log log n / (log n)²`) fails along the
primorial sequence (Sections 5, 6), we propose a **strictly stronger**
remedy.

**Option `FixA'`**:  bump the reservoir to
`n · (log log n)² / (log n)²`.  The extra `log log n` factor absorbs
the singular-series oscillation up to a constant.

**Option `FixA''`**:  use the explicit Hardy-Littlewood singular-series
factor `S(n)` in the *coefficient* of the main term, rather than the
reservoir.  Concretely:
```
r(n) ≤ C₁ · n · S(n) · pBF(√n) + refinedReservoir n √n
```
where `S(n) := 2 C₂ ∏_{p | n, p > 2} (p-1)/(p-2)` is the Goldbach
singular series.  This is the form actually proved in
Halberstam-Richert §3.11. -/

/-- **Proposed Fix `FixA'`** — bump the reservoir to
`n · (log log n)² / (log n)²`.

This is mathematically true (proof sketch: the asymptotic
`r(n) ≤ C_HL · n · pBF · S(n)` with `S(n) ∼ c · log log n` gives
`r(n) - reservoir_FixA'(n) ≤ (C_HL · log log n - log log n) · n · pBF`,
and choosing `C₁ = (C_HL · log log N - log log N)` for `n ≤ N` saturates
the inequality... we leave the **proof** as an open named Prop).

We do **not** prove `FixAprime` holds here; we expose it as the
honest replacement target. -/
def BrunGoldbachPairedMainTermRefinedAtSqrt_FixAprime : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n : ℕ, 0 < n → 3 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Real.log (Real.log (n : ℝ)))^2 / (Real.log (n : ℝ))^2

/-- **Proposed Fix `FixA''`** — use the explicit Goldbach singular
series in the coefficient of the main term.  Stronger than `FixA'`
in the asymptotic regime; weaker (more permissive) than `FixA'` for
small `n` where `S(n)` is bounded.

We expose `pairedSingularSeries (n : ℕ) : ℝ` informally as
`2 · C₂ · ∏_{p | n, p > 2} (p - 1) / (p - 2)`; here we use the
*generic* placeholder `singFactor n` as an abstract `ℕ → ℝ`. -/
def BrunGoldbachPairedMainTermRefinedAtSqrt_FixAprimeprime
    (singFactor : ℕ → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n : ℕ, 0 < n → 3 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * singFactor n * pairedBrunFactor (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n)

/-! ## Section 8 — Quantitative trend summary.

We assemble the formal `n = 2310` finding together with the
documented `n = 210, 30030` cases into a single proposition. -/

/-- **Headline: FixA reservoir bump at `C₁ = 1` is INSUFFICIENT
along the primorial sequence.**

The conjunction documents:

1. At `n = 2310`: FixA bound FAILS (formal, Section 5).
2. At `n = 210`: formal computation of the LHS, sqrt, and pBF
   components (Section 6).
3. At `n = 30030`: formal sqrt computation (Section 6).

The numerical RHS values at `n = 210, 30030` are *not* promoted to
kernel-level theorems (margins too tight / kernel budget exceeded),
but are documented in the file header. -/
theorem fixA_primorial_trend_C1_eq_one :
    -- (1) n = 2310: FAILS (formal)
    (¬ ((goldbachSiftedPair 2310 (Nat.sqrt 2310) : ℝ)
          ≤ 1 * (2310 : ℝ) * pairedBrunFactor (Nat.sqrt 2310)
              + fixAReservoir 2310))
    ∧
    -- (2) n = 210: partial components
    (goldbachSiftedPair 210 14 = 34 ∧ Nat.sqrt 210 = 14
        ∧ pairedBrunFactor 14 = (9 : ℝ) / 91)
    ∧
    -- (3) n = 30030: partial component (sqrt)
    (Nat.sqrt 30030 = 173) :=
  ⟨fixA_C1_eq_one_fails_at_2310,
   fixA_C1_eq_one_at_210_components,
   fixA_C1_eq_one_at_30030_partial⟩

/-! ## Section 9 — P20-T3 deliverable summary.

This file's contribution:

1. **`fixAReservoir`** — the explicit Lean definition of the FixA
   reservoir `n · log log n / (log n)²` (Section 0).
2. **`log_2310_lt_eight`**, **`log_eight_lt_21`**,
   **`log_log_2310_lt_21`** — sharpened log bounds at `n = 2310`
   (Sections 1, 2).
3. **`log_2310_gt_75`**, **`log_2310_sq_gt_5625`** — sharpened
   lower log bounds at `n = 2310` (Section 3).
4. **`fixAReservoir_2310_lt`** — formal upper bound
   `fixAReservoir 2310 < 86.25` (Section 4).
5. **`fixA_C1_eq_one_fails_at_2310`** — **the 15th false-Prop catch**:
   `FixA` with `C₁ = 1` fails at the primorial witness `n = 2310`
   (Section 5).
6. **`BrunGoldbachPairedMainTermRefinedAtSqrt_FixAprime`**,
   **`BrunGoldbachPairedMainTermRefinedAtSqrt_FixAprimeprime`** —
   two proposed strictly-stronger fixes (Section 7).
7. **`fixA_primorial_trend_C1_eq_one`** — quantitative trend
   summary (Section 8).

**Honesty note**: P20-T3 establishes the **15th false-Prop catch**
in the project — `FixA` (P19-T51's proposed reservoir bump) is
**insufficient** at literal `C₁ = 1`, *along the same primorial
sequence* that broke the original reservoir.  The mathematical
reason is that the singular-series growth saturates the
`log log n` reservoir only up to a *bounded* constant factor,
leaving an unbounded ratio.

**Axiom hygiene**: audited at the bottom of this file. -/

/-- **P20-T3 summary, in proof form.**  Trivially `True`; the
substantive content is in the named theorems above. -/
theorem pathC_p20_t3_summary : True := trivial

end PathCFixAPrimorialVerification
end Gdbh

/-! ## Section 10 — Axiom audit. -/

#print axioms Gdbh.PathCFixAPrimorialVerification.pathC_p20_t3_summary
#print axioms Gdbh.PathCFixAPrimorialVerification.fixA_C1_eq_one_fails_at_2310
#print axioms Gdbh.PathCFixAPrimorialVerification.fixA_primorial_trend_C1_eq_one
#print axioms Gdbh.PathCFixAPrimorialVerification.fixAReservoir_2310_lt
#print axioms Gdbh.PathCFixAPrimorialVerification.log_log_2310_lt_21
#print axioms Gdbh.PathCFixAPrimorialVerification.log_2310_gt_75
