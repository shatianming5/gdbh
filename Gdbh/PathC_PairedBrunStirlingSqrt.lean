/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P17-T5-Sqrt (Phase 17 / Path C — `PairedBrunStirlingTruncationErrorSqrt`
        axiom-clean closure via combinatorial Brun-Stirling estimate)
-/
import Gdbh.PathC_PairedBrunStirlingTrunc
import Gdbh.PathC_FactorialStirling

/-!
# Path C — P17-T5-Sqrt: Closure of `PairedBrunStirlingTruncationErrorSqrt`

This file is the **P17-T5-Sqrt deliverable** in Phase 17.  Its target is
the named open Prop `PairedBrunStirlingTruncationErrorSqrt` from
`Gdbh.PathC_PairedBrunStirlingTrunc`:

```
∃ k : ℕ → ℕ, ∃ N₀ : ℕ, ∀ n z : ℕ, N₀ ≤ n → z ≤ Nat.sqrt n →
  (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
      / ((2 * k n + 1).factorial : ℝ)
    ≤ (n : ℝ) / (2 * (Real.log (n : ℝ))^2)
```

## Strategy

The proof uses a **deep-truncation** choice `k(n) := 2n`, so
`2k(n)+1 = 4n+1`.  The combinatorial bound is then

```
(π(z))^{4n+1} ≤ (Nat.sqrt n + 1)^{4n+1}
            ≤ 4^n · (n+1)^{2n+1}     [via (√n+1)² ≤ 2(n+1)]
```

and the factorial bound (purely combinatorial — `Nat.factorial_mul_pow_le_factorial`)
gives

```
(4n+1)! ≥ n! · 4^n · (n+1)^{3n+1}
```

Combining and cancelling `4^n · (n+1)^{2n+1}` reduces the target to

```
n! · (n+1)^n ≥ 2 · (log n)²
```

which we close via the elementary bound
`(Real.log n)² ≤ n!` for `n ≥ 4` (from `PathC_FactorialStirling.log_sq_le_factorial_real`)
plus `(n+1)^n ≥ 2` for `n ≥ 1`.

## Witnesses

* `k(n) := 2n`
* `N₀ := 4`

## Constraint compliance

* No `sorry` / `axiom` / `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2 (Brun's pure sieve).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §2.2 (the combinatorial estimate `(π(z))^k / k!`).
* `Mathlib.Data.Nat.Factorial.Basic.factorial_mul_pow_le_factorial`.
-/

namespace Gdbh
namespace PathCPairedBrunStirlingSqrt

open Real
open Gdbh.PathCPairedBrunStirlingTrunc (PairedBrunStirlingTruncationErrorSqrt)
open Gdbh.PathCFactorialStirling (log_sq_le_factorial_real sq_le_factorial_of_four_le)

/-! ## Section 1 — Combinatorial helper lemmas on `Nat.sqrt`. -/

/-- For any `k : ℕ`, `2 * k ≤ k * k + 1`.  (This is `(k - 1)² ≥ 0` rearranged.) -/
private lemma two_le_sq_succ (k : ℕ) : 2 * k ≤ k * k + 1 := by
  induction k with
  | zero => omega
  | succ m ih =>
      -- Goal: 2*(m+1) ≤ (m+1)*(m+1) + 1.
      -- (m+1)*(m+1) + 1 - 2*(m+1) = m² + 2m + 1 + 1 - 2m - 2 = m² ≥ 0.
      nlinarith

/-- `2 · Nat.sqrt n ≤ n + 1` for all `n : ℕ`.

Proof: `(Nat.sqrt n - 1)² ≥ 0` rearranges to
`2 · Nat.sqrt n ≤ (Nat.sqrt n)² + 1 ≤ n + 1`. -/
private lemma two_sqrt_le_succ (n : ℕ) : 2 * Nat.sqrt n ≤ n + 1 := by
  have hk_sq_le_n : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have h_2k_le : 2 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n + 1 := two_le_sq_succ _
  omega

/-- `(Nat.sqrt n + 1)^2 ≤ 2 * (n + 1)` for all `n : ℕ`.

Proof: `(√n + 1)² = (√n)² + 2 √n + 1 ≤ n + (n+1) + 1 = 2n + 2 = 2(n+1)`,
using `(√n)² ≤ n` and `2 √n ≤ n + 1`. -/
private lemma sqrt_succ_sq_le (n : ℕ) :
    (Nat.sqrt n + 1)^2 ≤ 2 * (n + 1) := by
  set k := Nat.sqrt n with hk_def
  have hk_sq_le_n : k * k ≤ n := Nat.sqrt_le n
  have h_2k : 2 * k ≤ n + 1 := two_sqrt_le_succ n
  -- (k + 1)² = k² + 2k + 1 ≤ n + (n+1) + 1 = 2(n+1).
  have : (k + 1)^2 = k * k + 2 * k + 1 := by ring
  rw [this]
  -- k*k + 2k + 1 ≤ n + (n+1) + 1 = 2n + 2 = 2(n+1).
  omega

/-! ## Section 2 — Bound on `(Nat.sqrt n + 1)^(4n+1)`. -/

/-- **Power-product bound**: `(Nat.sqrt n + 1)^(4n+1) ≤ 4^n · (n+1)^(2n+1)`.

Proof: `(√n + 1)^(4n+1) = ((√n+1)²)^(2n) · (√n+1) ≤ (2(n+1))^(2n) · (n+1)
= 4^n · (n+1)^(2n+1)`.  The final step uses `√n + 1 ≤ n + 1`
(from `Nat.sqrt_le_self`). -/
private lemma sqrt_pow_le (n : ℕ) :
    (Nat.sqrt n + 1)^(4*n+1) ≤ 4^n * (n + 1)^(2*n+1) := by
  -- Rewrite (4n+1) = 2*(2n) + 1.
  have h_exp : 4 * n + 1 = 2 * (2 * n) + 1 := by ring
  rw [h_exp]
  -- (a+1)^(2k+1) = ((a+1)²)^k · (a+1).
  have h_pow_split :
      (Nat.sqrt n + 1)^(2 * (2 * n) + 1)
        = ((Nat.sqrt n + 1)^2)^(2 * n) * (Nat.sqrt n + 1) := by
    rw [pow_succ, ← pow_mul]
  rw [h_pow_split]
  -- ((√n+1)²)^(2n) ≤ (2(n+1))^(2n).
  have h_sq_le : (Nat.sqrt n + 1)^2 ≤ 2 * (n + 1) := sqrt_succ_sq_le n
  have h_pow_sq :
      ((Nat.sqrt n + 1)^2)^(2 * n) ≤ (2 * (n + 1))^(2 * n) := by
    exact Nat.pow_le_pow_left h_sq_le (2 * n)
  -- (√n+1) ≤ (n+1).
  have h_sqrt_le_self : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have h_succ_le : Nat.sqrt n + 1 ≤ n + 1 := Nat.succ_le_succ h_sqrt_le_self
  -- Combine: ((√n+1)²)^(2n) · (√n+1) ≤ (2(n+1))^(2n) · (n+1).
  have h_combine :
      ((Nat.sqrt n + 1)^2)^(2 * n) * (Nat.sqrt n + 1)
        ≤ (2 * (n + 1))^(2 * n) * (n + 1) := by
    exact Nat.mul_le_mul h_pow_sq h_succ_le
  -- (2(n+1))^(2n) = 2^(2n) · (n+1)^(2n) = 4^n · (n+1)^(2n).
  have h_2_pow : (2 * (n + 1))^(2 * n) = 4^n * (n + 1)^(2 * n) := by
    rw [Nat.mul_pow]
    have h_4n : (2 : ℕ)^(2 * n) = 4^n := by
      have : (2 : ℕ)^(2 * n) = (2^2)^n := by rw [pow_mul]
      rw [this]; norm_num
    rw [h_4n]
  rw [h_2_pow] at h_combine
  -- Final: 4^n · (n+1)^(2n) · (n+1) = 4^n · (n+1)^(2n+1).
  have h_final :
      4^n * (n + 1)^(2 * n) * (n + 1) = 4^n * (n + 1)^(2 * n + 1) := by
    rw [pow_succ]; ring
  rw [h_final] at h_combine
  exact h_combine

/-! ## Section 3 — Bound on `(4n+1)!`. -/

/-- **Factorial bound**: `n! · 4^n · (n+1)^(3n+1) ≤ (4n+1)!`.

Proof: iterated application of `Nat.factorial_mul_pow_le_factorial`:

* `n! · (n+1)^(n+1) ≤ (2n+1)!`  [with m=n, "n"=n+1]
* `(2n+1)! · (2n+2)^(2n) ≤ (4n+1)!`  [with m=2n+1, "n"=2n]

Multiplying: `n! · (n+1)^(n+1) · (2n+2)^(2n) ≤ (4n+1)!`.
Since `(2n+2)^(2n) = 2^(2n) · (n+1)^(2n) = 4^n · (n+1)^(2n)`, we get
`n! · 4^n · (n+1)^(3n+1) ≤ (4n+1)!`. -/
private lemma factorial_lower_bound (n : ℕ) :
    n.factorial * 4^n * (n + 1)^(3 * n + 1) ≤ (4 * n + 1).factorial := by
  -- Step 1: `n! · (n+1)^(n+1) ≤ (2n+1)!`.
  have h_step1 : n.factorial * (n + 1)^(n + 1) ≤ (2 * n + 1).factorial := by
    have h := @Nat.factorial_mul_pow_le_factorial n (n + 1)
    -- h : n! * (n + 1)^(n + 1) ≤ (n + (n + 1))!
    have h_eq : n + (n + 1) = 2 * n + 1 := by ring
    rw [h_eq] at h
    exact h
  -- Step 2: `(2n+1)! · (2n+2)^(2n) ≤ (4n+1)!`.
  have h_step2 : (2 * n + 1).factorial * (2 * n + 2)^(2 * n) ≤ (4 * n + 1).factorial := by
    have h := @Nat.factorial_mul_pow_le_factorial (2 * n + 1) (2 * n)
    -- h : (2n+1)! * (2n + 1 + 1)^(2n) ≤ (2n + 1 + 2n)!
    -- We need (2n+2)^(2n) = (2n+1+1)^(2n), and 4n+1 = 2n+1+2n.
    have h_eq1 : 2 * n + 1 + 1 = 2 * n + 2 := by ring
    have h_eq2 : 2 * n + 1 + 2 * n = 4 * n + 1 := by ring
    rw [h_eq1, h_eq2] at h
    exact h
  -- Combine: multiply step1 by (2n+2)^(2n) and apply step2.
  have h_mul1 :
      n.factorial * (n + 1)^(n + 1) * (2 * n + 2)^(2 * n)
        ≤ (2 * n + 1).factorial * (2 * n + 2)^(2 * n) :=
    Nat.mul_le_mul_right _ h_step1
  have h_chain :
      n.factorial * (n + 1)^(n + 1) * (2 * n + 2)^(2 * n)
        ≤ (4 * n + 1).factorial :=
    le_trans h_mul1 h_step2
  -- Simplify the LHS: (2n+2)^(2n) = (2(n+1))^(2n) = 4^n · (n+1)^(2n).
  have h_2n2_pow : (2 * n + 2)^(2 * n) = 4^n * (n + 1)^(2 * n) := by
    have h_factor : (2 : ℕ) * n + 2 = 2 * (n + 1) := by ring
    rw [h_factor, Nat.mul_pow]
    have h_4n : (2 : ℕ)^(2 * n) = 4^n := by
      have : (2 : ℕ)^(2 * n) = (2^2)^n := by rw [pow_mul]
      rw [this]; norm_num
    rw [h_4n]
  rw [h_2n2_pow] at h_chain
  -- (n+1)^(n+1) · (n+1)^(2n) = (n+1)^(3n+1).
  have h_combine_pow :
      n.factorial * (n + 1)^(n + 1) * (4^n * (n + 1)^(2 * n))
        = n.factorial * 4^n * (n + 1)^(3 * n + 1) := by
    have h_pow_add : (n + 1)^(n + 1) * (n + 1)^(2 * n) = (n + 1)^(3 * n + 1) := by
      rw [← pow_add]
      have : n + 1 + 2 * n = 3 * n + 1 := by ring
      rw [this]
    -- Rearrange and use h_pow_add.
    calc n.factorial * (n + 1)^(n + 1) * (4^n * (n + 1)^(2 * n))
        = n.factorial * 4^n * ((n + 1)^(n + 1) * (n + 1)^(2 * n)) := by ring
      _ = n.factorial * 4^n * (n + 1)^(3 * n + 1) := by rw [h_pow_add]
  rw [h_combine_pow] at h_chain
  exact h_chain

/-! ## Section 4 — Lower bound on `n! · (n+1)^n`. -/

/-- `(n + 1)^n ≥ 2` for `n ≥ 1` (in `ℕ`).

Proof: `(n+1)^n ≥ 2^1 = 2` follows from `n + 1 ≥ 2` and `n ≥ 1`. -/
private lemma succ_pow_ge_two_nat {n : ℕ} (hn : 1 ≤ n) : 2 ≤ (n + 1)^n := by
  -- Since n ≥ 1 and n+1 ≥ 2, (n+1)^n ≥ 2^n ≥ 2^1 = 2.
  have h_two_le_succ : 2 ≤ n + 1 := by omega
  have h_two_pow : (2 : ℕ)^n ≤ (n + 1)^n :=
    Nat.pow_le_pow_left h_two_le_succ n
  have h_two_pow_ge : (2 : ℕ) ≤ 2^n := by
    have : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    simpa using this
  exact le_trans h_two_pow_ge h_two_pow

/-- `(n+1)^n ≥ 2` as a real inequality for `n ≥ 1`. -/
private lemma succ_pow_ge_two_real {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ≤ ((n + 1)^n : ℕ) := by
  have h := succ_pow_ge_two_nat hn
  exact_mod_cast h

/-- **Key real inequality**: `2 * (log n)² ≤ n! · (n+1)^n` for `n ≥ 4`.

Proof: by `log_sq_le_factorial_real`, `(log n)² ≤ n!` for `n ≥ 4`.
And `(n+1)^n ≥ 2` for `n ≥ 1`.  Multiplying: `2 (log n)² ≤ 2 · n! ≤ n! · (n+1)^n`. -/
private lemma two_log_sq_le_factorial_mul_pow {n : ℕ} (hn : 4 ≤ n) :
    2 * (Real.log (n : ℝ))^2 ≤ (n.factorial : ℝ) * ((n + 1)^n : ℕ) := by
  -- `(log n)² ≤ n!`.
  have h1 : (Real.log (n : ℝ))^2 ≤ (n.factorial : ℝ) :=
    log_sq_le_factorial_real hn
  -- `(n+1)^n ≥ 2`.
  have hn_ge_one : 1 ≤ n := by omega
  have h2 : (2 : ℝ) ≤ ((n + 1)^n : ℕ) := succ_pow_ge_two_real hn_ge_one
  -- `0 ≤ (log n)²` and `0 ≤ n!`.
  have h_log_sq_nn : 0 ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  have h_fact_pos : 0 < (n.factorial : ℝ) := by
    have : 0 < n.factorial := Nat.factorial_pos n
    exact_mod_cast this
  have h_fact_nn : 0 ≤ (n.factorial : ℝ) := le_of_lt h_fact_pos
  -- 2 · (log n)² ≤ 2 · n! ≤ n! · (n+1)^n.
  have hstep1 : 2 * (Real.log (n : ℝ))^2 ≤ 2 * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
  have hstep2 : 2 * (n.factorial : ℝ) ≤ (n.factorial : ℝ) * ((n + 1)^n : ℕ) := by
    rw [mul_comm (n.factorial : ℝ) _]
    exact mul_le_mul_of_nonneg_right h2 h_fact_nn
  linarith

/-! ## Section 5 — Main combinatorial inequality. -/

/-- **Main combinatorial inequality**.

For `n ≥ 4`,
```
2 · (log n)² · (Nat.sqrt n + 1)^(4n+1) ≤ (4n+1)!
```

Proof: by `sqrt_pow_le` and `factorial_lower_bound`, both purely combinatorial.
Reduces to `n! · (n+1)^n ≥ 2 (log n)²`, then applies
`two_log_sq_le_factorial_mul_pow`. -/
private lemma key_combinatorial_bound {n : ℕ} (hn : 4 ≤ n) :
    2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1)^(4 * n + 1) : ℕ)
      ≤ ((4 * n + 1).factorial : ℕ) := by
  -- Step 1: `(√n+1)^(4n+1) ≤ 4^n · (n+1)^(2n+1)`.
  have h_pow_bound : (Nat.sqrt n + 1)^(4*n+1) ≤ 4^n * (n + 1)^(2*n+1) :=
    sqrt_pow_le n
  -- Step 2: `n! · 4^n · (n+1)^(3n+1) ≤ (4n+1)!`.
  have h_fact_bound :
      n.factorial * 4^n * (n + 1)^(3 * n + 1) ≤ (4 * n + 1).factorial :=
    factorial_lower_bound n
  -- Lift to real and combine.
  have h_pow_real :
      ((Nat.sqrt n + 1)^(4*n+1) : ℕ)
        ≤ ((4^n * (n + 1)^(2*n+1) : ℕ) : ℝ) := by exact_mod_cast h_pow_bound
  have h_fact_real :
      ((n.factorial * 4^n * (n + 1)^(3 * n + 1) : ℕ) : ℝ)
        ≤ ((4 * n + 1).factorial : ℕ) := by exact_mod_cast h_fact_bound
  -- 2 (log n)² · (√n+1)^(4n+1) ≤ 2 (log n)² · 4^n · (n+1)^(2n+1).
  have h_log_sq_nn : 0 ≤ 2 * (Real.log (n : ℝ))^2 := by positivity
  have h_step1 :
      2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1)^(4*n+1) : ℕ)
        ≤ 2 * (Real.log (n : ℝ))^2 * ((4^n * (n + 1)^(2*n+1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left h_pow_real h_log_sq_nn
  -- Cast manipulation: 2 (log n)² · 4^n · (n+1)^(2n+1) = 4^n · (n+1)^(2n+1) · 2 (log n)².
  have h_cast_split :
      ((4^n * (n + 1)^(2*n+1) : ℕ) : ℝ) = (4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ) := by
    push_cast; ring
  rw [h_cast_split] at h_step1
  -- Now use h_fact_real and the key inequality.
  -- We want: 2 (log n)² · 4^n · (n+1)^(2n+1) ≤ n! · 4^n · (n+1)^(3n+1).
  -- i.e., 2 (log n)² ≤ n! · (n+1)^n  (cancelling 4^n · (n+1)^(2n+1)).
  have h_key : 2 * (Real.log (n : ℝ))^2 ≤ (n.factorial : ℝ) * ((n + 1)^n : ℕ) :=
    two_log_sq_le_factorial_mul_pow hn
  -- 4^n · (n+1)^(2n+1) ≥ 0.
  have h_4n_nn : (0 : ℝ) ≤ (4^n : ℕ) := by exact_mod_cast Nat.zero_le _
  have h_succ_pow_nn : (0 : ℝ) ≤ ((n + 1)^(2 * n + 1) : ℕ) := by exact_mod_cast Nat.zero_le _
  -- Multiply h_key by 4^n · (n+1)^(2n+1).
  have h_key_mul :
      2 * (Real.log (n : ℝ))^2 * ((4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ))
        ≤ (n.factorial : ℝ) * ((n + 1)^n : ℕ) * ((4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ)) := by
    have h_prod_nn : (0 : ℝ) ≤ (4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ) := by positivity
    exact mul_le_mul_of_nonneg_right h_key h_prod_nn
  -- RHS of h_key_mul = n! · 4^n · (n+1)^(3n+1) (combining powers).
  have h_rhs_combine :
      (n.factorial : ℝ) * ((n + 1)^n : ℕ) * ((4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ))
        = ((n.factorial * 4^n * (n + 1)^(3 * n + 1) : ℕ) : ℝ) := by
    push_cast
    have h_pow_combine : ((n + 1) : ℝ)^n * ((n + 1) : ℝ)^(2 * n + 1)
        = ((n + 1) : ℝ)^(3 * n + 1) := by
      rw [← pow_add]
      have : n + (2 * n + 1) = 3 * n + 1 := by ring
      rw [this]
    calc (n.factorial : ℝ) * (((n + 1) : ℝ)^n) * ((4 : ℝ)^n * ((n + 1) : ℝ)^(2*n+1))
        = (n.factorial : ℝ) * (4 : ℝ)^n * (((n + 1) : ℝ)^n * ((n + 1) : ℝ)^(2*n+1)) := by ring
      _ = (n.factorial : ℝ) * (4 : ℝ)^n * ((n + 1) : ℝ)^(3 * n + 1) := by rw [h_pow_combine]
  rw [h_rhs_combine] at h_key_mul
  -- Combine: 2 (log n)² · (√n+1)^(4n+1) ≤ 2 (log n)² · 4^n · (n+1)^(2n+1)
  --        ≤ n! · 4^n · (n+1)^(3n+1) ≤ (4n+1)!.
  calc 2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1)^(4 * n + 1) : ℕ)
      ≤ 2 * (Real.log (n : ℝ))^2 * ((4^n : ℕ) * ((n + 1)^(2*n+1) : ℕ)) := h_step1
    _ ≤ ((n.factorial * 4^n * (n + 1)^(3 * n + 1) : ℕ) : ℝ) := h_key_mul
    _ ≤ ((4 * n + 1).factorial : ℕ) := h_fact_real

/-! ## Section 6 — `π(z) ≤ Nat.sqrt n + 1`. -/

/-- `Nat.primeCounting z ≤ Nat.sqrt n + 1` when `z ≤ Nat.sqrt n`.

Combines `Nat.primeCounting z ≤ z + 1` (mathlib's `Nat.count_le`) with `z ≤ Nat.sqrt n`. -/
private lemma primeCounting_le_sqrt_succ {n z : ℕ} (hz : z ≤ Nat.sqrt n) :
    Nat.primeCounting z ≤ Nat.sqrt n + 1 := by
  -- `primeCounting z ≤ z + 1`.
  have h1 : Nat.primeCounting z ≤ z + 1 := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact Nat.count_le (p := Nat.Prime)
  -- Combine with z ≤ Nat.sqrt n.
  omega

/-! ## Section 7 — The closure theorem. -/

/-- **Closure of `PairedBrunStirlingTruncationErrorSqrt` (P17-T5-Sqrt).**

Witnesses: `k(n) := 2 * n`, `N₀ := 4`.

The proof has two regimes:

* `n ≤ 3`: `Nat.sqrt n ≤ 1`, so `z ≤ 1` forces `π(z) = 0`, hence LHS = 0 ≤ RHS.
  But we set `N₀ = 4`, so this case is vacuous.

* `n ≥ 4`: use the combinatorial Brun-Stirling bound
  `2 (log n)² · (π(z))^(4n+1) ≤ (4n+1)!` from `key_combinatorial_bound`,
  combined with `π(z) ≤ Nat.sqrt n + 1` via `primeCounting_le_sqrt_succ`. -/
theorem pairedBrunStirlingTruncationErrorSqrt_holds :
    PairedBrunStirlingTruncationErrorSqrt := by
  refine ⟨fun n => 2 * n, 4, ?_⟩
  intro n z hn hz
  -- Goal: n · π(z)^(2(2n)+1) / (2(2n)+1)! ≤ n / (2 (log n)²)
  --     = n · π(z)^(4n+1) / (4n+1)! ≤ n / (2 (log n)²).
  -- Normalize `2 * (2 * n) + 1 = 4 * n + 1`.
  have h_exp_eq : 2 * (2 * n) + 1 = 4 * n + 1 := by ring
  rw [h_exp_eq]
  -- Setup: log n > 0, 2 (log n)² > 0, (4n+1)! > 0.
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hn_real_ge_four : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- log n ≥ log 4 > 1 for n ≥ 4? log 4 ≈ 1.386 > 1.
  -- We need: log n > 0, i.e., n > 1.
  have h_log_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    linarith
  have h_log_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have h_2_log_sq_pos : 0 < 2 * (Real.log (n : ℝ))^2 := by linarith
  have h_2_log_sq_nn : 0 ≤ 2 * (Real.log (n : ℝ))^2 := le_of_lt h_2_log_sq_pos
  have h_fact_pos : 0 < ((4 * n + 1).factorial : ℝ) := by
    have : 0 < (4 * n + 1).factorial := Nat.factorial_pos _
    exact_mod_cast this
  -- Cast bookkeeping for π(z).
  have h_piz_le : Nat.primeCounting z ≤ Nat.sqrt n + 1 :=
    primeCounting_le_sqrt_succ hz
  have h_piz_real_le :
      (Nat.primeCounting z : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h_piz_le
  have h_piz_real_nn : (0 : ℝ) ≤ (Nat.primeCounting z : ℝ) := by
    exact_mod_cast Nat.zero_le _
  -- (π(z))^(4n+1) ≤ (Nat.sqrt n + 1)^(4n+1) (in ℝ).
  have h_pi_pow_le :
      (Nat.primeCounting z : ℝ)^(4 * n + 1) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) :=
    pow_le_pow_left₀ h_piz_real_nn h_piz_real_le _
  have h_pi_pow_nn :
      (0 : ℝ) ≤ (Nat.primeCounting z : ℝ)^(4 * n + 1) := by positivity
  -- Combine: 2 (log n)² · (π(z))^(4n+1) ≤ 2 (log n)² · (√n+1)^(4n+1).
  have h_mul_pi :
      2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1)
        ≤ 2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) :=
    mul_le_mul_of_nonneg_left h_pi_pow_le h_2_log_sq_nn
  -- Cast: ((Nat.sqrt n + 1)^(4n+1) : ℕ) = ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4n+1).
  have h_cast_pow :
      (((Nat.sqrt n + 1)^(4 * n + 1) : ℕ) : ℝ)
        = ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) := by
    push_cast; ring
  -- Key bound: 2 (log n)² · (√n+1)^(4n+1) ≤ (4n+1)!.
  have h_key : 2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1)^(4 * n + 1) : ℕ)
      ≤ ((4 * n + 1).factorial : ℕ) := key_combinatorial_bound hn
  rw [h_cast_pow] at h_key
  -- Chain: 2 (log n)² · (π(z))^(4n+1) ≤ (4n+1)!.
  have h_chain :
      2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1)
        ≤ ((4 * n + 1).factorial : ℝ) := le_trans h_mul_pi h_key
  -- Final algebra: rearrange to the form `n · π(z)^(4n+1) / (4n+1)! ≤ n / (2 (log n)²)`.
  -- Equivalent to: n · π(z)^(4n+1) · 2 (log n)² ≤ n · (4n+1)!.
  -- Divide both sides by 2 (log n)² · (4n+1)! (both positive).
  -- Use `div_le_div_iff`.
  rw [div_le_div_iff₀ h_fact_pos h_2_log_sq_pos]
  -- Goal: n · π(z)^(4n+1) · (2 (log n)²) ≤ n · (4n+1)!.
  -- From h_chain: π(z)^(4n+1) · (2 (log n)²) ≤ (4n+1)!.
  -- Multiply both sides by n (which is ≥ 0).
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have h_chain' :
      (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
        ≤ ((4 * n + 1).factorial : ℝ) := by
    have h_comm :
        (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
          = 2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1) := by ring
    rw [h_comm]; exact h_chain
  calc (n : ℝ) * (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
      = (n : ℝ) * ((Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)) := by ring
    _ ≤ (n : ℝ) * ((4 * n + 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left h_chain' h_n_nn

/-- Explicit canonical-witness form of
`pairedBrunStirlingTruncationErrorSqrt_holds`.

The existential theorem above hides the witness `k n = 2 * n`.  This public
form exposes that witness for downstream canonical-tail workers. -/
theorem pairedBrunStirlingTruncationErrorSqrt_canonical :
    ∃ N₀ : ℕ, ∀ n z : ℕ, N₀ ≤ n → z ≤ Nat.sqrt n →
      (n : ℝ) * (Nat.primeCounting z : ℝ)^(2 * (2 * n) + 1)
          / ((2 * (2 * n) + 1).factorial : ℝ)
        ≤ (n : ℝ) / (2 * (Real.log (n : ℝ))^2) := by
  refine ⟨4, ?_⟩
  intro n z hn hz
  have h_exp_eq : 2 * (2 * n) + 1 = 4 * n + 1 := by ring
  rw [h_exp_eq]
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hn_real_ge_four : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_log_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    linarith
  have h_log_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have h_2_log_sq_pos : 0 < 2 * (Real.log (n : ℝ))^2 := by linarith
  have h_2_log_sq_nn : 0 ≤ 2 * (Real.log (n : ℝ))^2 := le_of_lt h_2_log_sq_pos
  have h_fact_pos : 0 < ((4 * n + 1).factorial : ℝ) := by
    have : 0 < (4 * n + 1).factorial := Nat.factorial_pos _
    exact_mod_cast this
  have h_piz_le : Nat.primeCounting z ≤ Nat.sqrt n + 1 :=
    primeCounting_le_sqrt_succ hz
  have h_piz_real_le :
      (Nat.primeCounting z : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h_piz_le
  have h_piz_real_nn : (0 : ℝ) ≤ (Nat.primeCounting z : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_pi_pow_le :
      (Nat.primeCounting z : ℝ)^(4 * n + 1) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) :=
    pow_le_pow_left₀ h_piz_real_nn h_piz_real_le _
  have h_mul_pi :
      2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1)
        ≤ 2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) :=
    mul_le_mul_of_nonneg_left h_pi_pow_le h_2_log_sq_nn
  have h_cast_pow :
      (((Nat.sqrt n + 1)^(4 * n + 1) : ℕ) : ℝ)
        = ((Nat.sqrt n + 1 : ℕ) : ℝ)^(4 * n + 1) := by
    push_cast; ring
  have h_key : 2 * (Real.log (n : ℝ))^2 * ((Nat.sqrt n + 1)^(4 * n + 1) : ℕ)
      ≤ ((4 * n + 1).factorial : ℕ) := key_combinatorial_bound hn
  rw [h_cast_pow] at h_key
  have h_chain :
      2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1)
        ≤ ((4 * n + 1).factorial : ℝ) := le_trans h_mul_pi h_key
  rw [div_le_div_iff₀ h_fact_pos h_2_log_sq_pos]
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have h_chain' :
      (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
        ≤ ((4 * n + 1).factorial : ℝ) := by
    have h_comm :
        (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
          = 2 * (Real.log (n : ℝ))^2 * (Nat.primeCounting z : ℝ)^(4 * n + 1) := by ring
    rw [h_comm]; exact h_chain
  calc (n : ℝ) * (Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)
      = (n : ℝ) * ((Nat.primeCounting z : ℝ)^(4 * n + 1) * (2 * (Real.log (n : ℝ))^2)) := by ring
    _ ≤ (n : ℝ) * ((4 * n + 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left h_chain' h_n_nn

/-! ## Section 8 — Public deliverable -/

/-- **Public deliverable**: `PairedBrunStirlingTruncationErrorSqrt` holds. -/
theorem pairedBrunStirlingTruncationErrorSqrt_closed :
    PairedBrunStirlingTruncationErrorSqrt :=
  pairedBrunStirlingTruncationErrorSqrt_holds

end PathCPairedBrunStirlingSqrt
end Gdbh
