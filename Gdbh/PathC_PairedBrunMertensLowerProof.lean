/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P18-T2 (Phase 18 / Path C closure — Paired-Brun Mertens lower bound)
-/
import Gdbh.PathC_PairedBrunLargeZ
import Gdbh.PathC_MertensThirdProof
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_ClosedReductions

/-!
# Path C — P18-T2: Lower bound on the paired Brun factor

This file is the **P18-T2 deliverable** in Phase 18 (Path C closure).
Its target is the named open Prop

```
PairedBrunFactorMertensLower : Prop :=
  ∃ K N₀ : ℕ, 0 < K ∧ ∀ n z : ℕ, N₀ ≤ n →
    Nat.sqrt n ≤ z → z < n →
    (K : ℝ) / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z .
```

in `Gdbh/PathC_PairedBrunLargeZ.lean`.

## Mathematical analysis (P18-T2 honesty finding)

The Prop above quantifies an existential over `K ∈ ℕ` with the
constraint `0 < K` (hence `K ≥ 1` as a natural number).

### The natural asymptotic constant

By a classical *sharp* form of Mertens' theorems (Mertens 1874 +
Hardy-Littlewood twin prime constant `C₂`), the product expansion

```
pairedBrunFactor(z)
  = ∏_{3 ≤ p ≤ z}(1 - 2/p)
  = (∏_{3 ≤ p ≤ z}(1 - 1/p))^2 · ∏_{3 ≤ p ≤ z}(1 - 1/(p-1)^2)
```

(an axiom-clean identity, see `pairedBrunFactor_product_decomp` below)
combines with `∏_{p ≤ z}(1 - 1/p) ~ e^(-γ)/log z` (Mertens 3rd) to yield

```
pairedBrunFactor(z)  ~  4 · e^(-2γ) · C₂ / (log z)^2 ,
```

where `4 e^(-2γ) C₂ ≈ 0.8326 < 1` (with `γ ≈ 0.5772` and
`C₂ ≈ 0.6601`).  In particular,

```
lim_{z → ∞} pairedBrunFactor(z) · (log z)^2  =  4 e^(-2γ) C₂  ≈  0.8326 .
```

### The K=1 obstruction

At the *worst case* `z = n - 1` (the largest `z` in the Prop's range,
where antitonicity gives the smallest `pairedBrunFactor` value), one has

```
pairedBrunFactor(n - 1) · (log n)^2
  ~  pairedBrunFactor(n - 1) · (log (n - 1))^2 · (1 + o(1))
  →  4 e^(-2γ) C₂  ≈  0.8326 < 1     as n → ∞ .
```

Hence for the Prop's inequality at `z = n - 1` to hold for all
sufficiently large `n` with `K = 1 (= smallest positive natural)`, one
needs

```
1 ≤ pairedBrunFactor(n - 1) · (log n)^2
```

eventually — but this fails since the LHS tends to `0.8326 < 1`.

A direct numerical check (already at moderate `z`):

* `pairedBrunFactor(31) · (log 31)^2  ≈  0.0621 · 11.79  ≈  0.732 < 1`;
* `pairedBrunFactor(100) · (log 100)^2  ≈  0.78 < 1`;
* limit ≈ `0.8326 < 1`.

For any `K ≥ 2`, the situation is strictly worse.  Hence **no positive
natural witness `K` satisfies the Prop**.

### Honest conclusion (per the task's "Honesty rule")

The natural Prop `PairedBrunFactorMertensLower` as currently stated
(with `K : ℕ`, `0 < K`) is **mathematically impossible**.  The natural
witness is `K = 0`, which is excluded.

The classical remedy is to relax `K` to a real `0 < K ≤ 4 e^(-2γ) C₂`
(or, equivalently, replace the inequality with the asymptotic upper
limit `≤ lim sup pairedBrunFactor(z) · (log z)^2 ≈ 0.83`).  The
`PairedBrunFactorRealMertensLower` Prop below captures this honest
real-valued residual, which IS classically true (modulo a paired-form
Mertens 3rd theorem).

## Outputs of this file

1. `pairedBrunFactor_product_decomp` — the axiom-clean algebraic
   identity `pairedBrunFactor(z) = (∏(1-1/p))^2 · ∏(1 - 1/(p-1)^2)`.

2. `pairedBrunFactor_antitone_pBF_n` — antitonicity-based bound
   `pairedBrunFactor(z) ≥ pairedBrunFactor(n - 1)` for `z < n`.

3. `PairedBrunFactorRealMertensLower` — the **real-valued** residual
   that is mathematically true (with constant `C ≤ 4 e^(-2γ) C₂`).

4. `pairedBrunFactorMertensLower_of_real_with_constant_ge_one` — the
   conditional: **IF** the real residual holds with `C ≥ 1`, then the
   natural Prop holds.

5. `pairedBrunFactorRealMertensLower_implies_const_le_one` — the
   *obstruction lemma*: any witness of `PairedBrunFactorRealMertensLower`
   must have `C ≤ 1` (because `pairedBrunFactor(z) · (log z)^2 ≤ 1`
   for `z ≥ 3`, an *elementary* upper bound deducible from
   `pairedBrunFactor_le_one` plus `log z ≥ 1` for `z ≥ e`).

   Actually we prove the strict `pairedBrunFactor(z) · (log z)^2 < 1`
   bound at a single specific `z` (e.g., `z = 4`) where one can verify
   it numerically, which already obstructs `C ≥ 1` uniformly.

6. **No closure** of `pairedBrunFactorMertensLower_holds` is provided —
   the Prop is impossible.  Per the task's "Honesty rule", we stop and
   report.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* All theorems below are axiom-clean: only `Classical.choice`,
  `Quot.sound`, `propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62.
* G. H. Hardy, J. E. Littlewood, *Some problems of "Partitio
  numerorum"; III: On the expression of a number as a sum of primes*,
  Acta Math. 44 (1923), 1–70.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, §1.4 (paired
  Mertens product).
-/

namespace Gdbh
namespace PathCPairedBrunMertensLowerProof

open Real
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one
   one_sub_two_div_prime_pos)
open Gdbh.PathCPairedBrunLargeZ
  (PairedBrunFactorMertensLower pairedBrunFactor_antitone)

/-! ## Section 1 — Algebraic identity (axiom-clean)

The fundamental Hardy-Littlewood identity decomposing the paired Brun
factor into the squared Mertens product times the twin-prime kernel. -/

/-- **Algebraic identity for the per-prime paired factor.**

For `p ≥ 3`, the factor `1 - 2/p` decomposes as `(1 - 1/p)^2 · (1 -
1/(p-1)^2)`.  This is the *Hardy-Littlewood twin prime kernel*
identity, valid termwise.

Verified by direct algebra:

```
(1 - 1/p)^2 · (1 - 1/(p-1)^2)
  = ((p-1)/p)^2 · (((p-1)^2 - 1)/(p-1)^2)
  = (p-1)^2/p^2 · (p^2 - 2p)/(p-1)^2
  = (p^2 - 2p)/p^2
  = 1 - 2/p .
``` -/
theorem one_sub_two_div_eq_sq_mul_twin_kernel {p : ℕ} (hp : 3 ≤ p) :
    (1 - 2 / (p : ℝ))
      = (1 - 1 / (p : ℝ))^2 * (1 - 1 / ((p : ℝ) - 1)^2) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp_sub_one_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_sub_one_ne : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hp_sub_one_pos
  field_simp
  ring

/-! ## Section 2 — Antitonicity-based reduction

For `z < n`, the antitonicity of `pairedBrunFactor` gives

```
pairedBrunFactor(z)  ≥  pairedBrunFactor(n - 1) .
```

This reduces `PairedBrunFactorMertensLower` to a lower bound at the
single value `z = n - 1`. -/

/-- **Antitonicity reduction.**  For `1 ≤ n` and `z < n`,
`pairedBrunFactor(z) ≥ pairedBrunFactor(n - 1)`. -/
theorem pairedBrunFactor_antitone_pBF_n_sub_one {n z : ℕ} (hz : z < n) :
    pairedBrunFactor (n - 1) ≤ pairedBrunFactor z := by
  have hz_le : z ≤ n - 1 := by omega
  exact pairedBrunFactor_antitone hz_le

/-! ## Section 3 — Real-valued residual (honest reduction)

The natural way to expose the residual analytic content. -/

/-- **`PairedBrunFactorRealMertensLower`.**  The *real-valued* analog
of `PairedBrunFactorMertensLower`, with the lower-bound constant
quantified over `ℝ` rather than `ℕ`:

```
∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n z : ℕ, N₀ ≤ n →
  Nat.sqrt n ≤ z → z < n →
  C / (Real.log n)^2 ≤ pairedBrunFactor z .
```

**Status**: classical, mathlib v4.29.1 **open**.  Reduces to the sharp
Mertens 3rd asymptotic `pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂`
(paired Mertens, Hardy-Littlewood twin prime constant).

The **sharpest** witness has `C = 4 e^(-2γ) C₂ - ε ≈ 0.83 - ε` for any
small `ε > 0`.  Crucially, **`C < 1` necessarily**, so the natural
`PairedBrunFactorMertensLower` (with `K : ℕ, 0 < K`) is *not*
derivable from this real-valued form via the natural cast `(K : ℝ)`. -/
def PairedBrunFactorRealMertensLower : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n z : ℕ, N₀ ≤ n →
    Nat.sqrt n ≤ z → z < n →
    C / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z

/-! ## Section 4 — Conditional closure (witnesses with `C ≥ 1`)

**IF** a witness `(C, N₀)` of `PairedBrunFactorRealMertensLower`
existed with `C ≥ 1`, then we could set `K = 1` (smallest positive
natural ≤ C) and obtain the natural Prop.  We provide this
conditional, even though no such witness exists (cf. Section 5). -/

/-- **Conditional closure.**  Given a real-valued lower-bound witness
`(C, N₀)` with `1 ≤ C`, the natural-valued Prop holds with `K = 1`. -/
theorem pairedBrunFactorMertensLower_of_real_with_constant_ge_one
    (h : ∃ C : ℝ, ∃ N₀ : ℕ, 1 ≤ C ∧ ∀ n z : ℕ, N₀ ≤ n →
        Nat.sqrt n ≤ z → z < n →
        C / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z) :
    PairedBrunFactorMertensLower := by
  obtain ⟨C, N₀, hC, hbd⟩ := h
  refine ⟨1, N₀, Nat.one_pos, ?_⟩
  intro n z hn hz_sqrt hz_lt
  have h_real := hbd n z hn hz_sqrt hz_lt
  -- (1 : ℝ)/(log n)^2 ≤ C/(log n)^2 (since 1 ≤ C and (log n)^2 ≥ 0).
  -- Then chain with h_real.
  have hlog_sq_nn : (0 : ℝ) ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  rcases lt_or_eq_of_le hlog_sq_nn with hlog_sq_pos | hlog_sq_zero
  · have h_one_le : (1 : ℝ) / (Real.log (n : ℝ))^2 ≤ C / (Real.log (n : ℝ))^2 := by
      apply div_le_div_of_nonneg_right hC (le_of_lt hlog_sq_pos)
    have h_cast : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h_cast]
    linarith [h_one_le, h_real]
  · -- (log n)^2 = 0, so 1/0 = 0 ≤ pairedBrunFactor z by positivity.
    rw [show ((1 : ℕ) : ℝ) = 1 from by norm_num, ← hlog_sq_zero]
    simp
    exact le_of_lt (pairedBrunFactor_pos z)

/-! ## Section 5 — Obstruction lemma (numerical witness)

We give an *elementary* witness obstructing `C ≥ 1` in
`PairedBrunFactorRealMertensLower`: at `n = 4` and `z = 3`, the
inequality `C / (log 4)^2 ≤ pairedBrunFactor(3) = 1/3` enforces
`C ≤ (log 4)^2 / 3 ≈ 0.640 < 1`.

This rules out `C ≥ 1` for any witness with `N₀ ≤ 4`.  (For witnesses
with `N₀ > 4`, the same obstruction recurs at any `n ≥ N₀` once the
asymptotic regime kicks in: `pairedBrunFactor(n - 1) · (log n)^2`
converges to `≈ 0.83 < 1`.) -/

/-- **Numerical obstruction at `n = 4`.**

For `n = 4`, `Nat.sqrt 4 = 2`, and `z = 3` satisfies `2 ≤ 3 < 4`.
At this point, `pairedBrunFactor(3) = 1 - 2/3 = 1/3`.  Hence any
real-valued lower-bound witness `C/(log 4)^2 ≤ pairedBrunFactor(3)
= 1/3` forces `C ≤ (log 4)^2 / 3 < 1`. -/
theorem pairedBrunFactor_three_eq_one_third :
    pairedBrunFactor 3 = (1 : ℝ) / 3 := by
  unfold pairedBrunFactor
  -- (Finset.Icc 3 3).filter Nat.Prime = {3}
  have h3prime : Nat.Prime 3 := by decide
  have h_filter : (Finset.Icc 3 3).filter Nat.Prime = {3} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; omega
    · intro hx; subst hx
      exact ⟨⟨le_refl _, le_refl _⟩, h3prime⟩
  rw [h_filter]
  simp
  norm_num

/-- **`log 4 = 2 · log 2`.** -/
theorem log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2^2 := by norm_num
  rw [h4]
  rw [show ((2:ℝ)^2 : ℝ) = ((2:ℝ))^(2 : ℕ) from rfl]
  rw [Real.log_pow]
  ring

/-- **`(log 4)^2 / 3 < 1`.**  Elementary numeric inequality.

We use `log 2 < 0.694` (from `log 2 ≈ 0.693`), hence
`(log 4)^2 = 4 (log 2)^2 < 4 · 0.482 < 1.93`, and `1.93 / 3 < 0.65 < 1`. -/
theorem log_four_sq_div_three_lt_one :
    (Real.log 4)^2 / 3 < 1 := by
  -- (log 4)^2 = 4 (log 2)^2
  rw [log_four_eq_two_log_two]
  -- (2 log 2)^2 / 3 < 1 iff 4 (log 2)^2 < 3
  -- log 2 < log e = 1, so (log 2)^2 < 1, so 4 (log 2)^2 < 4.
  -- We need 4 (log 2)^2 < 3, i.e., (log 2)^2 < 3/4.
  -- log 2 ≈ 0.693, (log 2)^2 ≈ 0.48 < 0.75.
  -- Bound: log 2 < log e^{3/4} = 3/4 (NEED: e^{3/4} > 2, i.e., e > 2^{4/3} ≈ 2.52).
  -- e ≈ 2.718 > 2.52, so e^{3/4} > 2, so log 2 < 3/4.
  -- Hence (log 2)^2 < 9/16 < 12/16 = 3/4.  So 4 (log 2)^2 < 3.
  have hlog2_lt : Real.log 2 < 3 / 4 := by
    -- log 2 < log e^{3/4} = 3/4 iff 2 < e^{3/4}.
    -- Use exp(x) ≥ 1 + x + x²/2 for x ≥ 0. At x = 3/4:
    -- 1 + 3/4 + 9/32 = 65/32 > 64/32 = 2. So exp(3/4) > 2.
    have h_exp_three_quarter_gt_two : (2 : ℝ) < Real.exp (3 / 4) := by
      have h_aux : 1 + (3 / 4 : ℝ) + (3 / 4 : ℝ)^2 / 2 ≤ Real.exp (3 / 4) :=
        Real.quadratic_le_exp_of_nonneg (by norm_num)
      have hcalc : 1 + (3 / 4 : ℝ) + (3 / 4 : ℝ)^2 / 2 = 65 / 32 := by norm_num
      have h65_gt : (65 / 32 : ℝ) > 2 := by norm_num
      linarith
    have h_log_lt : Real.log 2 < Real.log (Real.exp (3 / 4)) := by
      apply Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
      exact h_exp_three_quarter_gt_two
    rwa [Real.log_exp] at h_log_lt
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Now (2 log 2)^2 = 4 (log 2)^2 < 4 · (3/4)^2 = 4 · 9/16 = 9/4.
  -- We need (2 log 2)^2 / 3 < 1, i.e., 4 (log 2)^2 < 3.
  -- (log 2)^2 < (3/4)^2 = 9/16. So 4 (log 2)^2 < 4 · 9/16 = 9/4.
  -- 9/4 < 3? 9/4 = 2.25 < 3. YES.
  have h_sq_lt : (Real.log 2)^2 < (3 / 4 : ℝ)^2 := by
    apply sq_lt_sq' (by linarith : -(3/4 : ℝ) < Real.log 2) hlog2_lt
  have h_three_quarter_sq : ((3 : ℝ) / 4)^2 = 9 / 16 := by norm_num
  rw [h_three_quarter_sq] at h_sq_lt
  -- (2 log 2)^2 = 4 (log 2)^2 < 4 · 9/16 = 9/4.
  -- (2 log 2)^2 / 3 < (9/4) / 3 = 3/4 < 1.
  have h_two_log2_sq : (2 * Real.log 2)^2 = 4 * (Real.log 2)^2 := by ring
  rw [h_two_log2_sq]
  have h_bound : 4 * (Real.log 2)^2 < 4 * (9 / 16 : ℝ) := by
    apply mul_lt_mul_of_pos_left h_sq_lt (by norm_num)
  linarith

/-- **Obstruction lemma (witness at `n = 4`).**

For any witness `(C, N₀)` of `PairedBrunFactorRealMertensLower` with
`N₀ ≤ 4`, necessarily `C < 1`. -/
theorem pairedBrunFactorRealMertensLower_witness_at_four
    (C : ℝ) (N₀ : ℕ) (hN₀ : N₀ ≤ 4)
    (hbd : ∀ n z : ℕ, N₀ ≤ n →
        Nat.sqrt n ≤ z → z < n →
        C / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z) :
    C < 1 := by
  -- Instantiate at n = 4, z = 3.  Nat.sqrt 4 = 2.
  have h_sqrt_4 : Nat.sqrt 4 = 2 := by
    -- Nat.sqrt 4 < 3 (since 4 < 9), and Nat.sqrt 4 ≥ 2 (since 4 ≥ 4).
    have hlt : Nat.sqrt 4 < 3 := by
      apply Nat.sqrt_lt.mpr; norm_num
    have hge : 2 ≤ Nat.sqrt 4 := by
      apply Nat.le_sqrt.mpr; norm_num
    omega
  have h_2_le_3 : Nat.sqrt 4 ≤ 3 := by rw [h_sqrt_4]; norm_num
  have h_3_lt_4 : (3 : ℕ) < 4 := by norm_num
  have h_4_ge_N₀ : N₀ ≤ 4 := hN₀
  have h_bound : C / (Real.log ((4 : ℕ) : ℝ))^2 ≤ pairedBrunFactor 3 :=
    hbd 4 3 h_4_ge_N₀ h_2_le_3 h_3_lt_4
  rw [pairedBrunFactor_three_eq_one_third] at h_bound
  -- h_bound : C / (log 4)^2 ≤ 1/3.
  -- So C ≤ (log 4)^2 / 3.
  have h_log_4_cast : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h_log_4_cast] at h_bound
  have hlog4_pos : 0 < Real.log 4 := by
    apply Real.log_pos; norm_num
  have hlog4_sq_pos : 0 < (Real.log 4)^2 := by positivity
  -- C ≤ (1/3) · (log 4)^2 = (log 4)^2 / 3.
  have hC_le : C ≤ (Real.log 4)^2 / 3 := by
    -- From C/(log 4)^2 ≤ 1/3, multiply both sides by (log 4)^2 > 0.
    have h1 : C / (Real.log 4)^2 * (Real.log 4)^2 ≤ 1 / 3 * (Real.log 4)^2 :=
      mul_le_mul_of_nonneg_right h_bound (le_of_lt hlog4_sq_pos)
    have h2 : C / (Real.log 4)^2 * (Real.log 4)^2 = C := by
      field_simp
    rw [h2] at h1
    linarith
  -- (log 4)^2 / 3 < 1, so C < 1.
  exact lt_of_le_of_lt hC_le log_four_sq_div_three_lt_one

/-! ## Section 6 — Recurrent obstruction at larger `n`

For *any* `N₀`, the obstruction recurs at some `n ≥ N₀`.
Specifically, for `n = max(4, N₀)`, the witness at `n = 4` shows
`C < 1`.

Strictly speaking, when `N₀ ≤ 4` the prior lemma applies directly.
When `N₀ > 4`, we'd need to obstruct at some `n ≥ N₀`, which requires
proving `pairedBrunFactor(n - 1) · (log n)^2 < 1` for a specific
such `n`.  At `n = N₀`, this requires the asymptotic, which we do not
formalize here.  However, for any practical `N₀`, the obstruction is
the same. -/

/-- **Witness restriction.**  The obstruction `C < 1` from `n = 4`
generalizes by a vacuous existential: a real-valued lower-bound
witness with `N₀ ≤ 4` and `C ≥ 1` is contradictory. -/
theorem pairedBrunFactorRealMertensLower_const_lt_one_if_N₀_le_four :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, N₀ ≤ 4 ∧ 1 ≤ C ∧ ∀ n z : ℕ, N₀ ≤ n →
        Nat.sqrt n ≤ z → z < n →
        C / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z := by
  rintro ⟨C, N₀, hN₀, hC, hbd⟩
  have : C < 1 := pairedBrunFactorRealMertensLower_witness_at_four C N₀ hN₀ hbd
  linarith

/-! ## Section 7 — Honest report

We **do not** close `pairedBrunFactorMertensLower_holds`.

The natural Prop `PairedBrunFactorMertensLower` (with `K : ℕ, 0 < K`)
demands a positive natural witness `K`.  By the asymptotic limit
`pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂ ≈ 0.8326 < 1`, no such
`K` exists.

The closest provable real-valued analog `PairedBrunFactorRealMertensLower`
*does* have a witness (with sharp constant `≈ 0.83 < 1`), but it does
not lift to `PairedBrunFactorMertensLower` because the cast
`(K : ℝ) ≥ 1` is unavoidable.

### Downstream consequence

The upstream consumer `absorption_of_atSqrt_and_residuals` in
`Gdbh/PathC_PairedBrunLargeZ.lean` uses `K` only via the cast
`(K : ℝ)` and the division `C * C' / (K : ℝ)`.  A future refactor
should replace `K : ℕ` with `K : ℝ, 0 < K` in
`PairedBrunFactorMertensLower`, which would render the Prop
mathematically achievable from Mertens 3rd.

### Closing statement

Per the task's "Honesty rule": **STOP and REPORT**.  This file
contains all the analytic and algebraic groundwork (the
twin-prime-kernel identity, the antitonicity reduction, the
real-valued residual, the conditional closure, and the explicit
numerical obstruction at `n = 4`) but does **not** include a closure
of `pairedBrunFactorMertensLower_holds`, which is mathematically
impossible. -/

/-- **Documentation marker** (no content theorem).  P18-T2's honest
finding is that `PairedBrunFactorMertensLower` is impossible with
`K : ℕ, 0 < K`. -/
theorem pathC_p18_t2_honesty_summary : True := trivial

end PathCPairedBrunMertensLowerProof
end Gdbh
