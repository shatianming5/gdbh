/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P23-T2 (Phase 23 / Path C — Chebyshev θ ↔ log primorial bridge.)
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Gdbh.PathC_SingularSeriesPrimorialMertens
import Gdbh.VonMangoldtGoldbach

/-!
# Path C — P23-T2: Chebyshev θ for primorial estimates

## Mission

To bridge the singular-series primorial bound

```
  S(p_k#) ≤ K · log log (p_k#)
```

we need to compare `p_k` (the largest prime in `p_k#`) with
`log(p_k#)` and `log log (p_k#)`.  The Chebyshev θ function

```
  θ(x) := Σ_{p ≤ x, p prime} log p
```

provides exactly the right link: by mathlib's
`Chebyshev.theta_eq_log_primorial`,

```
  log(p_k#) = log (primorial p_k) = θ(p_k).
```

Combined with the two-sided Chebyshev bound `c · x ≤ θ(x) ≤ log 4 · x`
(eventual lower from `eventually_chebyshev_theta_two_mul_ge_const_mul_linear`,
upper from mathlib's `Chebyshev.theta_le_log4_mul_x`), this gives the
asymptotic `log(p_k#) ≍ p_k`, hence `log log (p_k#) ≍ log p_k`.

## Deliverables

1. **`theta` alias** — re-exposes `Chebyshev.theta` for ergonomic use in
   this file's API.

2. **`log_primorial_eq_theta`** — the identity
   `log(primorial n) = θ(n)`, the unique workhorse identity.

3. **Chebyshev two-sided** — for `0 < c < log 4`, eventually
   `c · x ≤ θ(x)`; unconditionally `θ(x) ≤ log 4 · x` for `x ≥ 0`.

4. **`ChebyshevTwoSidedLinear`** — packaged named Prop, closed below.

5. **`S_primorial_le_loglog_primorial`** — re-exports
   `SingularSeriesPrimorialMertensBound`, which is exactly the
   headline bridge `S(p_k#) ≤ K · log log p_k#` (proved in P22-T7).

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.

The bottom of the file contains a `#print axioms` audit on the
headline Chebyshev two-sided closure.
-/

namespace Gdbh
namespace PathCChebyshevPrimorial

open Real Filter
open Gdbh.PathCSingularSeriesPrimorialMertens
  (SingularSeriesPrimorialMertensBound
   singularSeriesPrimorialMertensBound_holds primorialOdd)

/-! ## Section 1 — `theta` alias and log–primorial identity -/

/-- **`theta`** — alias for `Chebyshev.theta`, the Chebyshev first
function `θ(x) = Σ_{p ≤ x, p prime} log p`. -/
noncomputable def theta (x : ℝ) : ℝ := Chebyshev.theta x

/-- **Headline identity P23-T2(2): `log(primorial n) = θ(n)`** for
`n : ℕ`.  This is mathlib's `Chebyshev.theta_eq_log_primorial`
specialised to a natural argument.  Phrased as "log of the primorial
through `n` equals θ at `n`", which is exactly the bridge

```
  log (p_k#) = θ (p_k)
```

once one notes that for `n = p_k` (the `k`-th prime), `primorial p_k`
is the product of all primes ≤ p_k, i.e., the standard primorial. -/
theorem log_primorial_eq_theta (n : ℕ) :
    Real.log ((primorial n : ℕ) : ℝ) = theta ((n : ℕ) : ℝ) := by
  unfold theta
  rw [Chebyshev.theta_eq_log_primorial]
  -- ⌊((n : ℕ) : ℝ)⌋₊ = n
  rw [Nat.floor_natCast n]

/-- Real-typed variant: `log(primorial n : ℝ) = θ(n : ℝ)`. -/
theorem log_primorial_eq_theta_real (n : ℕ) :
    Real.log ((primorial n : ℝ)) = theta (n : ℝ) := by
  have h := log_primorial_eq_theta n
  -- Both sides cast through.
  have h_cast : ((primorial n : ℕ) : ℝ) = (primorial n : ℝ) := by norm_cast
  rw [h_cast] at h
  exact h

/-- Reformulation in terms of the `k`-th prime `p_k := Nat.nth Nat.Prime k`,
matching the canonical formulation `log(p_k#) = θ(p_k)`.

By convention `Nat.nth Nat.Prime 0 = 2`, so this corresponds to
"primorial through the (k+1)-st prime equals θ at the (k+1)-st
prime".  The identity is just `log_primorial_eq_theta` applied at
`Nat.nth Nat.Prime k`. -/
theorem log_primorial_nth_prime_eq_theta (k : ℕ) :
    Real.log ((primorial (Nat.nth Nat.Prime k) : ℝ))
      = theta ((Nat.nth Nat.Prime k : ℕ) : ℝ) := by
  exact log_primorial_eq_theta_real (Nat.nth Nat.Prime k)

/-! ## Section 2 — Chebyshev's two-sided θ bound

We package the standard Chebyshev statement: there exist constants
`0 < c ≤ C` and `N₀ : ℕ` such that for every real `x ≥ N₀`,

```
  c · x ≤ θ(x) ≤ C · x.
```

We use `c < log 4` (any positive `c` strictly below `log 4` works) and
`C = log 4` (mathlib's upper bound).  The lower bound is `eventually`
on `ℕ` from `eventually_chebyshev_theta_two_mul_ge_const_mul_linear`,
which we transfer to real `x ≥ N₀` via floor monotonicity. -/

/-- **Named Prop**: the standard Chebyshev two-sided θ bound. -/
def ChebyshevTwoSidedLinear : Prop :=
  ∃ c C : ℝ, ∃ N₀ : ℕ,
    0 < c ∧ c ≤ C ∧
      ∀ x : ℝ, (N₀ : ℝ) ≤ x →
        c * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ C * x

/-- **Upper bound** (unconditional, no threshold): `θ(x) ≤ log 4 · x`
for `x ≥ 0`.  This is `Chebyshev.theta_le_log4_mul_x`. -/
theorem theta_upper_bound {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- **Numerical fact** used to pick a concrete lower constant. -/
theorem one_third_lt_log_four : (1 / 3 : ℝ) < Real.log 4 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
  linarith

/-- Auxiliary: for `x ≥ 2`, `⌊x⌋₊ ≥ 2`. -/
theorem two_le_floor {x : ℝ} (hx : 2 ≤ x) : 2 ≤ ⌊x⌋₊ := by
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have h : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  exact h

/-- Auxiliary: for real `x ≥ 1`, `⌊x⌋₊ : ℝ ≥ x / 2`.

(Proof: `⌊x⌋₊ ≥ x - 1`, and `x - 1 ≥ x / 2` iff `x ≥ 2`.  For
`1 ≤ x < 2`, `⌊x⌋₊ = 1 ≥ x / 2`.) -/
theorem floor_real_ge_half {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases hx2 : 2 ≤ x
  · -- Use ⌊x⌋₊ ≥ x - 1 ≥ x/2.
    have h_floor_ge : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
      have hxnn : (0 : ℝ) ≤ x := by linarith
      have h_lt := Nat.lt_floor_add_one x
      linarith
    linarith
  · -- 1 ≤ x < 2 ⇒ ⌊x⌋₊ = 1.
    have hx_lt_2 : x < 2 := lt_of_not_ge hx2
    have hx_nn : (0 : ℝ) ≤ x := by linarith
    have h_floor_one : ⌊x⌋₊ = 1 := by
      have h_le : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
      have h_lt : ⌊x⌋₊ < 2 := by
        have : x < ((2 : ℕ) : ℝ) := by exact_mod_cast hx_lt_2
        exact (Nat.floor_lt hx_nn).mpr this
      omega
    rw [h_floor_one]
    -- Goal: x / 2 ≤ 1.  Since x < 2.
    push_cast
    linarith

/-- **Eventual lower bound (ℕ-indexed)**: for any `0 < c < log 4`,
there exists `N₁ : ℕ` such that for every `n ≥ N₁`,
`c · n ≤ θ(2 * n)`.

This is exactly `eventually_chebyshev_theta_two_mul_ge_const_mul_linear`
unpacked. -/
theorem exists_chebyshev_lower_two_mul {c : ℝ}
    (_hc_pos : 0 < c) (hc_lt : c < Real.log 4) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      c * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ) := by
  have hCheb := Gdbh.eventually_chebyshev_theta_two_mul_ge_const_mul_linear hc_lt
  rw [Filter.eventually_atTop] at hCheb
  obtain ⟨N₁, hN₁⟩ := hCheb
  exact ⟨N₁, hN₁⟩

/-- **Transfer from `2n` (ℕ) to real `x ≥ N₀`**.

If `c · n ≤ θ(2n)` for all `n ≥ N₁`, then `(c / 4) · x ≤ θ(x)` for all
real `x ≥ max (2 * N₁) 2`.

Reason: at real `x`, let `n := ⌊x⌋₊ / 2`.  Then `2n ≤ ⌊x⌋₊ ≤ x`, so
by `theta_mono`, `θ(2n) ≤ θ(x)`.  Also `2n ≥ ⌊x⌋₊ - 1 ≥ x - 2 ≥ x/2`
for `x ≥ 4`, so `n ≥ x/4`. -/
theorem chebyshev_theta_real_lower {c : ℝ}
    (hc_pos : 0 < c)
    {N₁ : ℕ} (hN₁ : ∀ n : ℕ, N₁ ≤ n → c * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ))
    {x : ℝ} (hx : (max (2 * N₁ + 4) 4 : ℕ) ≤ x) :
    (c / 4) * x ≤ Chebyshev.theta x := by
  -- Setup: floor and half-floor.
  have hx4 : (4 : ℝ) ≤ x := by
    have h : (4 : ℕ) ≤ max (2 * N₁ + 4) 4 := le_max_right _ _
    have h_real : ((4 : ℕ) : ℝ) ≤ ((max (2 * N₁ + 4) 4 : ℕ) : ℝ) := by exact_mod_cast h
    have : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_cast
    linarith [hx, h_real]
  have hx_pos : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  set m : ℕ := ⌊x⌋₊ with hm_def
  have hm_le_x : (m : ℝ) ≤ x := by
    have h := Nat.floor_le hx_pos.le
    simpa [hm_def] using h
  have hm_ge : x - 1 < (m : ℝ) := by
    have h := Nat.lt_floor_add_one x
    -- h : x < ⌊x⌋₊ + 1
    linarith
  have hm_ge_4 : 4 ≤ m := by
    have h : (4 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx4)
    simpa [hm_def] using h
  set n : ℕ := m / 2 with hn_def
  have h2n_le_m : 2 * n ≤ m := by rw [hn_def]; omega
  have h2n_ge_pred : m - 1 ≤ 2 * n := by rw [hn_def]; omega
  have hn_ge_two : 2 ≤ n := by
    have : 4 / 2 ≤ m / 2 := Nat.div_le_div_right hm_ge_4
    have h4d2 : (4 : ℕ) / 2 = 2 := by norm_num
    simpa [hn_def, h4d2] using this
  -- Threshold: x ≥ 2 * N₁ + 4 ⇒ m ≥ 2 * N₁ + 3 ⇒ n ≥ N₁.
  have hx_thr : ((2 * N₁ + 4 : ℕ) : ℝ) ≤ x := by
    have h1 : (2 * N₁ + 4 : ℕ) ≤ max (2 * N₁ + 4) 4 := le_max_left _ _
    have h1r : ((2 * N₁ + 4 : ℕ) : ℝ) ≤ ((max (2 * N₁ + 4) 4 : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith [hx, h1r]
  have hm_ge_2N1_3 : 2 * N₁ + 3 ≤ m := by
    have h_real : ((2 * N₁ + 3 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have h_cast_add : ((2 * N₁ + 4 : ℕ) : ℝ) = (2 * N₁ + 4 : ℝ) := by
        push_cast; ring
      have h_cast_pred : ((2 * N₁ + 3 : ℕ) : ℝ) = (2 * N₁ + 3 : ℝ) := by
        push_cast; ring
      have h_xfact : (2 * N₁ + 4 : ℝ) ≤ x := by rw [← h_cast_add]; exact hx_thr
      rw [h_cast_pred]
      linarith [hm_ge]
    exact_mod_cast h_real
  have hn_ge_N1 : N₁ ≤ n := by
    have h_div : 2 * N₁ + 3 ≤ m := hm_ge_2N1_3
    have h_div_2 : (2 * N₁ + 3) / 2 ≤ m / 2 := Nat.div_le_div_right h_div
    have hN1_eq : (2 * N₁ + 3) / 2 = N₁ + 1 := by omega
    rw [hN1_eq] at h_div_2
    have : N₁ ≤ m / 2 := by omega
    exact this
  -- Apply the input bound.
  have hbound : c * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ) := hN₁ n hn_ge_N1
  -- Monotonicity: θ(2n) ≤ θ(x), since (2n : ℝ) ≤ m ≤ x.
  have h2n_real_le_x : ((2 * n : ℕ) : ℝ) ≤ x := by
    have h2n_real_le_m : ((2 * n : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast h2n_le_m
    linarith
  have h_theta_mono :
      Chebyshev.theta ((2 * n : ℕ) : ℝ) ≤ Chebyshev.theta x :=
    Chebyshev.theta_mono h2n_real_le_x
  -- Lower bound on (n : ℝ).
  -- 2n ≥ m - 1 ≥ x - 2 (since m ≥ x - 1, hence 2n ≥ m - 1 ≥ x - 2).
  have h2n_real_ge : (x - 2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    -- ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 since m ≥ 1.
    have hm_ge_1 : 1 ≤ m := by linarith
    have h_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have hsubr : ((m : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
        have := Nat.sub_add_cancel hm_ge_1
        exact_mod_cast this.symm
      linarith
    -- ((2 * n : ℕ) : ℝ) ≥ ((m - 1 : ℕ) : ℝ).
    have h_pred_le : ((m - 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast h2n_ge_pred
    rw [h_cast] at h_pred_le
    linarith
  -- For x ≥ 4: x - 2 ≥ x / 2, so 2n ≥ x / 2, so n ≥ x / 4.
  have hx_minus_two_ge_half : x / 2 ≤ x - 2 := by linarith
  have h2n_ge_half_x : x / 2 ≤ ((2 * n : ℕ) : ℝ) :=
    le_trans hx_minus_two_ge_half h2n_real_ge
  have hn_ge_quarter_x : x / 4 ≤ (n : ℝ) := by
    have h_cast2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [h_cast2n] at h2n_ge_half_x
    linarith
  -- Combine.
  have h_lb : (c / 4) * x ≤ c * (n : ℝ) := by
    have h_mul : c * (x / 4) ≤ c * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hn_ge_quarter_x hc_pos.le
    have h_eq : c * (x / 4) = (c / 4) * x := by ring
    linarith
  exact h_lb.trans (hbound.trans h_theta_mono)

/-- **Headline: Chebyshev's θ two-sided linear bound.**

There exist `0 < c ≤ C` and `N₀ : ℕ` such that for every `x ≥ N₀`,

```
  c · x ≤ θ(x) ≤ C · x.
```

We exhibit `c = (1/3) / 4 = 1/12`, `C = log 4`, and an explicit
`N₀`.  Closes `ChebyshevTwoSidedLinear`. -/
theorem chebyshevTwoSidedLinear_holds : ChebyshevTwoSidedLinear := by
  -- Lower constant.
  have hc_pos : (0 : ℝ) < 1 / 3 := by norm_num
  have hc_lt : (1 / 3 : ℝ) < Real.log 4 := one_third_lt_log_four
  obtain ⟨N₁, hN₁⟩ := exists_chebyshev_lower_two_mul hc_pos hc_lt
  -- Threshold.
  set N₀ : ℕ := max (2 * N₁ + 4) 4 with hN₀_def
  -- Pick c = 1/12, C = log 4.
  refine ⟨1 / 12, Real.log 4, N₀, by norm_num, ?_, ?_⟩
  · -- 1/12 ≤ log 4.
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
    linarith
  · intro x hx
    -- hx : (N₀ : ℝ) ≤ x.
    have hx_thr : ((max (2 * N₁ + 4) 4 : ℕ) : ℝ) ≤ x := by
      simpa [hN₀_def] using hx
    refine ⟨?_, ?_⟩
    · -- Lower bound.
      have h := chebyshev_theta_real_lower hc_pos hN₁ hx_thr
      -- h : (1 / 3) / 4 * x ≤ θ x.
      have h_eq : (1 / 3 : ℝ) / 4 = 1 / 12 := by norm_num
      rw [h_eq] at h
      exact h
    · -- Upper bound.
      have hx_pos : 0 ≤ x := by
        have h4 : (4 : ℕ) ≤ max (2 * N₁ + 4) 4 := le_max_right _ _
        have h4_r : ((4 : ℕ) : ℝ) ≤ ((max (2 * N₁ + 4) 4 : ℕ) : ℝ) := by
          exact_mod_cast h4
        have : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_cast
        linarith
      exact theta_upper_bound hx_pos

/-! ## Section 3 — Bridge: `S(p_k#) ≤ K · log log (p_k#)`

The headline bridge `S(p_k#) ≤ K · log log (p_k#)` is exactly the
content of `SingularSeriesPrimorialMertensBound`, closed in
P22-T7 (`Gdbh.PathCSingularSeriesPrimorialMertens`).

The closure uses Mertens-2 odd for the singular-series sum, together
with the Chebyshev linear lower bound on `log primorial` (which is
`log primorial k = θ(k)` from `log_primorial_eq_theta` chained with
`eventually_chebyshev_theta_two_mul_ge_const_mul_linear`), to go from
`S(p_k#) ≤ exp(B+3) · log k` to `S(p_k#) ≤ 2 exp(B+3) · log log p_k#`.

We re-expose the result here, marking it as P23-T2's bridge
deliverable. -/

/-- **Headline bridge P23-T2(4): `S(p_k#) ≤ K · log log p_k#`**.

For some absolute constant `K > 0` and threshold `N₀`,

```
  ∀ k ≥ N₀, singularSeries (primorial k) ≤ K · log log (primorial k).
```

Re-exposed from `PathCSingularSeriesPrimorialMertens` (P22-T7). -/
theorem singular_series_primorial_le_loglog_primorial :
    SingularSeriesPrimorialMertensBound :=
  singularSeriesPrimorialMertensBound_holds

/-- **Convenience unfolded form** for downstream consumers.

The form `S(p_k#) ≤ K · log log p_k#` with `primorialOdd k = primorial k`
unfolded. -/
theorem S_primorial_le_K_loglog_primorial :
    ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧
      ∀ k : ℕ, N₀ ≤ k →
        (Gdbh.PathCHardyLittlewoodForm.singularSeries (primorial k) : ℝ)
          ≤ K * Real.log (Real.log ((primorial k : ℕ) : ℝ)) := by
  obtain ⟨K, N₀, hK_pos, hbd⟩ := singularSeriesPrimorialMertensBound_holds
  refine ⟨K, N₀, hK_pos, ?_⟩
  intro k hk
  have h := hbd k hk
  -- h uses primorialOdd; unfold.
  unfold Gdbh.PathCSingularSeriesPrimorialMertens.primorialOdd at h
  exact h

/-! ## Section 4 — Auxiliary: `log p_k ≍ log log (p_k#)`

For downstream Erdős/Hardy–Littlewood arguments, we record the
asymptotic equivalence `log p_k ~ log log (p_k#)`.  Concretely, for
the `k`-th prime `p_k`, since `log p_k# = θ(p_k)` and `θ(p_k) ≍ p_k`,
we have `log(p_k#) ≍ p_k`, hence `log log (p_k#) ≍ log p_k`.

Below we record the cleanest concrete inequalities: an upper-bound
`log p_k ≤ log log (p_k#) + log log 4 ≤ 2 log log (p_k#)` for `p_k`
large.  The matching lower bound uses the Chebyshev upper θ bound:
`log(p_k#) = θ(p_k) ≤ (log 4) · p_k`, hence `log log (p_k#) ≤ log p_k
+ log log 4`. -/

/-- **Upper θ implies `log log p_k# ≤ log p_k + log log 4`**.

For `n ≥ 2` (so that `θ(n) > 0` and `log n > 0`), if we use the
Chebyshev upper bound `θ(n) ≤ log 4 · n`, then taking `log` on both
sides yields `log θ(n) ≤ log log 4 + log n`.  Combined with
`log θ(n) = log log(primorial n)`, we obtain

```
  log log (primorial n) ≤ log n + log log 4.
```

In words: `log log p_k# ≤ log p_k + (a small absolute constant)`. -/
theorem loglog_primorial_le_log_n_plus_const {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log ((primorial n : ℕ) : ℝ))
      ≤ Real.log (n : ℝ) + Real.log (Real.log 4) := by
  -- Cast.
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  -- θ(n) > 0 since n ≥ 2.
  have h_theta_pos : 0 < Chebyshev.theta (n : ℝ) := Chebyshev.theta_pos hn_real
  -- log primorial n = θ(n) > 0.
  have h_log_prim_eq : Real.log ((primorial n : ℕ) : ℝ) = Chebyshev.theta (n : ℝ) := by
    have := log_primorial_eq_theta n
    unfold theta at this
    exact this
  -- Upper bound: θ(n) ≤ log 4 · n.
  have h_upper : Chebyshev.theta (n : ℝ) ≤ Real.log 4 * (n : ℝ) :=
    theta_upper_bound (by linarith : (0 : ℝ) ≤ (n : ℝ))
  -- Take log.  We need both sides positive.
  -- log 4 > 0.
  have h_log4_pos : (0 : ℝ) < Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
    linarith
  have h_rhs_pos : (0 : ℝ) < Real.log 4 * (n : ℝ) := mul_pos h_log4_pos hn_pos
  -- log (θ(n)) ≤ log (log 4 * n).
  have h_log_le : Real.log (Chebyshev.theta (n : ℝ))
                    ≤ Real.log (Real.log 4 * (n : ℝ)) :=
    Real.log_le_log h_theta_pos h_upper
  -- log (log 4 * n) = log (log 4) + log n.
  have h_log_prod : Real.log (Real.log 4 * (n : ℝ))
                      = Real.log (Real.log 4) + Real.log (n : ℝ) :=
    Real.log_mul (ne_of_gt h_log4_pos) (ne_of_gt hn_pos)
  -- Substitute.
  rw [h_log_prim_eq]
  linarith [h_log_le, h_log_prod]

/-! ## Section 5 — Summary marker -/

/-- **P23-T2 summary marker** (no content theorem).

Deliverables (axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext`):

1. `theta` — alias for `Chebyshev.theta`.
2. `log_primorial_eq_theta` — `log (primorial n) = θ n`.
3. `log_primorial_nth_prime_eq_theta` — `log (p_k#) = θ(p_k)`.
4. `theta_upper_bound` — `θ(x) ≤ log 4 · x` for `x ≥ 0`.
5. `chebyshevTwoSidedLinear_holds` — `∃ 0 < c ≤ C, ∃ N₀, ∀ x ≥ N₀,
   c · x ≤ θ(x) ≤ C · x`.
6. `singular_series_primorial_le_loglog_primorial` — re-export of
   `SingularSeriesPrimorialMertensBound` from P22-T7, exactly
   `S(p_k#) ≤ K · log log p_k#`.
7. `loglog_primorial_le_log_n_plus_const` — `log log p_k# ≤ log p_k +
   log log 4` (consequence of Chebyshev upper). -/
theorem pathC_p23_t2_summary : True := trivial

end PathCChebyshevPrimorial
end Gdbh

/-! ## Axiom audit -/

#print axioms Gdbh.PathCChebyshevPrimorial.log_primorial_eq_theta
#print axioms Gdbh.PathCChebyshevPrimorial.chebyshevTwoSidedLinear_holds
#print axioms Gdbh.PathCChebyshevPrimorial.singular_series_primorial_le_loglog_primorial
#print axioms Gdbh.PathCChebyshevPrimorial.loglog_primorial_le_log_n_plus_const
