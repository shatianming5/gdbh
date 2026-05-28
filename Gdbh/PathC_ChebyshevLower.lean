/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P8-T1 (Phase 8 / Path C closure — Chebyshev prime-counting lower bound)
-/
import Gdbh.PathC_PrimesSumsetDensity
import Gdbh.VonMangoldtGoldbach

/-!
# Path C — Unconditional Chebyshev prime-counting lower bound

This file is the **P8-T1 deliverable** in Phase 8 (Path C closure). It
discharges the `ChebyshevPrimeLowerBound` open `Prop` from
`Gdbh/PathC_PrimesSumsetDensity.lean` *unconditionally*.

## Statement

The named open `Prop` from `PathC_PrimesSumsetDensity` is

```
def ChebyshevPrimeLowerBound : Prop :=
  ∃ c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ ∀ n : ℕ, N₀ ≤ n →
    c * (n : ℝ) / Real.log (n : ℝ) ≤ (Nat.primeCounting n : ℝ)
```

The main theorem of this file, `chebyshevPrimeLowerBound_holds`, exhibits
an explicit `c > 0` and `N₀ : ℕ` for which this holds for every `n ≥ N₀`.

## Strategy

The repository already contains the *hard* Erdős-style work in
`Gdbh/VonMangoldtGoldbach.lean`:

* `chebyshev_theta_linear_lower_bound` — for `n ≥ 4`,
  `n · log 4 − log n − √(2n) · log(2n) < θ(2n)`.
* `eventually_chebyshev_primeCounting_two_mul_ge_const_mul_div_log` —
  for any `0 < c < log 2`, eventually
  `c · 2n / log(2n) ≤ π(2n)`.

The second lemma is exactly Chebyshev's lower bound on the
*subsequence* `(2n)`.  To pass to arbitrary `m ≥ N₀`, we use
monotonicity of `Nat.primeCounting`: for any `m`, with `k := m / 2`,
we have `2k ≥ m − 1`, hence

```
  π(m) ≥ π(2k) ≥ c₀ · 2k / log(2k) ≥ c₀ · (m − 1) / log m
        ≥ (c₀ / 2) · m / log m
```

for all `m` large enough that `m − 1 ≥ m / 2`, i.e., for `m ≥ 2`.

Choosing `c₀ = 1/2 < log 2` and `c := c₀ / 2 = 1/4`, we obtain the
quoted bound.

## Axiom budget

Every lemma below is axiom-clean: the only axioms transitively used are
`Classical.choice`, `Quot.sound`, `propext`.  We rely solely on
mathlib's `Mathlib.NumberTheory.Chebyshev`, `Mathlib.NumberTheory.PrimeCounting`,
and the existing repository theorems in `Gdbh.VonMangoldtGoldbach`.

## Main results

* `chebyshev_primeCounting_lower_bound_at_even` — transfer of the
  `2n`-subsequence bound to the actual statement at the natural number
  `2n`.
* `chebyshev_primeCounting_lower_bound_general` — extension to all
  `m ≥ N₀`, with explicit constants and quantitative dependence on
  `c₀ < log 2`.
* `chebyshevPrimeLowerBound_holds` — the headline:
  `Gdbh.PathCPrimesSumsetDensity.ChebyshevPrimeLowerBound` holds
  unconditionally.
-/

namespace Gdbh
namespace PathCChebyshevLower

open Gdbh
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound)
open Filter Topology

/-! ## Section 1 — Quantitative single-step lemma

For a fixed `0 < c₀ < log 2`, eventually the inequality
`c₀ · 2n / log(2n) ≤ π(2n)` holds.  We restate this from
`VonMangoldtGoldbach` for proximity. -/

/-- The mathlib/repo input lemma: for `0 < c₀ < log 2`, eventually
`c₀ · 2n / log(2n) ≤ π(2n)`.  This is exactly
`eventually_chebyshev_primeCounting_two_mul_ge_const_mul_div_log`. -/
theorem eventually_subseq_bound {c₀ : ℝ} (hc₀_pos : 0 < c₀)
    (hc₀_lt : c₀ < Real.log 2) :
    ∀ᶠ n : ℕ in atTop,
      c₀ * ((2 * n : ℕ) : ℝ) / Real.log ((2 * n : ℕ) : ℝ) ≤
        (Nat.primeCounting (2 * n) : ℝ) :=
  Gdbh.eventually_chebyshev_primeCounting_two_mul_ge_const_mul_div_log
    hc₀_pos hc₀_lt

/-! ## Section 2 — Transfer to arbitrary `m`

For any `m ≥ N₀` (large enough), setting `k := m / 2`, the bound at
`2k` (which is the existing subsequence bound) transfers to a bound
at `m` via monotonicity. -/

/-- Auxiliary numerical bound: for `m ≥ 2`, `(m : ℝ) - 1 ≥ (m : ℝ) / 2`. -/
theorem half_le_pred {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) / 2 ≤ ((m : ℝ) - 1) := by
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- Auxiliary numerical bound: for `m ≥ 1`, `(m - 1 : ℕ) = m - 1` as reals. -/
theorem sub_one_real {m : ℕ} (hm : 1 ≤ m) :
    ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
  have : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
    have hm' : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
    exact_mod_cast hm'
  linarith

/-- For `m ≥ 1`, `2 * (m / 2) ≥ m - 1`. -/
theorem two_div_two_ge_pred (m : ℕ) :
    m - 1 ≤ 2 * (m / 2) := by
  -- The Euclidean division: m = 2 * (m/2) + (m % 2), and m % 2 ≤ 1.
  have h := Nat.div_add_mod m 2
  -- m = 2 * (m/2) + m%2
  have hmod : m % 2 ≤ 1 := by
    have : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  omega

/-- For `m ≥ 1`, `2 * (m / 2) ≤ m`. -/
theorem two_div_two_le (m : ℕ) :
    2 * (m / 2) ≤ m := by
  have h := Nat.div_add_mod m 2
  omega

/-- **Quantitative transfer step.**

If `m ≥ 4` (so that `m / 2 ≥ 2`, ensuring `log(2 * (m/2)) > 0`), and
`c₀ · 2k / log(2k) ≤ π(2k)` holds at `k := m / 2`, then

```
  (c₀ / 2) · m / log m ≤ π(m).
```
-/
theorem transfer_to_general
    {c₀ : ℝ} (hc₀_pos : 0 < c₀)
    {m : ℕ} (hm : 4 ≤ m)
    (hbound :
      c₀ * ((2 * (m / 2) : ℕ) : ℝ) / Real.log ((2 * (m / 2) : ℕ) : ℝ) ≤
        (Nat.primeCounting (2 * (m / 2)) : ℝ)) :
    (c₀ / 2) * (m : ℝ) / Real.log (m : ℝ) ≤
      (Nat.primeCounting m : ℝ) := by
  -- Setup
  set k : ℕ := m / 2 with hk_def
  have hk_ge_two : 2 ≤ k := by
    have : 4 / 2 ≤ m / 2 := Nat.div_le_div_right hm
    simpa [hk_def] using this
  have hk_pos : 0 < k := lt_of_lt_of_le (by norm_num) hk_ge_two
  have h2k_pos : 0 < 2 * k := by positivity
  have h2k_ge_two : 2 ≤ 2 * k := by linarith [hk_ge_two]
  have h2k_le_m : 2 * k ≤ m := by simpa [hk_def] using two_div_two_le m
  have hm_ge_one : 1 ≤ m := by linarith
  have h2k_ge_pred : m - 1 ≤ 2 * k := by simpa [hk_def] using two_div_two_ge_pred m
  -- Cast facts
  have h2k_real_le_m : ((2 * k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2k_le_m
  have h2k_real_pos : 0 < ((2 * k : ℕ) : ℝ) := by exact_mod_cast h2k_pos
  have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 4) hm)
  -- The 2k-real cast: ((2*k:ℕ):ℝ) ≥ m - 1
  have h2k_real_ge_pred : (m : ℝ) - 1 ≤ ((2 * k : ℕ) : ℝ) := by
    have : ((m - 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast h2k_ge_pred
    have hcast := sub_one_real hm_ge_one
    linarith [hcast, this]
  -- m/2 ≤ 2k as reals
  have h2k_real_ge_half : (m : ℝ) / 2 ≤ ((2 * k : ℕ) : ℝ) := by
    have hm_ge_two : 2 ≤ m := by linarith
    have := half_le_pred (m := m) hm_ge_two
    linarith [h2k_real_ge_pred]
  -- log positivity
  have h2k_gt_one : 1 < ((2 * k : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ 2 * k := h2k_ge_two
    have : (2 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hm_gt_one : 1 < (m : ℝ) := by
    have : (2 : ℕ) ≤ m := by linarith
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  have hlog_2k_pos : 0 < Real.log ((2 * k : ℕ) : ℝ) := Real.log_pos h2k_gt_one
  have hlog_m_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt_one
  -- log(2k) ≤ log m  (since 2k ≤ m)
  have hlog_2k_le_m : Real.log ((2 * k : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log h2k_real_pos h2k_real_le_m
  -- Monotonicity: π(2k) ≤ π(m)
  have hπ_mono : (Nat.primeCounting (2 * k) : ℝ) ≤ (Nat.primeCounting m : ℝ) := by
    have hnat : Nat.primeCounting (2 * k) ≤ Nat.primeCounting m :=
      Nat.monotone_primeCounting h2k_le_m
    exact_mod_cast hnat
  -- Goal: (c₀ / 2) * m / log m ≤ π(m)
  -- We chain: (c₀ / 2) * m / log m ≤ c₀ * (m/2) / log m ≤ c₀ * 2k / log m
  --        ≤ c₀ * 2k / log(2k) ≤ π(2k) ≤ π(m)
  have step1 :
      (c₀ / 2) * (m : ℝ) / Real.log (m : ℝ) =
        c₀ * ((m : ℝ) / 2) / Real.log (m : ℝ) := by ring
  have step2 :
      c₀ * ((m : ℝ) / 2) / Real.log (m : ℝ) ≤
        c₀ * ((2 * k : ℕ) : ℝ) / Real.log (m : ℝ) := by
    apply div_le_div_of_nonneg_right _ hlog_m_pos.le
    exact mul_le_mul_of_nonneg_left h2k_real_ge_half hc₀_pos.le
  have hnum_nonneg : 0 ≤ c₀ * ((2 * k : ℕ) : ℝ) :=
    mul_nonneg hc₀_pos.le h2k_real_pos.le
  have step3 :
      c₀ * ((2 * k : ℕ) : ℝ) / Real.log (m : ℝ) ≤
        c₀ * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hlog_2k_pos hlog_2k_le_m
  -- chain
  have hchain :
      (c₀ / 2) * (m : ℝ) / Real.log (m : ℝ) ≤
        c₀ * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k : ℕ) : ℝ) := by
    rw [step1]; exact step2.trans step3
  exact hchain.trans (hbound.trans hπ_mono)

/-! ## Section 3 — The unconditional eventual bound

Combining `eventually_subseq_bound` with the transfer step yields the
unconditional statement at any single `c < log 2 / 2`. -/

/-- **Eventual unconditional Chebyshev lower bound.**

For any `c` with `0 < c < (log 2) / 2`, there exists `N₀` such that for
every `m ≥ N₀`,

```
  c · m / log m ≤ π m.
```
-/
theorem eventually_primeCounting_ge {c : ℝ}
    (hc_pos : 0 < c) (hc_lt : c < Real.log 2 / 2) :
    ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m →
      c * (m : ℝ) / Real.log (m : ℝ) ≤ (Nat.primeCounting m : ℝ) := by
  -- Set c₀ = 2c, so 0 < c₀ < log 2.
  set c₀ : ℝ := 2 * c with hc₀_def
  have hc₀_pos : 0 < c₀ := by positivity
  have hc₀_lt : c₀ < Real.log 2 := by
    have : 2 * c < 2 * (Real.log 2 / 2) := by linarith
    have h2 : 2 * (Real.log 2 / 2) = Real.log 2 := by ring
    linarith [h2 ▸ this]
  -- The subsequence bound is eventual.
  have hsub := eventually_subseq_bound (c₀ := c₀) hc₀_pos hc₀_lt
  -- Find N from the eventual filter.
  rw [Filter.eventually_atTop] at hsub
  obtain ⟨N, hN⟩ := hsub
  -- Choose N₀ = max(2N + 1, 4) so that for m ≥ N₀, we have m/2 ≥ N and m ≥ 4.
  refine ⟨2 * N + 4, ?_⟩
  intro m hm_ge
  have hm_ge_4 : 4 ≤ m := by linarith
  have hk_ge_N : N ≤ m / 2 := by
    have h1 : 2 * N + 4 ≤ m := hm_ge
    have : 2 * N ≤ m := by linarith
    have h2 : (2 * N) / 2 ≤ m / 2 := Nat.div_le_div_right this
    have h3 : (2 * N) / 2 = N := by
      rw [Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
    linarith [h2, h3 ▸ le_refl ((2 * N) / 2)]
  have hbd := hN (m / 2) hk_ge_N
  -- Note `2 * (m / 2)` appears explicitly: `hbd` uses the variable name `n = m/2`.
  have hbd' :
      c₀ * ((2 * (m / 2) : ℕ) : ℝ) / Real.log ((2 * (m / 2) : ℕ) : ℝ) ≤
        (Nat.primeCounting (2 * (m / 2)) : ℝ) := hbd
  -- Apply the transfer step.
  have htransfer := transfer_to_general (c₀ := c₀) hc₀_pos (m := m) hm_ge_4 hbd'
  -- htransfer: (c₀ / 2) * m / log m ≤ π m.
  -- And c₀ / 2 = c.
  have hc_eq : c₀ / 2 = c := by rw [hc₀_def]; ring
  rw [hc_eq] at htransfer
  exact htransfer

/-! ## Section 4 — Headline theorem

We pick a concrete constant `c = 1/4` (since `log 2 / 2 ≈ 0.3466 > 1/4`)
and discharge `ChebyshevPrimeLowerBound`. -/

/-- Numerical fact: `1/4 < log 2 / 2`, since `log 2 > 1/2`. -/
theorem one_quarter_lt_half_log_two : (1 : ℝ) / 4 < Real.log 2 / 2 := by
  -- We use the standard mathlib bound `Real.log_two_gt_d9 : 0.6931471803 < log 2`.
  -- A safer route: log 2 > 1/2.  Since log 2 = log (4/2) and 1/2 = log √e, this
  -- requires only `Real.exp (1/2) < 2`, i.e., `√e < 2`.  Cleanest in mathlib:
  -- use `Real.log_two_gt_d9` if available, else use `Real.exp_one_lt_d9`.
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

/-- **Headline P8-T1 result: `ChebyshevPrimeLowerBound` holds.**

Unconditionally, there exists `c > 0` and `N₀ : ℕ` such that for every
`n ≥ N₀`, `c · n / log n ≤ π(n)`.  We exhibit `c = 1/4` and rely on
`eventually_primeCounting_ge` for an explicit `N₀`. -/
theorem chebyshevPrimeLowerBound_holds : ChebyshevPrimeLowerBound := by
  -- Pick c = 1/4 < log 2 / 2.
  have hc_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have hc_lt : (1 : ℝ) / 4 < Real.log 2 / 2 := one_quarter_lt_half_log_two
  obtain ⟨N₀, hN₀⟩ := eventually_primeCounting_ge hc_pos hc_lt
  refine ⟨1 / 4, N₀, hc_pos, ?_⟩
  intro n hn
  exact hN₀ n hn

end PathCChebyshevLower
end Gdbh
