/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T7 (Phase 22 / Path C — Mertens-3 for primorials specifically.)
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Gdbh.PathC_HardyLittlewoodForm
import Gdbh.PathC_SingularSeriesMertens
import Gdbh.PathC_SingularSeriesLogNBound
import Gdbh.PathC_MertensSecondTwoSided
import Gdbh.PathC_MertensSecondUpper
import Gdbh.VonMangoldtGoldbach

/-!
# Path C — P22-T7: Singular series upper bound on primorials, `S(p_k#) ≤ K · log log p_k#`

## Mission

The pointwise bound `S(n) ≤ K · log log n` is **false** for arbitrary
`n` (the odd prime divisors of `n` can form an arbitrary subset of
primes ≤ `n`, saturating Mertens-2 only along primorials).

For **primorials** `n = p_k#` (the product of all primes ≤ `k`), the
bound is mathematically true and provable.  This file proves

```
∃ K > 0, ∃ N₀ : ℕ, ∀ k ≥ N₀,
  singularSeries (primorial k) ≤ K · log log (primorial k) .
```

axiom-clean from existing infrastructure.

## Proof strategy

For `n = primorial k`, the prime divisors of `n` in `[3, n]` are
exactly the odd primes ≤ `k`.  Therefore by reusing the tight
Mertens-2 decomposition (`PathC_SingularSeriesLogNBound`) at the
*smaller* upper bound `k`,

```
log S(primorial k)  =  Σ_{3 ≤ p ≤ k, p prime} log((p-1)/(p-2))
                    ≤  Σ_{3 ≤ p ≤ k, p prime} (1/p + 6/p²)        (tight per-prime)
                    ≤  (log log k + B)  +  6 · (1/2)              (Mertens-2 odd + telescoping)
                    =  log log k + B + 3 .
```

Exponentiating: `S(primorial k) ≤ exp(B+3) · log k`.

By Chebyshev's linear lower bound on `θ`
(`eventually_chebyshev_theta_two_mul_ge_const_mul_linear`),
`Chebyshev.theta (2n) ≥ n` for `n` large.  Combined with
`theta_eq_log_primorial`, this gives `log primorial (2n) ≥ n`, hence
by monotonicity `log primorial k ≥ k/4` for `k` large enough.

Therefore `log log primorial k ≥ log(k/4) = log k - log 4`, which is at
least `(1/2) log k` for `k ≥ 16`.  Combining:

```
S(primorial k) ≤ exp(B+3) · log k ≤ 2 exp(B+3) · log log primorial k .
```

We take `K = 2 · exp(B + 3)`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCSingularSeriesPrimorialMertens

open Real Finset Filter
open Gdbh.PathCMertensSecondTwoSided
  (MertensSecondUpperBoundOdd mertensSecondUpperBoundOdd_holds)
open Gdbh.PathCMertensSecondUpper (sum_one_div_sq_prime_le_half)
open Gdbh.PathCSingularSeriesLogNBound (log_oddFactor_le_split)
open Gdbh.PathCHardyLittlewoodForm
  (singularSeries singularSeries_pos singularSeries_factor_pos)

/-! ## Section 1 — Primorial-odd definition and the named Prop -/

/-- **`primorialOdd k`** — the primorial of `k`, i.e., the product of
all primes ≤ `k`.  This is mathlib's `Nat.primorial`, the standard
primorial function, exposed under the name `primorialOdd` for the
present P22-T7 deliverable.

Note: despite the name "odd", the standard primorial *includes* `p = 2`
when `k ≥ 2`; the "odd" in the predicate refers to the fact that the
*singular series* `S(primorial k)` only sums over odd prime divisors
(`p ≥ 3`), not to the primorial itself. -/
def primorialOdd (k : ℕ) : ℕ := primorial k

/-- **Named Prop**: the primorial-specific upper bound on the Goldbach
singular series.

```
∃ K > 0, ∃ N₀ : ℕ, ∀ k ≥ N₀,
  singularSeries (primorialOdd k) ≤ K · log log (primorialOdd k) .
``` -/
def SingularSeriesPrimorialMertensBound : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧
    ∀ k : ℕ, N₀ ≤ k →
      (singularSeries (primorialOdd k) : ℝ)
        ≤ K * Real.log (Real.log (primorialOdd k : ℝ))

/-! ## Section 2 — Prime divisors of `primorial k` are exactly primes ≤ k

The filter `(Icc 3 (primorial k)).filter (Prime ∧ p ∣ primorial k)`
equals `(Icc 3 k).filter Prime` for `k ≥ 2`. -/

/-- The singular-series filter at `primorial k` collapses
to the filter of primes in `[3, k]`. -/
lemma primorial_singularSeries_filter_eq (k : ℕ) :
    ((Finset.Icc 3 (primorial k)).filter
        (fun p => Nat.Prime p ∧ p ∣ primorial k))
      = (Finset.Icc 3 k).filter Nat.Prime := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp3, _⟩, hpp, hpdvd⟩
    have hpk : p ≤ k := (Nat.Prime.dvd_primorial_iff hpp).mp hpdvd
    exact ⟨⟨hp3, hpk⟩, hpp⟩
  · rintro ⟨⟨hp3, hpk⟩, hpp⟩
    have hk_le : k ≤ primorial k := le_primorial_self
    have hp_dvd : p ∣ primorial k := (Nat.Prime.dvd_primorial_iff hpp).mpr hpk
    exact ⟨⟨hp3, hpk.trans hk_le⟩, hpp, hp_dvd⟩

/-- `singularSeries (primorial k)` is the product over primes in `[3, k]`. -/
lemma singularSeries_primorial_eq (k : ℕ) :
    singularSeries (primorial k)
      = ∏ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  unfold singularSeries
  rw [primorial_singularSeries_filter_eq k]

/-! ## Section 3 — Log sum bound at primorials

`log S(primorial k) ≤ log log k + B + 3` for `k ≥ max z₀ 3`. -/

/-- The log of `singularSeries (primorial k)` as a sum. -/
lemma log_singularSeries_primorial_eq_sum (k : ℕ) :
    Real.log (singularSeries (primorial k))
      = ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
          Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [singularSeries_primorial_eq k]
  rw [Real.log_prod]
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact ne_of_gt (singularSeries_factor_pos hp3)

/-- Sum upper bound: `log S(primorial k) ≤ Σ 1/p + 6 Σ 1/p²` over
primes in `[3, k]`. -/
lemma log_singularSeries_primorial_le_sum_split (k : ℕ) :
    Real.log (singularSeries (primorial k))
      ≤ (∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          + 6 * ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
  classical
  rw [log_singularSeries_primorial_eq_sum k]
  -- Termwise bound: log((p-1)/(p-2)) ≤ 1/p + 6/p² via `log_oddFactor_le_split`.
  have h_termwise :
      ∀ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
        Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2))
          ≤ (1 : ℝ) / (p : ℝ) + 6 / (p : ℝ)^2 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    have h := log_oddFactor_le_split (p := p) hp3
    unfold Gdbh.goldbachOddPrimeLocalFactor at h
    exact h
  have h_sum_le :
      ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
          Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
            ((1 : ℝ) / (p : ℝ) + 6 / (p : ℝ)^2) :=
    Finset.sum_le_sum h_termwise
  have h_rhs_split :
      ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime,
          ((1 : ℝ) / (p : ℝ) + 6 / (p : ℝ)^2)
        = (∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            + 6 * ∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  linarith [h_sum_le, h_rhs_split]

/-- **Headline bound on `log S(primorial k)`**.  For `k ≥ max z₀ 3`,
where `(B, z₀)` are the constants from `mertensSecondUpperBoundOdd_holds`,

```
log S(primorial k) ≤ log log k + B + 3 .
``` -/
lemma log_singularSeries_primorial_le_log_log_k_const {B : ℝ} {z₀ k : ℕ}
    (hM2 : ∀ z : ℕ, z₀ ≤ z →
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B)
    (hk_z₀ : z₀ ≤ k) (hk_3 : 3 ≤ k) :
    Real.log (singularSeries (primorial k))
      ≤ Real.log (Real.log (k : ℝ)) + B + 3 := by
  have h_step1 := log_singularSeries_primorial_le_sum_split k
  have h_step2a : (∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                    ≤ Real.log (Real.log (k : ℝ)) + B := hM2 k hk_z₀
  have h_step2b : (∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
                    ≤ 1 / 2 := sum_one_div_sq_prime_le_half k hk_3
  have h_6_le : 6 * (∑ p ∈ (Finset.Icc 3 k).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
                  ≤ 6 * (1 / 2) := by
    have := mul_le_mul_of_nonneg_left h_step2b (by norm_num : (0 : ℝ) ≤ 6)
    linarith
  linarith [h_step1, h_step2a, h_6_le]

/-! ## Section 4 — Exponentiating: `S(primorial k) ≤ exp(B+3) · log k` -/

/-- Identity `exp(log log k + (B+3)) = exp(B+3) · log k` for `k ≥ 3`. -/
lemma exp_log_log_k_add_const_eq {k : ℕ} (hk : 3 ≤ k) (C : ℝ) :
    Real.exp (Real.log (Real.log (k : ℝ)) + C)
      = Real.exp C * Real.log (k : ℝ) := by
  have hk_real : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_gt_one : (1 : ℝ) < (k : ℝ) := by linarith
  have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_gt_one
  rw [Real.exp_add, Real.exp_log hlogk_pos]
  ring

/-- **Multiplicative bound on `singularSeries (primorial k)`**.

For `k ≥ max z₀ 3`, `singularSeries (primorial k) ≤ exp(B+3) · log k`. -/
lemma singularSeries_primorial_le_const_mul_log_k {B : ℝ} {z₀ k : ℕ}
    (hM2 : ∀ z : ℕ, z₀ ≤ z →
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B)
    (hk_z₀ : z₀ ≤ k) (hk_3 : 3 ≤ k) :
    singularSeries (primorial k) ≤ Real.exp (B + 3) * Real.log (k : ℝ) := by
  have h_log_S_le := log_singularSeries_primorial_le_log_log_k_const hM2 hk_z₀ hk_3
  have h_S_pos : 0 < singularSeries (primorial k) := singularSeries_pos _
  have h_exp_mono :
      Real.exp (Real.log (singularSeries (primorial k)))
        ≤ Real.exp (Real.log (Real.log (k : ℝ)) + B + 3) :=
    Real.exp_le_exp.mpr h_log_S_le
  have h_exp_log : Real.exp (Real.log (singularSeries (primorial k)))
                    = singularSeries (primorial k) := Real.exp_log h_S_pos
  have h_rearrange : Real.log (Real.log (k : ℝ)) + B + 3
                      = Real.log (Real.log (k : ℝ)) + (B + 3) := by ring
  rw [h_rearrange] at h_exp_mono
  rw [exp_log_log_k_add_const_eq hk_3 (B + 3)] at h_exp_mono
  rw [h_exp_log] at h_exp_mono
  exact h_exp_mono

/-! ## Section 5 — Chebyshev linear lower bound on `log primorial k`

From `eventually_chebyshev_theta_two_mul_ge_const_mul_linear` (with
`c = 1 < log 4`), there is `N₁` such that for all `n ≥ N₁`,
`n ≤ θ(2n) = log primorial (2n)`.

By monotonicity of `primorial`, this extends to all `k ≥ 2N₁`:
`log primorial k ≥ ⌊k/2⌋ ≥ (k - 1) / 2`. -/

/-- **Extraction of the linear Chebyshev lower bound on θ**.

There exists `N₁ : ℕ` such that for every `n ≥ N₁`,
`(n : ℝ) ≤ log (primorial (2 * n))`. -/
lemma exists_linear_lower_bound_log_primorial_two_mul :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      (n : ℝ) ≤ Real.log (primorial (2 * n) : ℝ) := by
  -- Take c = 1 < log 4 ≈ 1.386.
  have hc_lt : (1 : ℝ) < Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
    linarith
  have hCheb := Gdbh.eventually_chebyshev_theta_two_mul_ge_const_mul_linear
    (c := (1 : ℝ)) hc_lt
  rw [Filter.eventually_atTop] at hCheb
  obtain ⟨N₁, hN₁⟩ := hCheb
  refine ⟨N₁, ?_⟩
  intro n hn
  have h := hN₁ n hn
  -- h : 1 * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ).
  -- Rewrite via theta_eq_log_primorial.
  have h_theta_eq :
      Chebyshev.theta ((2 * n : ℕ) : ℝ) = Real.log ((primorial (2 * n) : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial]
    -- ⌊((2 * n : ℕ) : ℝ)⌋₊ = 2 * n
    have h_floor : ⌊((2 * n : ℕ) : ℝ)⌋₊ = 2 * n := Nat.floor_natCast (2 * n)
    rw [h_floor]
  rw [h_theta_eq] at h
  have h_cast : ((primorial (2 * n) : ℕ) : ℝ) = (primorial (2 * n) : ℝ) := by norm_cast
  rw [h_cast] at h
  linarith

/-- **Concrete linear lower bound on `log primorial k`** (even `k`).

For `k ≥ 2 N₁`, `log primorial k ≥ k / 2 - 1`. -/
lemma log_primorial_ge_linear_aux {N₁ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n → (n : ℝ) ≤ Real.log (primorial (2 * n) : ℝ))
    {k : ℕ} (hk : 2 * N₁ ≤ k) :
    (k : ℝ) / 2 - 1 ≤ Real.log (primorial k : ℝ) := by
  -- Take m = k / 2.  Then 2m ∈ {k-1, k}, and `m ≥ N₁`.
  set m : ℕ := k / 2 with hm_def
  have hm_N₁ : N₁ ≤ m := by
    have h1 : 2 * N₁ ≤ k := hk
    have h2 : 2 * N₁ / 2 ≤ k / 2 := Nat.div_le_div_right h1
    have h3 : 2 * N₁ / 2 = N₁ := by
      exact Nat.mul_div_cancel_left N₁ (by norm_num : (0:ℕ) < 2)
    linarith [h2, h3 ▸ le_refl ((2 * N₁) / 2)]
  -- log primorial (2 * m) ≥ m.
  have h_2m := hN₁ m hm_N₁
  -- 2 * m ≤ k (since k / 2 * 2 ≤ k).
  have h_2m_le_k : 2 * m ≤ k := by
    rw [hm_def]
    omega
  -- primorial is monotone, so log primorial k ≥ log primorial (2 * m).
  have h_prim_mono : primorial (2 * m) ≤ primorial k := primorial_mono h_2m_le_k
  have h_prim_pos_2m : (0 : ℝ) < (primorial (2 * m) : ℝ) := by
    have := primorial_pos (2 * m); exact_mod_cast this
  have h_log_mono : Real.log (primorial (2 * m) : ℝ) ≤ Real.log (primorial k : ℝ) := by
    have h_cast : (primorial (2 * m) : ℝ) ≤ (primorial k : ℝ) := by exact_mod_cast h_prim_mono
    exact Real.log_le_log h_prim_pos_2m h_cast
  -- Combine.
  have h_chain : (m : ℝ) ≤ Real.log (primorial k : ℝ) := le_trans h_2m h_log_mono
  -- m = k / 2, so (m : ℝ) ≥ k / 2 - 1.
  have h_m_real : ((k : ℝ) - 1) / 2 ≤ (m : ℝ) := by
    -- k = 2 * (k / 2) + k % 2, where k % 2 ∈ {0, 1}.
    have h_div : k = 2 * m + k % 2 := by rw [hm_def]; omega
    have h_mod : k % 2 < 2 := Nat.mod_lt k (by norm_num : 0 < 2)
    have h_mod_le_1 : k % 2 ≤ 1 := by omega
    have h_mod_real : ((k % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h_mod_le_1
    have h_div_real : (k : ℝ) = 2 * (m : ℝ) + ((k % 2 : ℕ) : ℝ) := by exact_mod_cast h_div
    linarith [h_div_real, h_mod_real]
  have h_aux : ((k : ℝ) - 1) / 2 = (k : ℝ) / 2 - 1 / 2 := by ring
  rw [h_aux] at h_m_real
  linarith [h_chain, h_m_real]

/-! ## Section 6 — Lower bound on `log log primorial k` -/

/-- For `k ≥ 16` with `k / 2 - 1 ≤ log primorial k`,
`(1/2) log k ≤ log log primorial k`. -/
lemma log_log_primorial_ge_half_log_k_aux {k : ℕ}
    (hk16 : 16 ≤ k)
    (h_lin : (k : ℝ) / 2 - 1 ≤ Real.log (primorial k : ℝ)) :
    (1 / 2 : ℝ) * Real.log (k : ℝ) ≤ Real.log (Real.log (primorial k : ℝ)) := by
  have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16
  -- k/2 - 1 ≥ k/4 since k ≥ 4 (i.e., k/2 ≥ 2 ≥ 1, so k/2 - 1 ≥ k/2 - k/4 = k/4).
  -- Actually: k/2 - 1 ≥ k/4 iff k/4 ≥ 1 iff k ≥ 4.
  have h_lower : (k : ℝ) / 4 ≤ (k : ℝ) / 2 - 1 := by linarith
  have h_log_primorial_ge : (k : ℝ) / 4 ≤ Real.log (primorial k : ℝ) :=
    le_trans h_lower h_lin
  -- log primorial k ≥ k/4 > 0 for k ≥ 16, so log log primorial k is well-defined.
  have h_kf_pos : (0 : ℝ) < (k : ℝ) / 4 := by linarith
  -- log monotone: log log primorial k ≥ log (k / 4) = log k - log 4.
  have h_log_mono : Real.log ((k : ℝ) / 4) ≤ Real.log (Real.log (primorial k : ℝ)) :=
    Real.log_le_log h_kf_pos h_log_primorial_ge
  -- log (k / 4) = log k - log 4.
  have h_log_div : Real.log ((k : ℝ) / 4) = Real.log (k : ℝ) - Real.log 4 := by
    rw [Real.log_div (by linarith : (k : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  -- For k ≥ 16, log k ≥ log 16 = 4 log 2 ≥ 2 log 4 (since log 16 = 2 log 4).
  have h_log_k_ge : 2 * Real.log 4 ≤ Real.log (k : ℝ) := by
    have h_log_mono' : Real.log 16 ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) hk_real
    have h_log_16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
      have h1 : (16 : ℝ) = 4 ^ (2 : ℕ) := by norm_num
      rw [h1, Real.log_pow]; ring
    linarith
  -- Conclude: log k - log 4 ≥ log k / 2.
  -- (log k - log 4) - log k / 2 = (1/2) log k - log 4 ≥ (1/2) · 2 log 4 - log 4 = 0.
  have h_target : Real.log (k : ℝ) - Real.log 4 ≥ (1 / 2 : ℝ) * Real.log (k : ℝ) := by
    linarith [h_log_k_ge]
  linarith [h_log_mono, h_log_div, h_target]

/-! ## Section 7 — Headline closure of `SingularSeriesPrimorialMertensBound` -/

/-- **Headline closure** of `SingularSeriesPrimorialMertensBound`.

For `K = 2 · exp(B + 3)` and `N₀ = max (max z₀ 16) (2 * N₁)`,
where `(B, z₀)` are the Mertens-2 odd constants and `N₁` is the
Chebyshev linear constant,

```
∀ k ≥ N₀, singularSeries (primorial k) ≤ K · log log (primorial k) .
``` -/
theorem singularSeriesPrimorialMertensBound_holds :
    SingularSeriesPrimorialMertensBound := by
  -- Extract Mertens-2 odd upper.
  obtain ⟨B, z₀, hM2⟩ := mertensSecondUpperBoundOdd_holds
  -- Extract Chebyshev linear lower bound on log primorial.
  obtain ⟨N₁, hN₁⟩ := exists_linear_lower_bound_log_primorial_two_mul
  set K : ℝ := 2 * Real.exp (B + 3) with hK_def
  set N₀ : ℕ := max (max z₀ 16) (2 * N₁) with hN₀_def
  have hK_pos : 0 < K := by
    have : (0 : ℝ) < Real.exp (B + 3) := Real.exp_pos _
    rw [hK_def]; linarith
  refine ⟨K, N₀, hK_pos, ?_⟩
  intro k hk
  -- Unpack the threshold.
  have hk_z₀ : z₀ ≤ k := by
    have h1 : z₀ ≤ max z₀ 16 := le_max_left _ _
    have h2 : max z₀ 16 ≤ max (max z₀ 16) (2 * N₁) := le_max_left _ _
    exact (h1.trans h2).trans hk
  have hk_16 : 16 ≤ k := by
    have h1 : 16 ≤ max z₀ 16 := le_max_right _ _
    have h2 : max z₀ 16 ≤ max (max z₀ 16) (2 * N₁) := le_max_left _ _
    exact (h1.trans h2).trans hk
  have hk_2N₁ : 2 * N₁ ≤ k := by
    have h2 : 2 * N₁ ≤ max (max z₀ 16) (2 * N₁) := le_max_right _ _
    exact h2.trans hk
  have hk_3 : 3 ≤ k := by omega
  -- Step 1: S(primorial k) ≤ exp(B+3) · log k.
  have h_S_le_log_k :
      singularSeries (primorial k) ≤ Real.exp (B + 3) * Real.log (k : ℝ) :=
    singularSeries_primorial_le_const_mul_log_k hM2 hk_z₀ hk_3
  -- Step 2: linear lower bound on log primorial k.
  have h_lin : (k : ℝ) / 2 - 1 ≤ Real.log (primorial k : ℝ) :=
    log_primorial_ge_linear_aux hN₁ hk_2N₁
  -- Step 3: log log primorial k ≥ (1/2) log k.
  have h_loglog : (1 / 2 : ℝ) * Real.log (k : ℝ)
                    ≤ Real.log (Real.log (primorial k : ℝ)) :=
    log_log_primorial_ge_half_log_k_aux hk_16 h_lin
  -- Step 4: log k ≤ 2 · log log primorial k.
  have h_log_k_le : Real.log (k : ℝ)
                      ≤ 2 * Real.log (Real.log (primorial k : ℝ)) := by
    linarith
  -- Combine: S ≤ exp(B+3) · log k ≤ exp(B+3) · 2 · log log primorial k = K · log log primorial k.
  have h_exp_pos : (0 : ℝ) < Real.exp (B + 3) := Real.exp_pos _
  have h_step :
      Real.exp (B + 3) * Real.log (k : ℝ)
        ≤ Real.exp (B + 3) * (2 * Real.log (Real.log (primorial k : ℝ))) :=
    mul_le_mul_of_nonneg_left h_log_k_le h_exp_pos.le
  have h_K_eq :
      Real.exp (B + 3) * (2 * Real.log (Real.log (primorial k : ℝ)))
        = K * Real.log (Real.log (primorial k : ℝ)) := by
    rw [hK_def]; ring
  -- Unfold primorialOdd.
  show (singularSeries (primorialOdd k) : ℝ)
        ≤ K * Real.log (Real.log (primorialOdd k : ℝ))
  unfold primorialOdd
  linarith [h_S_le_log_k, h_step, h_K_eq]

/-! ## Section 8 — Summary marker -/

/-- **P22-T7 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `primorialOdd` — alias for mathlib's `Nat.primorial`.
2. `SingularSeriesPrimorialMertensBound` — named Prop.
3. `singularSeriesPrimorialMertensBound_holds` — **closure** of the
   Prop from `mertensSecondUpperBoundOdd_holds` + Chebyshev's
   `eventually_chebyshev_theta_two_mul_ge_const_mul_linear`. -/
theorem pathC_p22_t7_summary : True := trivial

end PathCSingularSeriesPrimorialMertens
end Gdbh

/-! ## Axiom audit -/

#print axioms Gdbh.PathCSingularSeriesPrimorialMertens.singularSeriesPrimorialMertensBound_holds
