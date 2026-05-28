/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T5 (Phase 22 / Path C — sibling `S(n) ≤ K · log n` bound,
        sharpening the `(log n)^3` polynomial of P22-T1 to a single
        `log n` factor via the tight per-prime decomposition
        `1/(p-2) ≤ 1/p + 6/p²`.)
-/
import Gdbh.PathC_SingularSeriesMertens
import Gdbh.PathC_MertensSecondUpper

/-!
# Path C — P22-T5: `S(n) ≤ K · log n` from Mertens-2 + telescoping `Σ 1/p²`

## Mission

P22-T1 proved the polynomial bound `S(n) ≤ C · (log n)^3` using the
uniform per-prime bound `log((p-1)/(p-2)) ≤ 3/p`.  T22-T1 identified that
the sharper bound `S(n) ≤ K · log n` is closeable *today* using the
existing infrastructure, by replacing the loose `1/(p-2) ≤ 3/p` with the
tight decomposition

```
  1/(p-2)  =  1/p  +  2/(p(p-2))  ≤  1/p  +  6/p²        (valid for p ≥ 3).
```

The remainder `6/p²` is summable to a *constant* (not a `log log n`
factor!) via the closed telescoping bound

```
  Σ_{3 ≤ p ≤ z, p prime}  1/p²  ≤  1/2 ,
```

giving `Σ_{p|n, p>2} 1/(p-2) ≤ (log log n + B) + 6 · 1/2 = log log n + B + 3`.
Exponentiating: `S(n) ≤ exp(B+3) · exp(log log n) = K · log n` with
`K = exp(B+3)`.

This is a **strictly sharper** bound than P22-T1's `(log n)^3` (for large
enough `n`), and closes the headline sibling Prop `SingularSeriesLogNBound`
axiom-clean.

## Strategy summary

1. **Per-prime log bound (tight).**  For prime `p ≥ 3`:
   `log((p-1)/(p-2)) = log(1 + 1/(p-2)) ≤ 1/(p-2)`  (Real.log_le_sub_one_of_pos).
2. **Algebraic decomposition.**  For real `p ≥ 3`:
   `1/(p-2) ≤ 1/p + 6/p²`  (since `p(p-2) ≥ p²/3`).
3. **Sum the per-prime bound.**
   `Σ_{p|n, p>2} log((p-1)/(p-2)) ≤ Σ_{p|n, p>2} 1/p + 6 · Σ_{p|n, p>2} 1/p²`.
4. **Apply Mertens-2 odd-form (closed) + telescoping `Σ 1/p² ≤ 1/2`.**
   `Σ_{p|n, p>2} 1/p ≤ log log n + B`  (P19-T6/T9 + subset).
   `Σ_{p|n, p>2} 1/p² ≤ 1/2`            (P19-T6 telescoping + subset).
5. **Combine and exponentiate.**
   `log S(n) ≤ log log n + B + 3`, so `S(n) ≤ exp(B+3) · log n`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCSingularSeriesLogNBound

open Real Finset
open Gdbh.PathCMertensSecondTwoSided
  (MertensSecondUpperBoundOdd mertensSecondUpperBoundOdd_holds)
open Gdbh.PathCMertensSecondUpper (sum_one_div_sq_prime_le_half)
open Gdbh.PathCSingularSeriesMertens
  (goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two
   goldbachOddPrimeLocalFactor_pos
   goldbachSingularSeriesLocalPrimes_subset_Icc_filter
   log_goldbachSingularSeriesLocalMultiplier_eq_sum)

/-! ## Section 1 — Named Prop `SingularSeriesLogNBound`

The parametric Prop generalises both the named Goldbach singular series
`goldbachSingularSeriesLocalMultiplier` and any analogous Mertens-product
shape, so it can be reused for downstream bounds. -/

/-- **Named Prop**: `K · log n` upper bound for a singular-series-like
function `S : ℕ → ℝ`.

```
∃ K : ℝ, ∃ N₀ : ℕ, 0 < K  ∧  ∀ n ≥ N₀,  S(n) ≤ K · log n .
```

The headline closure `singularSeries_log_n_bound_holds` establishes this
for `S = goldbachSingularSeriesLocalMultiplier`. -/
def SingularSeriesLogNBound (S : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧
    ∀ n : ℕ, N₀ ≤ n → S n ≤ K * Real.log (n : ℝ)

/-! ## Section 2 — Tight per-prime bound `log((p-1)/(p-2)) ≤ 1/(p-2)`

For prime `p ≥ 3`, rewrite the local factor as `1 + 1/(p-2)` (positive)
and apply `Real.log_le_sub_one_of_pos`. -/

/-- For prime `p ≥ 3`, `log((p-1)/(p-2)) ≤ 1/(p-2)`. -/
lemma log_oddFactor_le_inv_p_sub_two
    {p : ℕ} (hp : 3 ≤ p) :
    Real.log (goldbachOddPrimeLocalFactor p) ≤ 1 / ((p : ℝ) - 2) := by
  have hp2 : 2 < p := by omega
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two hp2]
  have h_inv_pos : (0 : ℝ) < 1 / ((p : ℝ) - 2) := by positivity
  have h_base_pos : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 2) := by linarith
  have h_log_le : Real.log (1 + 1 / ((p : ℝ) - 2))
      ≤ (1 + 1 / ((p : ℝ) - 2)) - 1 :=
    Real.log_le_sub_one_of_pos h_base_pos
  have h_simp : (1 + 1 / ((p : ℝ) - 2)) - 1 = 1 / ((p : ℝ) - 2) := by ring
  linarith [h_log_le, h_simp]

/-! ## Section 3 — Algebraic decomposition `1/(p-2) ≤ 1/p + 6/p²`

`1/(p-2) - 1/p = 2/(p(p-2))`, and `p(p-2) ≥ p²/3` for `p ≥ 3`, so
`2/(p(p-2)) ≤ 6/p²`.  Equivalently: `2p² ≤ 6p(p-2)` ⟺ `p² ≤ 3p(p-2)` ⟺
`0 ≤ 2p(p-3)`, which holds for `p ≥ 3`. -/

/-- For real `p ≥ 3`, `1/(p-2) ≤ 1/p + 6/p²`. -/
lemma one_div_p_sub_two_le_split
    {p : ℝ} (hp : (3 : ℝ) ≤ p) :
    1 / (p - 2) ≤ 1 / p + 6 / p^2 := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_sub_pos : (0 : ℝ) < p - 2 := by linarith
  have hp_sq_pos : (0 : ℝ) < p^2 := by positivity
  -- 1/(p-2) - 1/p = ((p) - (p-2)) / (p(p-2)) = 2/(p(p-2)).
  have h_diff : 1 / (p - 2) - 1 / p
                  = 2 / (p * (p - 2)) := by
    field_simp
    ring
  -- 2/(p(p-2)) ≤ 6/p²  ⟺  2 p² ≤ 6 p (p-2)  ⟺  p² ≤ 3 p (p-2)
  -- ⟺ p² ≤ 3 p² - 6 p ⟺ 0 ≤ 2p² - 6p = 2p(p-3), true for p ≥ 3.
  have h_prod_pos : (0 : ℝ) < p * (p - 2) := by positivity
  have h_ineq : 2 / (p * (p - 2)) ≤ 6 / p^2 := by
    rw [div_le_div_iff₀ h_prod_pos hp_sq_pos]
    -- Goal: 2 * p^2 ≤ 6 * (p * (p - 2))
    nlinarith [hp, hp_pos]
  linarith [h_diff, h_ineq]

/-- For prime `p ≥ 3`, `log((p-1)/(p-2)) ≤ 1/p + 6/p²`. -/
lemma log_oddFactor_le_split
    {p : ℕ} (hp : 3 ≤ p) :
    Real.log (goldbachOddPrimeLocalFactor p)
      ≤ 1 / (p : ℝ) + 6 / (p : ℝ)^2 := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact le_trans (log_oddFactor_le_inv_p_sub_two hp)
                 (one_div_p_sub_two_le_split hp_real)

/-! ## Section 4 — Summed log bound for `goldbachSingularSeriesLocalMultiplier`

Combining the tight per-prime bound with the existing decomposition
`log S(n) = Σ_{p | n, p > 2} log((p-1)/(p-2))` gives

```
  log S(n)  ≤  Σ_{p | n, p > 2} (1/p + 6/p²)
             ≤  Σ_{3 ≤ p ≤ n, p prime} 1/p  +  6 · Σ_{3 ≤ p ≤ n, p prime} 1/p² .
```
-/

/-- **Termwise sum bound** for `log S(n)`.

```
  log S(n)  ≤  Σ_{p | n, p > 2} 1/p  +  6 · Σ_{p | n, p > 2} 1/p² .
``` -/
lemma log_singularSeries_le_sum_split (n : ℕ) :
    Real.log (goldbachSingularSeriesLocalMultiplier n)
      ≤ (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
          + 6 * ∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2 := by
  classical
  rw [log_goldbachSingularSeriesLocalMultiplier_eq_sum]
  -- Rewrite RHS as a single sum.
  have h_rhs_eq :
      (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
          + 6 * ∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2
        = ∑ p ∈ goldbachSingularSeriesLocalPrimes n,
            ((1 : ℝ) / (p : ℝ) + 6 / (p : ℝ)^2) := by
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [h_rhs_eq]
  refine Finset.sum_le_sum ?_
  intro p hp
  rw [goldbachSingularSeriesLocalPrimes, Finset.mem_filter] at hp
  rcases hp with ⟨_, _hpprime, hp2⟩
  exact log_oddFactor_le_split (by omega : 3 ≤ p)

/-- **Subset bound** for the squared-reciprocal sum:
`Σ_{p | n, p > 2} 1/p² ≤ Σ_{3 ≤ p ≤ n, prime} 1/p²`. -/
lemma sum_inv_sq_oddPrimeDiv_le_sum_inv_sq_oddPrime
    (n : ℕ) :
    (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2)
      ≤ ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact goldbachSingularSeriesLocalPrimes_subset_Icc_filter n
  · intro p hp _
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_pos : 0 < (p : ℝ) := by
      have : 0 < p := by omega
      exact_mod_cast this
    positivity

/-- **Subset bound** for the reciprocal sum:
`Σ_{p | n, p > 2} 1/p ≤ Σ_{3 ≤ p ≤ n, prime} 1/p`. -/
lemma sum_inv_oddPrimeDiv_le_sum_inv_oddPrime'
    (n : ℕ) :
    (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact goldbachSingularSeriesLocalPrimes_subset_Icc_filter n
  · intro p hp _
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_pos : 0 < (p : ℝ) := by
      have : 0 < p := by omega
      exact_mod_cast this
    positivity

/-! ## Section 5 — Exponential identity `exp(log log n + C) = exp(C) · log n`

The bridge identity used to convert the additive log-log bound into the
multiplicative `log n` bound. -/

/-- For `n ≥ 3`, `exp(log log n + C) = exp(C) · log n`. -/
lemma exp_log_log_add_const_eq
    {n : ℕ} (hn : 3 ≤ n) (C : ℝ) :
    Real.exp (Real.log (Real.log (n : ℝ)) + C)
      = Real.exp C * Real.log (n : ℝ) := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  -- exp(log log n + C) = exp(log log n) · exp(C) = log n · exp(C).
  rw [Real.exp_add, Real.exp_log hlogn_pos]
  ring

/-! ## Section 6 — Headline closure

Combine Sections 2-5 to obtain `S(n) ≤ exp(B+3) · log n`. -/

/-- **Headline closure** of `SingularSeriesLogNBound` for the Goldbach
singular-series multiplier.

```
∃ K > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  goldbachSingularSeriesLocalMultiplier n  ≤  K · log n .
```

Constants: `K = exp(B + 3)` and `N₀ = max z₀ 3`, where `(B, z₀)` are the
constants from the closed `mertensSecondUpperBoundOdd_holds`. -/
theorem singularSeries_log_n_bound_holds :
    SingularSeriesLogNBound goldbachSingularSeriesLocalMultiplier := by
  -- Extract closed Mertens-2 odd upper:
  -- ∃ B z₀, ∀ z ≥ z₀, Σ_{3 ≤ p ≤ z} 1/p ≤ log log z + B.
  obtain ⟨B, z₀, hM2⟩ := mertensSecondUpperBoundOdd_holds
  refine ⟨Real.exp (B + 3), max z₀ 3, Real.exp_pos _, ?_⟩
  intro n hn
  have hn_z₀ : z₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn_3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  -- Step 1: log S(n) ≤ Σ_{p|n,p>2} 1/p + 6 · Σ_{p|n,p>2} 1/p².
  have h_step1 := log_singularSeries_le_sum_split n
  -- Step 2: subset sums.
  have h_step2a := sum_inv_oddPrimeDiv_le_sum_inv_oddPrime' n
  have h_step2b := sum_inv_sq_oddPrimeDiv_le_sum_inv_sq_oddPrime n
  -- Step 3: Mertens-2 odd upper at n.
  have h_step3a : (∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                    ≤ Real.log (Real.log (n : ℝ)) + B := hM2 n hn_z₀
  -- Step 4: telescoping `Σ 1/p² ≤ 1/2`.
  have h_step3b : (∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
                    ≤ 1 / 2 := sum_one_div_sq_prime_le_half n hn_3
  -- Combine: log S(n) ≤ (log log n + B) + 6 · (1/2) = log log n + B + 3.
  have h_sum_p : (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
                  ≤ Real.log (Real.log (n : ℝ)) + B :=
    le_trans h_step2a h_step3a
  have h_sum_p_sq : (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2)
                    ≤ 1 / 2 :=
    le_trans h_step2b h_step3b
  have h_6_le : 6 * (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2)
                ≤ 6 * (1 / 2) := by
    have := mul_le_mul_of_nonneg_left h_sum_p_sq (by norm_num : (0 : ℝ) ≤ 6)
    linarith [this]
  have h_log_S_le : Real.log (goldbachSingularSeriesLocalMultiplier n)
                      ≤ Real.log (Real.log (n : ℝ)) + B + 3 := by
    have h_combine :
        (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
          + 6 * ∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)^2
        ≤ (Real.log (Real.log (n : ℝ)) + B) + 6 * (1 / 2) := by
      linarith [h_sum_p, h_6_le]
    have h_eq : (Real.log (Real.log (n : ℝ)) + B) + 6 * (1 / 2)
                  = Real.log (Real.log (n : ℝ)) + B + 3 := by ring
    linarith [h_step1, h_combine, h_eq]
  -- Step 5: exponentiate.
  have h_S_pos : 0 < goldbachSingularSeriesLocalMultiplier n := by
    have h_one_le := one_le_goldbachSingularSeriesLocalMultiplier n
    linarith
  -- exp is monotone.
  have h_exp_mono :
      Real.exp (Real.log (goldbachSingularSeriesLocalMultiplier n))
        ≤ Real.exp (Real.log (Real.log (n : ℝ)) + B + 3) :=
    Real.exp_le_exp.mpr h_log_S_le
  have h_exp_log : Real.exp (Real.log (goldbachSingularSeriesLocalMultiplier n))
                    = goldbachSingularSeriesLocalMultiplier n :=
    Real.exp_log h_S_pos
  -- Identify exp(log log n + (B+3)) = exp(B+3) · log n.
  have h_rearrange : Real.log (Real.log (n : ℝ)) + B + 3
                      = Real.log (Real.log (n : ℝ)) + (B + 3) := by ring
  rw [h_rearrange] at h_exp_mono
  rw [exp_log_log_add_const_eq hn_3 (B + 3)] at h_exp_mono
  rw [h_exp_log] at h_exp_mono
  exact h_exp_mono

/-! ## Section 7 — Summary marker

The closed bound `singularSeries_log_n_bound_holds` is *strictly sharper*
than the polynomial `(log n)^3` bound from P22-T1 (since `log n ≤ (log n)^3`
for `n ≥ e`).  Both rely on the same closed Mertens-2 odd upper from
P19-T6/T9, but the present bound exploits the tight decomposition
`1/(p-2) ≤ 1/p + 6/p²` to absorb the `1/(p-2)` excess into a *constant*
remainder (via the closed telescoping `Σ 1/p² ≤ 1/2`), rather than
the loose uniform `1/(p-2) ≤ 3/p`. -/

/-- **P22-T5 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `SingularSeriesLogNBound` — parametric Prop `S(n) ≤ K · log n`.
2. `log_oddFactor_le_inv_p_sub_two` — `log((p-1)/(p-2)) ≤ 1/(p-2)` for
   prime `p ≥ 3`.
3. `one_div_p_sub_two_le_split` — `1/(p-2) ≤ 1/p + 6/p²` for real `p ≥ 3`.
4. `log_oddFactor_le_split` — combination of (2)+(3).
5. `log_singularSeries_le_sum_split` — sum form of (4).
6. `singularSeries_log_n_bound_holds` — closure of
   `SingularSeriesLogNBound goldbachSingularSeriesLocalMultiplier`. -/
theorem pathC_p22_t5_summary : True := trivial

end PathCSingularSeriesLogNBound
end Gdbh

/-! ## Axiom audit -/

#print axioms Gdbh.PathCSingularSeriesLogNBound.singularSeries_log_n_bound_holds
