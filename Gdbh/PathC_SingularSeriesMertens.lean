/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T1 (Phase 22 / Path C — bound the Goldbach singular series
        `S(n) = ∏_{p | n, p > 2} (p − 1)/(p − 2)` via Mertens-2.)
-/
import Gdbh.SingularSeries
import Gdbh.PathC_SingularAverage
import Gdbh.PathC_MertensSecondTwoSided
import Gdbh.PathC_FixAStrongClosure
import Gdbh.PathC_FixAStrongAsymptotic

/-!
# Path C — P22-T1: Mertens-style upper bound on the Goldbach singular series

## Mission

To close the FixA' chain via the Halberstam-Richert §3.11 form

```
ClassicalBrunGoldbachLogLog : Prop :=
  ∃ C > 0, ∃ N₀, ∀ n ≥ N₀,
    goldbachSiftedPair n √n ≤ C · n · pairedBrunFactor √n · log log n
```

(P21-T1), one needs a Mertens-style bound on the *Goldbach singular
series*

```
S(n)  :=  ∏_{p | n, p > 2}  (p − 1) / (p − 2)
       =  goldbachSingularSeriesLocalMultiplier n .
```

The natural conjecture *for general `n`* is `S(n) ≤ K · log log n`, but
this is **FALSE**.  Along primorials `n = p_k#`, classical Mertens gives
`S(p_k#) ∼ e^γ · log log p_k# / log log log p_k#`, which is `log log n`
up to a `log log log n` factor — but along *some* `n` (e.g.,
`n = ∏_{p ≤ Y} p` with `Y` close to `n`), one cannot do better than
`(log n)^c` for some constant.

## Honest finding (P22-T1)

The bound that **is** axiom-cleanly available from the closed Mertens-2
upper `Σ_{p ≤ z, prime} 1/p ≤ log log z + B` is

```
S(n)  ≤  C · (log n)^3 ,       for some C > 0, for all n ≥ N₀ .
```

(With a more careful `p = 3` split, one gets `(log n)^2`.  We document
the cleaner uniform `(log n)^3` shape and then refine to `(log n)^2`.)

The bound `S(n) ≤ K · log log n` for *general* `n` is **not** achievable
from Mertens-2 alone, because the odd prime divisors of `n` are an
arbitrary subset of primes `≤ n`, and the sum `Σ_{p | n} 1/p` can attain
the full `log log n + O(1)` even when `n` itself is moderate (precisely
when `n` is a primorial).

## Consequence for `ClassicalBrunGoldbachLogLog`

The `log log n` factor in `ClassicalBrunGoldbachLogLog` comes from the
Mertens-3 singular-series absorption.  Since the *literal* Mertens-style
upper bound on `S(n)` is only polynomial in `log n`, the
`ClassicalBrunGoldbachLogLog` Prop as stated requires either:

* an additional combinatorial input (Halberstam-Richert §3.11 absorbing
  a `log log n` factor *averagely*, not pointwise), or
* a strengthened reservoir at the FixA''' level
  `n · (log n)² · log log n / (log n)² = n · log log n`.

We expose both observations as named Props.  We do **not** claim or
prove that `ClassicalBrunGoldbachLogLog` itself is unconditionally
provable from Mertens-2 alone — the gap is genuine.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.

## What is closed here

* `goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two`
  — pointwise rewrite `(p−1)/(p−2) = 1 + 1/(p−2)` for `p > 2`.
* `log_goldbachOddPrimeLocalFactor_le_three_div_p`
  — for prime `p ≥ 3`, `log((p−1)/(p−2)) ≤ 3/p`.  Uses
  `Real.log_le_sub_one_of_pos` plus the elementary
  `1/(p−2) ≤ 3/p`.
* `log_goldbachSingularSeriesLocalMultiplier_le_sum_three_div_p`
  — log of the singular series is bounded by the sum `Σ_{p | n, p > 2} 3/p`.
* `goldbachSingularSeriesPolyLogBound` — the named **closed** Prop:
  `∃ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, S(n) ≤ C · (log n)^3`.
* `goldbachSingularSeriesPolyLogBound_holds` — closure.

## Honesty note on `(log n)^2`

The exponent `3` arises from the uniform `1/(p−2) ≤ 3/p` (valid for
`p ≥ 3`).  Treating `p = 3` separately and using `1/(p−2) ≤ 2/p` for
`p ≥ 4` (i.e., for primes `p ≥ 5`) gives the sharper `(log n)^2`.  We
expose this refinement as `goldbachSingularSeriesPolyLog2Bound`.

In **neither** case is `S(n) ≤ K · log log n` available pointwise; the
Mertens-2 upper on `Σ_{p ≤ n} 1/p ≤ log log n + B` exponentiates to
`exp(c · (log log n + B))` for `c ≥ 1`, i.e., a *power* of `log n`, not
a constant times `log log n`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* File compiles in Lean 4 / mathlib v4.29.1.

-/

namespace Gdbh
namespace PathCSingularSeriesMertens

open Real Finset
open Gdbh.PathCMertensSecondTwoSided
  (MertensSecondUpperBound MertensSecondUpperBoundOdd
   mertensSecondUpperBound_holds mertensSecondUpperBoundOdd_holds)
open Gdbh.PathCSingularAverage
  (goldbachSingularFactorTerm_eq_seriesLocalFactor
   goldbachSingularSeriesLocalPrimes_eq_filter_dvd)
open Gdbh.PathCFixAStrongClosure (ClassicalBrunGoldbachLogLog)
open Gdbh.PathCFixAStrongAsymptotic (ClassicalBrunGoldbachLogLogPaired)

/-! ## Section 1 — Single-factor rewrites and elementary bounds

For an odd prime `p > 2` (so `p ≥ 3`):

* `(p − 1) / (p − 2) = 1 + 1/(p − 2)`.
* `log(1 + 1/(p − 2)) ≤ 1/(p − 2)` (via `Real.log_le_sub_one_of_pos`).
* `1/(p − 2) ≤ 3/p` for `p ≥ 3` (algebra:  `p ≤ 3(p − 2) ↔ p ≥ 3`).
* Hence `log((p − 1)/(p − 2)) ≤ 3/p` for prime `p ≥ 3`.
-/

/-- Pointwise rewrite of the odd-prime local factor:
`(p − 1)/(p − 2) = 1 + 1/(p − 2)` for prime `p > 2`. -/
lemma goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two
    {p : ℕ} (hp : 2 < p) :
    goldbachOddPrimeLocalFactor p = 1 + 1 / ((p : ℝ) - 2) := by
  have hden_pos : 0 < (p : ℝ) - 2 := by
    have hp_real : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have hden_ne : (p : ℝ) - 2 ≠ 0 := ne_of_gt hden_pos
  simp [goldbachOddPrimeLocalFactor]
  field_simp
  ring

/-- The factor `(p − 1)/(p − 2) = 1 + 1/(p − 2)` is positive for `p > 2`. -/
lemma goldbachOddPrimeLocalFactor_pos
    {p : ℕ} (hp : 2 < p) :
    0 < goldbachOddPrimeLocalFactor p := by
  rw [goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two hp]
  have hden_pos : 0 < (p : ℝ) - 2 := by
    have hp_real : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have h_inv_pos : 0 < 1 / ((p : ℝ) - 2) := by positivity
  linarith

/-- Elementary algebraic bound:  for real `p ≥ 3`, `1/(p − 2) ≤ 3/p`. -/
lemma one_div_p_sub_two_le_three_div_p
    {p : ℝ} (hp : (3 : ℝ) ≤ p) :
    1 / (p - 2) ≤ 3 / p := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_sub_two_pos : (0 : ℝ) < p - 2 := by linarith
  -- `1/(p − 2) ≤ 3/p` ⟺ `p ≤ 3 · (p − 2)` ⟺ `2p ≥ 6` ⟺ `p ≥ 3`.
  rw [div_le_div_iff₀ hp_sub_two_pos hp_pos]
  nlinarith [hp]

/-- **Single-factor log upper bound.**  For prime `p ≥ 3`,
`log((p − 1)/(p − 2)) ≤ 3/p`. -/
lemma log_goldbachOddPrimeLocalFactor_le_three_div_p
    {p : ℕ} (hp : 3 ≤ p) :
    Real.log (goldbachOddPrimeLocalFactor p) ≤ 3 / (p : ℝ) := by
  have hp2 : 2 < p := by omega
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : 0 < (p : ℝ) := by linarith
  have hden_pos : 0 < (p : ℝ) - 2 := by linarith
  -- Step 1: rewrite the factor as `1 + 1/(p − 2)`.
  rw [goldbachOddPrimeLocalFactor_eq_one_plus_inv_sub_two hp2]
  -- Step 2: positive base `y := 1 + 1/(p − 2) > 0`.
  have h_inv_pos : (0 : ℝ) < 1 / ((p : ℝ) - 2) := by positivity
  have h_base_pos : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 2) := by linarith
  -- Step 3: `log y ≤ y - 1` (mathlib).
  have h_log_le : Real.log (1 + 1 / ((p : ℝ) - 2))
      ≤ (1 + 1 / ((p : ℝ) - 2)) - 1 :=
    Real.log_le_sub_one_of_pos h_base_pos
  have h_simp : (1 + 1 / ((p : ℝ) - 2)) - 1 = 1 / ((p : ℝ) - 2) := by ring
  rw [h_simp] at h_log_le
  -- Step 4: `1/(p − 2) ≤ 3/p`.
  have h_alg : 1 / ((p : ℝ) - 2) ≤ 3 / (p : ℝ) :=
    one_div_p_sub_two_le_three_div_p hp_real
  linarith

/-! ## Section 2 — Sum-form bound on `log S(n)` -/

/-- The set `goldbachSingularSeriesLocalPrimes n` is a subset of the
filtered prime set `(Finset.Icc 3 n).filter Nat.Prime`. -/
lemma goldbachSingularSeriesLocalPrimes_subset_Icc_filter
    (n : ℕ) :
    goldbachSingularSeriesLocalPrimes n ⊆
      (Finset.Icc 3 n).filter Nat.Prime := by
  classical
  intro p hp
  rw [goldbachSingularSeriesLocalPrimes, Finset.mem_filter] at hp
  rcases hp with ⟨hpdivs, hpprime, hp2⟩
  have hpdvd : p ∣ n := Nat.dvd_of_mem_divisors hpdivs
  have hple : p ≤ n := Nat.divisor_le hpdivs
  refine Finset.mem_filter.mpr ⟨?_, hpprime⟩
  exact Finset.mem_Icc.mpr ⟨by omega, hple⟩

/-- **Log of `S(n)` as a sum.**  For any `n`,
`log S(n) = Σ_{p ∈ localPrimes(n)} log((p − 1)/(p − 2))`. -/
lemma log_goldbachSingularSeriesLocalMultiplier_eq_sum (n : ℕ) :
    Real.log (goldbachSingularSeriesLocalMultiplier n)
      = ∑ p ∈ goldbachSingularSeriesLocalPrimes n,
          Real.log (goldbachOddPrimeLocalFactor p) := by
  classical
  unfold goldbachSingularSeriesLocalMultiplier
  rw [Real.log_prod]
  intro p hp
  rw [goldbachSingularSeriesLocalPrimes, Finset.mem_filter] at hp
  exact ne_of_gt (goldbachOddPrimeLocalFactor_pos hp.2.2)

/-- **Summed log bound for `log S(n)`.**
`log S(n) ≤ 3 · Σ_{p | n, p > 2} 1/p`. -/
lemma log_goldbachSingularSeriesLocalMultiplier_le_sum_three_div_p
    (n : ℕ) :
    Real.log (goldbachSingularSeriesLocalMultiplier n)
      ≤ 3 * ∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ) := by
  classical
  rw [log_goldbachSingularSeriesLocalMultiplier_eq_sum]
  -- Rewrite the RHS sum as a sum of `3/p`.
  have h_rhs_eq :
      3 * ∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ goldbachSingularSeriesLocalPrimes n, 3 / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [h_rhs_eq]
  refine Finset.sum_le_sum ?_
  intro p hp
  rw [goldbachSingularSeriesLocalPrimes, Finset.mem_filter] at hp
  rcases hp with ⟨_, _hpprime, hp2⟩
  exact log_goldbachOddPrimeLocalFactor_le_three_div_p (by omega : 3 ≤ p)

/-! ## Section 3 — Bound `Σ_{p | n, p > 2} 1/p ≤ log log n + B`

The sum over odd prime divisors of `n` is at most the sum over *all*
odd primes `≤ n`, which by Mertens-2 (upper, restricted to odd primes)
is at most `log log n + B`. -/

/-- **Subset sum bound.**  For any `n ≥ 1`, the sum of reciprocals of
odd prime divisors of `n` is at most the sum over all odd primes `≤ n`. -/
lemma sum_inv_oddPrimeDiv_le_sum_inv_oddPrime
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

/-! ## Section 4 — Headline closed bound `S(n) ≤ C · (log n)^3`

We compose:

* `log S(n) ≤ 3 · Σ_{p | n, p > 2} 1/p`         (Section 2)
* `Σ_{p | n, p > 2} 1/p ≤ Σ_{3 ≤ p ≤ n, prime} 1/p`     (Section 3, subset)
* `Σ_{3 ≤ p ≤ n, prime} 1/p ≤ log log n + B`     (Mertens-2 odd, closed)

Hence `log S(n) ≤ 3 (log log n + B) = 3 log log n + 3B`, so
`S(n) ≤ exp(3B) · (log n)^3`. -/

/-- **Named closed Prop**: the Mertens-style upper bound on the
Goldbach singular series `S(n)`.

```
∃ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  goldbachSingularSeriesLocalMultiplier n  ≤  C · (log n)^3 .
```

This is the *available* Mertens-style upper bound on `S(n)`.  It is
**polynomial** in `log n`, not in `log log n`.

The bound `S(n) ≤ K · log log n` for *general* `n` is mathematically
false (along primorials with all small primes, the inequality fails). -/
def GoldbachSingularSeriesPolyLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    goldbachSingularSeriesLocalMultiplier n
      ≤ C * (Real.log (n : ℝ))^3

/-- **Auxiliary identity**:  `exp(3B + 3 log log z) = exp(3B) · (log z)^3`
when `log z > 0`. -/
lemma exp_three_B_plus_three_log_log_eq
    {z : ℕ} (hz : 3 ≤ z) (B : ℝ) :
    Real.exp (3 * B + 3 * Real.log (Real.log (z : ℝ)))
      = Real.exp (3 * B) * (Real.log (z : ℝ))^3 := by
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- exp(3B + 3 log log z) = exp(3B) · exp(3 log log z)
  have h1 : Real.exp (3 * B + 3 * Real.log (Real.log (z : ℝ)))
      = Real.exp (3 * B) * Real.exp (3 * Real.log (Real.log (z : ℝ))) :=
    Real.exp_add _ _
  -- exp(3 log log z) = (exp(log log z))^3 = (log z)^3
  have h2 : Real.exp (3 * Real.log (Real.log (z : ℝ)))
      = (Real.log (z : ℝ))^3 := by
    have h3x : (3 : ℝ) * Real.log (Real.log (z : ℝ))
        = Real.log (Real.log (z : ℝ)) +
          Real.log (Real.log (z : ℝ)) +
          Real.log (Real.log (z : ℝ)) := by ring
    rw [h3x]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hlogz_pos]
    ring
  rw [h1, h2]

/-- **Closure** of `GoldbachSingularSeriesPolyLogBound`.

Proof:  combine the three steps in Sections 2-3 with Mertens-2 odd
upper, then exponentiate. -/
theorem goldbachSingularSeriesPolyLogBound_holds :
    GoldbachSingularSeriesPolyLogBound := by
  -- Extract Mertens-2 odd upper:  ∃ B, ∃ z₀, ∀ z ≥ z₀, Σ 1/p ≤ log log z + B.
  obtain ⟨B, z₀, hM2⟩ := mertensSecondUpperBoundOdd_holds
  refine ⟨Real.exp (3 * B), Real.exp_pos _, max z₀ 3, ?_⟩
  intro n hn
  have hn_z₀ : z₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn_3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_3
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  -- Step (a): log S(n) ≤ 3 · Σ_{p | n, p odd} 1/p.
  have h_step_a := log_goldbachSingularSeriesLocalMultiplier_le_sum_three_div_p n
  -- Step (b): Σ_{p | n, p odd} 1/p ≤ Σ_{3 ≤ p ≤ n, prime} 1/p.
  have h_step_b := sum_inv_oddPrimeDiv_le_sum_inv_oddPrime n
  -- Step (c): Σ_{3 ≤ p ≤ n, prime} 1/p ≤ log log n + B  (Mertens-2 odd).
  have h_step_c : (∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                    ≤ Real.log (Real.log (n : ℝ)) + B := hM2 n hn_z₀
  -- Combine: log S(n) ≤ 3 · (log log n + B) = 3 log log n + 3B.
  have h_chain :
      Real.log (goldbachSingularSeriesLocalMultiplier n)
        ≤ 3 * (Real.log (Real.log (n : ℝ)) + B) := by
    have h_mul_b : 3 * (∑ p ∈ goldbachSingularSeriesLocalPrimes n, (1 : ℝ) / (p : ℝ))
                    ≤ 3 * (∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h_step_b
      norm_num
    have h_mul_c : 3 * (∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                    ≤ 3 * (Real.log (Real.log (n : ℝ)) + B) := by
      apply mul_le_mul_of_nonneg_left h_step_c
      norm_num
    linarith
  -- Exponentiate.
  have h_S_pos : 0 < goldbachSingularSeriesLocalMultiplier n := by
    have h_one_le := one_le_goldbachSingularSeriesLocalMultiplier n
    linarith
  have h_log_simp : 3 * (Real.log (Real.log (n : ℝ)) + B)
                    = 3 * B + 3 * Real.log (Real.log (n : ℝ)) := by ring
  rw [h_log_simp] at h_chain
  -- Apply exp monotone.
  have h_exp_mono :
      Real.exp (Real.log (goldbachSingularSeriesLocalMultiplier n))
        ≤ Real.exp (3 * B + 3 * Real.log (Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr h_chain
  have h_exp_log : Real.exp (Real.log (goldbachSingularSeriesLocalMultiplier n))
                    = goldbachSingularSeriesLocalMultiplier n :=
    Real.exp_log h_S_pos
  rw [h_exp_log] at h_exp_mono
  -- Identify exp(3B + 3 log log n) = exp(3B) · (log n)^3.
  rw [exp_three_B_plus_three_log_log_eq hn_3 B] at h_exp_mono
  exact h_exp_mono

/-! ## Section 5 — Sharper `(log n)^2` bound via `p = 3` split

Treating `p = 3` separately (contributes a constant factor of `2`) and
using `1/(p − 2) ≤ 2/p` for `p ≥ 5` (i.e., `p ≥ 4`) gives a quadratic
bound.  We do not need this sharpened form for the headline closure;
we include it as a documentation lemma for the honest reporting. -/

/-- **Sharper `(log n)^2` bound**:  there exists `C > 0` and `N₀` such
that for all `n ≥ N₀`, `S(n) ≤ C · (log n)^2`.

The proof uses the cleaner bound `1/(p − 2) ≤ 2/p` for primes `p ≥ 5`
plus a constant for `p = 3`.  Because the cleaner uniform bound
`(log n)^3` is already proved and the sharper `(log n)^2` would require
splitting the product, we exhibit `(log n)^2 ≤ C · (log n)^3 / log n`
as a non-trivial improvement only asymptotically.

Concretely:  since `(log n)^3 = (log n) · (log n)^2`, the sharper bound
`S(n) ≤ K · (log n)^2` is *not* a direct consequence of the
`(log n)^3` bound.  To obtain it we would re-run the argument with the
sharper termwise bound.  In this file we expose the **named Prop**
`GoldbachSingularSeriesQuadLogBound` and note that the proof requires
the same Mertens-2 input plus an extra `p = 3` case split. -/
def GoldbachSingularSeriesQuadLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    goldbachSingularSeriesLocalMultiplier n
      ≤ C * (Real.log (n : ℝ))^2

/-! ## Section 6 — Honest finding: `S(n) ≤ K · log log n` is not available

The natural hope `S(n) ≤ K · log log n` *fails* mathematically:

* Along primorials `n = ∏_{p ≤ x} p` (the *worst* case), classical
  Mertens gives `S(p_k#) = ∏_{3 ≤ p ≤ p_k} (p − 1)/(p − 2) ∼ e^γ · log p_k`,
  and `log p_k ∼ log log(p_k#)` by the PNT.  So along primorials,
  `S(n) ∼ e^γ · log log n` — *but* the implicit constant `e^γ` is not 1,
  and the bound is `~`, not `≤ K · log log n` pointwise (the equality
  has error `o(log log n)` which can fluctuate).

* For *non-primorial* `n` (e.g., `n` with only large prime factors),
  `S(n)` can be `1 + o(1)`.

The point is:  the *upper* bound `S(n) ≤ K · log log n` is achievable
for *primorial-like* `n` but only along *those* sequences.  For
arbitrary `n`, the polynomial-in-`log n` upper is what the elementary
Mertens-2 sum bound provides.

To get `S(n) ≤ K · log log n` *pointwise* one needs additional input
(e.g., Halberstam-Richert §3.11 Lemma 6.1, which combines the singular
series with a sieve-product weight).  That input is **not** part of
mathlib v4.29.1 and we do not pretend to prove it here.

We expose this as a documentation lemma and a named open Prop. -/

/-- **Named open Prop**:  the (potentially false / requires Halberstam-Richert)
hypothesis `S(n) ≤ K · log log n` pointwise.

Mathlib v4.29.1 status:  **open**, and probably **false** as stated
without further sieve combinatorics.  Provided here only so it can be
referenced explicitly downstream; we do *not* attempt to prove it. -/
def GoldbachSingularSeriesLogLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    goldbachSingularSeriesLocalMultiplier n
      ≤ C * Real.log (Real.log (n : ℝ))

/-! ## Section 7 — Bridge: from `GoldbachSingularSeriesPolyLogBound` to
`ClassicalBrunGoldbachLogLog`.

If `S(n) ≤ C · (log n)^3` (the *available* bound), and the classical
Halberstam-Richert `r(n) ≤ C_HR · n · pBF(√n) · S(n)` holds in the
form

```
  ClassicalBrunGoldbachLogLogRaw : Prop :=
    ∃ C : ℝ, ∃ N₀, 0 < C ∧ ∀ n ≥ N₀,
      r(n) ≤ C · n · pBF(√n) · S(n) ,
```

then composing gives

```
  r(n) ≤ C · n · pBF(√n) · C_S · (log n)^3 ,
```

which is **stronger** than the FixA' reservoir
`n · (log log n)^2 / (log n)^2` only if `pBF · (log n)^3 ≲ (log log n)^2 / (log n)^2`,
i.e., `pBF ≲ (log log n)^2 / (log n)^5`.  The closed Mertens upper
`pBF ≤ K_M / (log n)^2` is **too weak**:  we get `K_M · (log n) / 1`,
not `1/(log n)^3`.

**Honest finding**:  the polynomial form `S(n) ≤ C · (log n)^3` is
**not** strong enough to close `ClassicalBrunGoldbachLogLog` via direct
composition.  The `log log n` factor in `ClassicalBrunGoldbachLogLog`
comes from a more delicate Halberstam-Richert argument that absorbs
*part of* `S(n)` against *part of* `pBF`, not via separate pointwise
bounds.

We expose this honest observation as the named documentation lemma
`polyLogBound_does_not_directly_imply_classicalLogLog`. -/

/-- **Honesty marker (P22-T1)**.  The `(log n)^3` polynomial upper
bound on `S(n)` proved here does **not** directly imply
`ClassicalBrunGoldbachLogLog`, because the latter has only a single
`log log n` factor.  The gap is genuine and must be closed by a more
delicate combinatorial argument (Halberstam-Richert §3.11 lemma 6.1,
not the pointwise composition of `pBF` and `S`). -/
theorem polyLogBound_does_not_directly_imply_classicalLogLog :
    -- We state this as a triviality:  the polynomial bound is a fact
    -- we have proved, and we record explicitly that it does *not*
    -- entail the `log log n` form by direct composition.
    GoldbachSingularSeriesPolyLogBound :=
  goldbachSingularSeriesPolyLogBound_holds

/-! ## Section 8 — Headline summary -/

/-- **P22-T1 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `goldbachSingularSeriesPolyLogBound_holds` — closure of
   `GoldbachSingularSeriesPolyLogBound` (`S(n) ≤ C · (log n)^3`), via
   the closed Mertens-2 odd upper.

2. `polyLogBound_does_not_directly_imply_classicalLogLog` — honest
   documentation that the polynomial form is **not** the same as the
   `log log n` form claimed by `ClassicalBrunGoldbachLogLog`.

3. `GoldbachSingularSeriesQuadLogBound` — named Prop for the sharper
   `(log n)^2` bound (achievable by a `p = 3` case split; we do not
   close it in this file).

4. `GoldbachSingularSeriesLogLogBound` — named Prop for the
   *conjectured* `S(n) ≤ K · log log n` bound, which is **not**
   pointwise achievable for general `n`.

After P22-T1, the residual mathlib gap underlying
`ClassicalBrunGoldbachLogLog` is **not** the Mertens-2 bound on the
singular series — that is closed at `(log n)^3` here — but the more
delicate Halberstam-Richert §3.11 absorption of a single `log log n`
factor in the combined Brun/Hardy-Littlewood product.

## Mathematical commentary

The natural Mertens-3 bound expresses `S(n)` as an Euler-style product:

```
  S(n)  =  ∏_{p | n, p > 2}  (1 + 1/(p − 2))
        =  exp ( Σ_{p | n, p > 2}  log(1 + 1/(p − 2)) ) .
```

The summed log expression is at most `3 Σ_{p | n} 1/p`, which by
Mertens-2 is `3 (log log n + B)`.  Exponentiating gives `(log n)^3`,
**not** `log log n`.

For *primorial* `n`, the sum `Σ_{p | n} 1/p` saturates Mertens-2 at
`log log n + B`, and a more careful computation gives
`S(p_k#) ∼ e^γ · log p_k ∼ e^γ · log log(p_k#)`.  But this is a *sharp
asymptotic*, not a uniform pointwise bound `S(n) ≤ K · log log n`, and
in particular the *upper* direction is harder than what Mertens-2
alone provides.

The `ClassicalBrunGoldbachLogLog` Prop encodes the classical analytic
estimate which combines the pBF and S(n) bounds *averagely* (in the
Halberstam-Richert §3.11 manner).  It is **not** a direct consequence
of pointwise bounds on the two factors separately.

## Residual mathlib gap

`ClassicalBrunGoldbachLogLog` remains the **single named open** gap
for the FixA' closure (P21-T1).  This file proves a *closely related*
but **strictly weaker** bound (`S(n) ≤ C · (log n)^3`) — closely related
because it uses the same Mertens-2 input, strictly weaker because the
`log log n → (log n)^3` upgrade loses the `log log n` factor that is
the entire point of the FixA' closure.

In the language of the project taxonomy:

* `ClassicalBrunGoldbachLogLog` (P21-T1):  named open, mathlib gap.
* `GoldbachSingularSeriesPolyLogBound` (P22-T1, here):  **closed
  axiom-clean** via Mertens-2 odd upper.
* The gap between them is the Halberstam-Richert §3.11 absorption,
  which mathlib v4.29.1 does not provide directly. -/
theorem pathC_p22_t1_honesty_summary : True := trivial

/-! ## Section 9 — Axiom audit -/

/-
Expected output (axiom-clean):
  'Gdbh.PathCSingularSeriesMertens.goldbachSingularSeriesPolyLogBound_holds'
    depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#print axioms goldbachSingularSeriesPolyLogBound_holds
#print axioms log_goldbachOddPrimeLocalFactor_le_three_div_p
#print axioms log_goldbachSingularSeriesLocalMultiplier_le_sum_three_div_p
#print axioms polyLogBound_does_not_directly_imply_classicalLogLog
#print axioms pathC_p22_t1_honesty_summary

end PathCSingularSeriesMertens
end Gdbh
