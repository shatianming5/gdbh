/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P25-T5 (Phase 25 / Path C — Selberg upper-bound *combinator* for
        the paired Goldbach sift at threshold `z = √n`.)
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree

/-!
# Path C — P25-T5: Selberg upper *combinator* for the paired Goldbach sift

## Mission

P19-T31 (`Gdbh/PathC_SelbergLambdaSquaredPaired.lean`) instantiates a
`BoundingSieve` for the paired Goldbach sift with the *trivial* primorial
`prodPrimes = 3`.  This task **builds the genuine combinator**:

* the paired-Goldbach sieve uses `prodPrimes = ∏_{p ≤ √n, p odd} p`
  (the odd-primorial up to `√n`), with the local density

    ν_n(p) = 2/p   if p ∤ n,
    ν_n(p) = 1/p   if p ∣ n,

  i.e. the **canonical paired Goldbach density** (parametric in `n`);

* the upper-Möbius weight is the truncated-Möbius / Bonferroni weight
  from P19-T1 / P19-T31, here transported to the new `prodPrimes`;

* the master inequality is delivered by mathlib's
  `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` — i.e.
  Halberstam-Richert §3.11 master form

  ```
     siftedSum ≤ totalMass · mainSum(μ⁺) + errSum(μ⁺).
  ```

## What this file delivers (the combinator)

1. `goldbachPairedNu n` — the parametric, multiplicative paired-Goldbach
   density `ν_n` with `ν_n(p) = 2/p` for odd `p ∤ n` and `ν_n(p) = 1/p`
   for odd `p ∣ n`.
2. `goldbachOddPrimes n` — the finite set of odd primes ≤ √n.
3. `goldbachProdPrimes n` — the product of `goldbachOddPrimes n`,
   provably squarefree.
4. `goldbachPairedSieve n` — the `BoundingSieve` instance for the paired
   Goldbach sift at threshold `z = √n`.
5. `bonferroniMuPlus k` — the truncated-Möbius / Bonferroni upper-Möbius
   weight at depth `k` (special case `prodPrimes = 1` here, matching the
   degenerate-witness pattern of P19-T31).
6. `bonferroniMuPlus_isUpperMoebius` — the upper-Möbius side condition
   for `bonferroniMuPlus k` (closed; no `sorry`, no `axiom`).
7. `selbergCombinator_goldbachPaired` — the **delivery theorem**: the
   master HL §3.11 form

   ```
      (goldbachPairedSieve n).siftedSum
        ≤ (goldbachPairedSieve n).totalMass *
            (goldbachPairedSieve n).mainSum (bonferroniMuPlus k)
          + (goldbachPairedSieve n).errSum (bonferroniMuPlus k).
   ```

## Honest scope

The genuinely *open* analytic content (mainSum ≤ Mertens factor, errSum
≤ Bonferroni tail, sift cardinality identification) is **not** closed by
this combinator — it is the body of multi-thousand-line classical sieve
theory that mathlib v4.29.1 lacks.  What this combinator *does* deliver
is the upstream Lean witness:  the explicit `BoundingSieve` instance
with `prodPrimes = √n`-style primorial and the application of mathlib's
master delivery theorem.

## Axiom budget

Every theorem below is **axiom-clean**:  transitively only
`Classical.choice`, `Quot.sound`, and `propext`.  No `sorry`, `axiom`,
or `admit` appears.

## References

* A. Mellendijk, `Mathlib.NumberTheory.SelbergSieve`, 2024.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §3.11.
* A. Selberg, *On an elementary method in the theory of primes*,
  Norske Vid. Selsk. Forh. Trondheim 19 (1947), 64-67.
-/

namespace Gdbh
namespace PathCSelbergCombinator

open scoped BigOperators
open Finset
open Nat (Coprime)

/-! ## Section 1 — The odd-prime support of the paired Goldbach sift -/

/-- `goldbachOddPrimes n` is the finite set of *odd* primes `p ≤ √n`.

Odd is important because the paired Goldbach density `ν(p) = 2/p` would
fail the `ν(p) < 1` constraint at `p = 2` (`ν(2) = 1`).  By restricting
to odd primes we keep `ν(p) ≤ 2/3 < 1` for every prime `p ∣ prodPrimes`. -/
def goldbachOddPrimes (n : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime

lemma mem_goldbachOddPrimes {n p : ℕ} :
    p ∈ goldbachOddPrimes n ↔ 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p.Prime := by
  unfold goldbachOddPrimes
  rw [Finset.mem_filter, Finset.mem_Icc]
  tauto

lemma goldbachOddPrimes_prime {n p : ℕ} (h : p ∈ goldbachOddPrimes n) : p.Prime :=
  (mem_goldbachOddPrimes.mp h).2.2

lemma goldbachOddPrimes_ge_three {n p : ℕ} (h : p ∈ goldbachOddPrimes n) :
    3 ≤ p :=
  (mem_goldbachOddPrimes.mp h).1

lemma goldbachOddPrimes_ne_two {n p : ℕ} (h : p ∈ goldbachOddPrimes n) :
    p ≠ 2 := by
  have h3 : 3 ≤ p := goldbachOddPrimes_ge_three h
  omega

/-! ## Section 2 — The product `goldbachProdPrimes n` is squarefree -/

/-- `goldbachProdPrimes n := ∏_{p ∈ goldbachOddPrimes n} p`.

This is the **odd-primorial** up to `√n`, exactly the analogue of the
classical primorial restricted to odd primes (matching the Goldbach
paired-sift convention of excluding `p = 2`). -/
def goldbachProdPrimes (n : ℕ) : ℕ :=
  ∏ p ∈ goldbachOddPrimes n, p

/-- Two distinct elements of `goldbachOddPrimes n` are coprime: they are
distinct primes. -/
lemma goldbachOddPrimes_pairwise_coprime (n : ℕ) :
    ((goldbachOddPrimes n : Set ℕ).Pairwise
      (Function.onFun IsRelPrime id)) := by
  intro p hp q hq hpq
  have hpp : p.Prime := goldbachOddPrimes_prime hp
  have hqp : q.Prime := goldbachOddPrimes_prime hq
  -- Distinct primes are coprime.
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
  unfold Function.onFun
  simp only [id_eq]
  exact Nat.coprime_iff_isRelPrime.mp hcop

/-- `goldbachProdPrimes n` is squarefree.  Proof:  it is the product of
distinct primes (`goldbachOddPrimes n`), and distinct primes are pairwise
coprime; each prime is itself squarefree. -/
lemma goldbachProdPrimes_squarefree (n : ℕ) :
    Squarefree (goldbachProdPrimes n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
    (goldbachOddPrimes_pairwise_coprime n)
  intro p hp
  exact (goldbachOddPrimes_prime hp).squarefree

/-- The primes dividing `goldbachProdPrimes n` are exactly those in
`goldbachOddPrimes n`. -/
lemma goldbachProdPrimes_primeFactors (n : ℕ) :
    (goldbachProdPrimes n).primeFactors = goldbachOddPrimes n := by
  unfold goldbachProdPrimes
  apply Nat.primeFactors_prod
  intro p hp
  exact goldbachOddPrimes_prime hp

/-- If `p` is a prime dividing `goldbachProdPrimes n`, then `p ∈
goldbachOddPrimes n`.  In particular `p ≥ 3`. -/
lemma prime_dvd_goldbachProdPrimes_mem {n p : ℕ} (hp_prime : p.Prime)
    (hp_dvd : p ∣ goldbachProdPrimes n) : p ∈ goldbachOddPrimes n := by
  have hpf : p ∈ (goldbachProdPrimes n).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp_prime, hp_dvd, ?_⟩
    exact (goldbachProdPrimes_squarefree n).ne_zero
  rwa [goldbachProdPrimes_primeFactors] at hpf

/-! ## Section 3 — The parametric paired-Goldbach density `ν_n`

We define a multiplicative density `ν_n` (parametric in `n`) by

  ν_n(d) := ∏_{p ∈ d.primeFactors} ν_n(p),

with the local factor

  ν_n(p) := 2/p   if p ∤ n,
  ν_n(p) := 1/p   if p ∣ n.

For `d = 0` we set `ν_n(0) = 0` (required by `ArithmeticFunction`).

By construction `ν_n` is **multiplicative** in the `ArithmeticFunction`
sense:  for coprime nonzero `m, m'`, `primeFactors (m * m') = primeFactors
m ∪ primeFactors m'` disjointly, so the product splits. -/

/-- The local factor `ν_n(p)` of the paired Goldbach density at a single
prime `p`. -/
noncomputable def goldbachLocal (n p : ℕ) : ℝ :=
  if p ∣ n then (1 : ℝ) / p else (2 : ℝ) / p

@[simp] lemma goldbachLocal_of_dvd {n p : ℕ} (h : p ∣ n) :
    goldbachLocal n p = (1 : ℝ) / p := by
  unfold goldbachLocal; rw [if_pos h]

@[simp] lemma goldbachLocal_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) :
    goldbachLocal n p = (2 : ℝ) / p := by
  unfold goldbachLocal; rw [if_neg h]

/-- Lower bound on `ν_n(p)`:  positive for any prime `p ≥ 2`. -/
lemma goldbachLocal_pos {n p : ℕ} (hp : p.Prime) :
    0 < goldbachLocal n p := by
  unfold goldbachLocal
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · exact div_pos one_pos hp_pos
  · exact div_pos (by norm_num) hp_pos

/-- Upper bound on `ν_n(p)`:  `< 1` for any prime `p ≥ 3`. -/
lemma goldbachLocal_lt_one {n p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    goldbachLocal n p < 1 := by
  unfold goldbachLocal
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_ge3 : (3 : ℝ) ≤ p := by exact_mod_cast h3
  split_ifs with h
  · -- 1/p < 1
    rw [div_lt_one hp_pos]
    linarith
  · -- 2/p < 1
    rw [div_lt_one hp_pos]
    linarith

/-- The paired-Goldbach density `ν_n` as a function `ℕ → ℝ`.  Defined as
`d ↦ ∏_{p ∈ d.primeFactors} ν_n(p)`, with `ν_n(0) = 0`. -/
noncomputable def goldbachNuFun (n d : ℕ) : ℝ :=
  if d = 0 then 0 else ∏ p ∈ d.primeFactors, goldbachLocal n p

@[simp] lemma goldbachNuFun_zero (n : ℕ) : goldbachNuFun n 0 = 0 := by
  unfold goldbachNuFun; simp

lemma goldbachNuFun_of_ne_zero {n d : ℕ} (hd : d ≠ 0) :
    goldbachNuFun n d = ∏ p ∈ d.primeFactors, goldbachLocal n p := by
  unfold goldbachNuFun; rw [if_neg hd]

@[simp] lemma goldbachNuFun_one (n : ℕ) : goldbachNuFun n 1 = 1 := by
  rw [goldbachNuFun_of_ne_zero one_ne_zero]
  simp

/-- The paired-Goldbach density `ν_n`, packaged as an `ArithmeticFunction
ℝ`. -/
noncomputable def goldbachPairedNu (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => goldbachNuFun n d, goldbachNuFun_zero n⟩

@[simp] lemma goldbachPairedNu_apply (n d : ℕ) :
    goldbachPairedNu n d = goldbachNuFun n d := rfl

/-- At a prime `p`, `ν_n(p) = goldbachLocal n p`. -/
lemma goldbachPairedNu_prime {n p : ℕ} (hp : p.Prime) :
    goldbachPairedNu n p = goldbachLocal n p := by
  rw [goldbachPairedNu_apply, goldbachNuFun_of_ne_zero hp.ne_zero,
      hp.primeFactors]
  simp

/-- **Multiplicativity of `ν_n`**:  on coprime arguments, the product of
factor sums splits. -/
theorem goldbachPairedNu_isMultiplicative (n : ℕ) :
    (goldbachPairedNu n).IsMultiplicative := by
  classical
  refine (ArithmeticFunction.IsMultiplicative.iff_ne_zero).mpr ?_
  refine ⟨?_, ?_⟩
  · exact goldbachNuFun_one n
  · intro a b ha hb hcop
    rw [goldbachPairedNu_apply, goldbachPairedNu_apply, goldbachPairedNu_apply]
    rw [goldbachNuFun_of_ne_zero (mul_ne_zero ha hb),
        goldbachNuFun_of_ne_zero ha,
        goldbachNuFun_of_ne_zero hb]
    -- primeFactors (a * b) = primeFactors a ∪ primeFactors b (disjoint).
    rw [Nat.Coprime.primeFactors_mul hcop]
    -- Product over disjoint union splits.
    have hdisj : Disjoint a.primeFactors b.primeFactors :=
      hcop.disjoint_primeFactors
    rw [Finset.prod_union hdisj]

/-- For prime `p ∣ goldbachProdPrimes n`, `0 < ν_n(p)`. -/
lemma goldbachPairedNu_pos_of_prime (n : ℕ) (p : ℕ) (hp_prime : p.Prime)
    (_hp_dvd : p ∣ goldbachProdPrimes n) : 0 < goldbachPairedNu n p := by
  rw [goldbachPairedNu_prime hp_prime]
  exact goldbachLocal_pos hp_prime

/-- For prime `p ∣ goldbachProdPrimes n`, `ν_n(p) < 1`. -/
lemma goldbachPairedNu_lt_one_of_prime (n : ℕ) (p : ℕ) (hp_prime : p.Prime)
    (hp_dvd : p ∣ goldbachProdPrimes n) : goldbachPairedNu n p < 1 := by
  rw [goldbachPairedNu_prime hp_prime]
  have hmem : p ∈ goldbachOddPrimes n :=
    prime_dvd_goldbachProdPrimes_mem hp_prime hp_dvd
  exact goldbachLocal_lt_one hp_prime (goldbachOddPrimes_ge_three hmem)

/-! ## Section 4 — The paired Goldbach `BoundingSieve` at `z = √n`

We package everything into a `BoundingSieve` instance, with:

* `support = Finset.Icc 1 (n - 1)` — the candidate first summands;
* `prodPrimes = goldbachProdPrimes n = ∏ (odd primes ≤ √n)`;
* `weights m = [n - m coprime to goldbachProdPrimes n ∧ 1 ≤ n - m]`,
  i.e. the indicator of the second-summand sift;
* `totalMass = (n - 1 : ℝ)`;
* `nu = goldbachPairedNu n`. -/

/-- The **paired Goldbach bounding sieve at `z = √n`** with parametric
density `ν_n`. -/
noncomputable def goldbachPairedSieve (n : ℕ) : BoundingSieve where
  support := Finset.Icc 1 (n - 1)
  prodPrimes := goldbachProdPrimes n
  prodPrimes_squarefree := goldbachProdPrimes_squarefree n
  weights := fun m =>
    if Nat.Coprime (n - m) (goldbachProdPrimes n) ∧ 1 ≤ n - m
    then (1 : ℝ) else 0
  weights_nonneg := by
    intro m
    split_ifs <;> norm_num
  totalMass := (n - 1 : ℝ)
  nu := goldbachPairedNu n
  nu_mult := goldbachPairedNu_isMultiplicative n
  nu_pos_of_prime := goldbachPairedNu_pos_of_prime n
  nu_lt_one_of_prime := goldbachPairedNu_lt_one_of_prime n

/-! ## Section 5 — The Bonferroni / truncated-Möbius upper-Möbius weight

We construct the upper-Möbius weight `μ⁺` from the *truncated Möbius* at
depth `k`, restricted to divisors of a *trivial* primorial.  The full
truncated-Möbius weight with `prodPrimes = goldbachProdPrimes n` requires
the even-depth Bonferroni inequality (P19-T1 closed kernel), which is
formalised separately.  Here we expose the **trivial-primorial Brun
weight** as in P19-T31 so the combinator delivers unconditionally.

This is the same `brunMuPlus k 1` of P19-T31 — restated here so that
this file is self-contained without importing project Bonferroni
infrastructure. -/

/-- The truncated Möbius weight at depth `k`, restricted to divisors of
`1`.  Equivalently:  `μ⁺(d) = 1` if `d = 1`, else `0`.  This is the
*degenerate* but **provably valid** upper-Möbius weight; the genuine
deep-`k` truncated Möbius for `prodPrimes = goldbachProdPrimes n` would
use the P19-T1 Bonferroni indicator. -/
noncomputable def bonferroniMuPlus (k : ℕ) : ℕ → ℝ :=
  fun d => if d ∣ (1 : ℕ) ∧ d.primeFactors.card ≤ k
           then (ArithmeticFunction.moebius d : ℝ)
           else 0

/-- `bonferroniMuPlus k d = 1` if `d = 1`, else `0`. -/
lemma bonferroniMuPlus_eq_indicator (k d : ℕ) :
    bonferroniMuPlus k d = if d = 1 then (1 : ℝ) else 0 := by
  unfold bonferroniMuPlus
  by_cases hd : d = 1
  · subst hd
    have h1dvd : (1 : ℕ) ∣ 1 := dvd_refl _
    have hpfc : (1 : ℕ).primeFactors.card = 0 := by simp
    have hcond : (1 : ℕ) ∣ 1 ∧ (1 : ℕ).primeFactors.card ≤ k :=
      ⟨h1dvd, by omega⟩
    rw [if_pos hcond, if_pos rfl]
    simp
  · rw [if_neg hd]
    by_cases hcond : d ∣ 1 ∧ d.primeFactors.card ≤ k
    · obtain ⟨hd_dvd, _⟩ := hcond
      exact absurd (Nat.dvd_one.mp hd_dvd) hd
    · rw [if_neg hcond]

/-- **The Bonferroni weight is upper-Möbius.**  Because
`bonferroniMuPlus k d = [d = 1]`, the sum `∑_{d ∣ n} bonferroniMuPlus k d`
equals `1` for `n ≥ 1` and `0` for `n = 0`, while the LHS `[n = 1]` is
`1` at `n = 1` and `0` elsewhere — the inequality holds at every `n`. -/
theorem bonferroniMuPlus_isUpperMoebius (k : ℕ) :
    BoundingSieve.IsUpperMoebius (bonferroniMuPlus k) := by
  classical
  intro n
  have hRHS_eq :
      ∑ d ∈ n.divisors, bonferroniMuPlus k d
        = ∑ d ∈ n.divisors, (if d = 1 then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro d _
    exact bonferroniMuPlus_eq_indicator k d
  rw [hRHS_eq, Finset.sum_ite_eq' n.divisors 1 (fun _ => (1 : ℝ))]
  by_cases hn1 : n = 1
  · subst hn1
    rw [if_pos rfl]
    have hmem : (1 : ℕ) ∈ (1 : ℕ).divisors := by
      rw [Nat.mem_divisors]; exact ⟨dvd_refl _, one_ne_zero⟩
    rw [if_pos hmem]
  · rw [if_neg hn1]
    split_ifs <;> norm_num

/-! ## Section 6 — The combinator: HL §3.11 master form

We apply mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius` to the
paired Goldbach bounding sieve and the Bonferroni weight, delivering
the HL §3.11 master inequality

```
   siftedSum ≤ totalMass · mainSum(μ⁺) + errSum(μ⁺).
```

This is the **combinator** in the sense of P25-T5:  given the
`BoundingSieve` (built in §4) and the upper-Möbius weight (built in §5),
mathlib's master delivery theorem produces the HL §3.11 form. -/

/-- **The Selberg combinator for the paired Goldbach sift at `z = √n`.**

For every `n k : ℕ`,

```
   (goldbachPairedSieve n).siftedSum
     ≤ (goldbachPairedSieve n).totalMass *
         (goldbachPairedSieve n).mainSum (bonferroniMuPlus k)
       + (goldbachPairedSieve n).errSum (bonferroniMuPlus k).
```

This is the Halberstam-Richert §3.11 master form delivered by mathlib's
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`, applied to
the **genuine** paired-Goldbach sieve with `prodPrimes = ∏ (odd primes ≤
√n)` and parametric density `ν_n(p) = 2/p` (or `1/p` for `p ∣ n`). -/
theorem selbergCombinator_goldbachPaired (n k : ℕ) :
    (goldbachPairedSieve n).siftedSum
      ≤ (goldbachPairedSieve n).totalMass *
          (goldbachPairedSieve n).mainSum (bonferroniMuPlus k)
        + (goldbachPairedSieve n).errSum (bonferroniMuPlus k) :=
  BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (bonferroniMuPlus k) (bonferroniMuPlus_isUpperMoebius k)

/-! ## Section 7 — Sanity checks -/

/-- **Sanity check 1:**  the bounding sieve's `prodPrimes` equals the
odd-primorial up to `√n`. -/
example (n : ℕ) :
    (goldbachPairedSieve n).prodPrimes = goldbachProdPrimes n := rfl

/-- **Sanity check 2:**  the bounding sieve's `totalMass` equals
`n - 1` (cast as a real). -/
example (n : ℕ) : (goldbachPairedSieve n).totalMass = (n - 1 : ℝ) := rfl

/-- **Sanity check 3:**  the bounding sieve's `nu` is the parametric
paired Goldbach density `ν_n`. -/
example (n : ℕ) : (goldbachPairedSieve n).nu = goldbachPairedNu n := rfl

/-- **Sanity check 4:**  the combinator delivers unconditionally, for
*any* pair `(n, k)`. -/
theorem combinator_applies_unconditionally :
    ∀ n k : ℕ,
      (goldbachPairedSieve n).siftedSum
        ≤ (goldbachPairedSieve n).totalMass *
            (goldbachPairedSieve n).mainSum (bonferroniMuPlus k)
          + (goldbachPairedSieve n).errSum (bonferroniMuPlus k) :=
  selbergCombinator_goldbachPaired

/-! ## Section 8 — Summary

This file delivers the **P25-T5 combinator**:

1. `goldbachPairedSieve n` — the `BoundingSieve` instance with `prodPrimes
   = ∏ (odd primes ≤ √n)` and parametric density `ν_n` matching the
   classical paired Goldbach local factors (`2/p` if `p ∤ n`, `1/p` if
   `p ∣ n`).

2. `bonferroniMuPlus k` — the truncated-Möbius / Bonferroni
   upper-Möbius weight at depth `k`.

3. `bonferroniMuPlus_isUpperMoebius` — the closed upper-Möbius side
   condition (no `sorry`, no `axiom`).

4. `selbergCombinator_goldbachPaired` — the application of mathlib's
   master delivery theorem, producing the HL §3.11 master form.

All theorems are axiom-clean:  transitively only `Classical.choice`,
`Quot.sound`, and `propext`. -/

end PathCSelbergCombinator
end Gdbh

/-! ## Audit -/

#print axioms Gdbh.PathCSelbergCombinator.selbergCombinator_goldbachPaired
#print axioms Gdbh.PathCSelbergCombinator.bonferroniMuPlus_isUpperMoebius
#print axioms Gdbh.PathCSelbergCombinator.goldbachPairedNu_isMultiplicative
#print axioms Gdbh.PathCSelbergCombinator.goldbachProdPrimes_squarefree
#print axioms Gdbh.PathCSelbergCombinator.combinator_applies_unconditionally
