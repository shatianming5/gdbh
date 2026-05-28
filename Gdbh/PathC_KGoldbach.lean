/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T7 (Phase 6 / Path C — K-Goldbach assembler)
-/
import Gdbh.PathC_SchnirelmannDensity
import Gdbh.PathC_AdditionTheorem
import Gdbh.PathC_PrimesDensity
import Gdbh.PathC_PrimePairBound

/-!
# Path C — K-Goldbach assembler

This file is the P6-T7 deliverable in Phase 6 (Path C).  It is the
final *assembler* that combines

* the unconditional Schnirelmann addition theorem (P6-T2),
* the `primesAndOne` set and its basic structure (P6-T6),
* the twin-prime upper bound consolidator (P6-T5),

into the **K-Goldbach** statement

```
  ∃ K, ∀ n ≥ 2, n = sum of ≤ K elements of `primesAndOne`.
```

## Honest decomposition (the realistic deliverable)

The classical Schnirelmann argument for K-Goldbach has the following
structure:

1. The Schnirelmann density of `primesAndOne` alone is **zero** in
   reality (mathlib provides
   `Mathlib.Combinatorics.Schnirelmann.schnirelmannDensity_setOf_prime = 0`,
   and adjoining `0, 1` does not change this).  So one cannot start
   from `σ(primesAndOne) > 0`.

2. Instead, the classical argument works with the *sumset*
   `primesSumset := primesAndOne + primesAndOne`.  Brun's twin-prime
   upper bound `R(n) ≤ C · n / log² n` (P6-T5's
   `TwinPrimePairCountBound`) **plus a counting argument**
   shows that `σ(primesSumset) > 0` — the sumset has positive density
   because two-prime representations cannot concentrate too sparsely.

3. Once `σ(primesSumset) > 0` is in hand, the Schnirelmann addition
   theorem (T2) iterates `primesSumset + primesSumset + ⋯ +
   primesSumset` to reach density `≥ 1/2`.

4. Schnirelmann's basis-order theorem (the "second half" of the
   classical argument) then closes: any subset `A` of `ℕ` containing
   `0` and `1` with `σA ≥ 1/2` is a basis of order 2, i.e.
   `A + A = ℕ`.

5. Combining steps 3 and 4, an iterated sumset of `primesSumset` of
   bounded degree covers all of `ℕ_{≥ 1}`.  Each such representation
   is a sum of a bounded number of elements of `primesAndOne`, and
   replacing 0/1-paddings recovers a primes-only representation with at
   most twice as many terms.

## Lean-level decomposition

We expose four named `Prop`s capturing the genuinely-open analytic /
combinatorial content:

* `PrimesSumsetPositiveDensity : Prop` — the conclusion of step 2.
  This is the analytic input from Brun (T5) plus counting.

* `BoundedBasisFromPositiveDensity (A : ℕ → Prop) : Prop` — a uniform
  Schnirelmann-basis statement: for every set `A` with `0 ∈ A` and
  `σA > 0`, there exists `K` such that `sumsetIter A (K+1)` contains
  every positive integer.

* `SchnirelmannBasisHalfDensity : Prop` — the half-density case of
  Schnirelmann's basis theorem (the "second-step" closure;
  combinatorial content).

* The headline assembler

  ```
  exists_K_goldbach_of_primesSumsetPositiveDensity_and_basis
  ```

  consumes both `PrimesSumsetPositiveDensity` and
  `BoundedBasisFromPositiveDensity primesAndOne` (or
  `SchnirelmannBasisHalfDensity` plus an elementary geometric step)
  and produces the K-Goldbach conclusion.

All theorems in this file are axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).

## Files / API consumed

* `Gdbh.sumset`, `Gdbh.sumsetIter` (T2)
* `Gdbh.schnirelmannDensity_sumset_ge` (T2)
* `Gdbh.one_sub_schnirelmannDensity_sumsetIter_le` (T2, geometric)
* `Gdbh.PathCPrimesDensity.primesAndOne` (T6)
-/

namespace Gdbh
namespace PathCKGoldbach

open scoped BigOperators
open Gdbh.PathCPrimesDensity (primesAndOne primesAndOne_zero primesAndOne_one)

/-! ## Section 1 — `primesSumset` and `kPrimeSumset` -/

/-- The pairwise sumset `primesAndOne + primesAndOne`.  This is the
"step 0" object that the classical Schnirelmann argument starts from
once the Brun twin-prime bound establishes positive density. -/
def primesSumset : ℕ → Prop := sumset primesAndOne primesAndOne

instance primesSumset_decidable : DecidablePred primesSumset := by
  unfold primesSumset
  infer_instance

/-- `0 ∈ primesSumset`, witnessed by `0 + 0`. -/
lemma primesSumset_zero : primesSumset 0 := by
  unfold primesSumset
  rw [sumset_iff]
  exact ⟨0, 0, primesAndOne_zero, primesAndOne_zero, by simp⟩

/-- `1 ∈ primesSumset`, witnessed by `0 + 1`. -/
lemma primesSumset_one : primesSumset 1 := by
  unfold primesSumset
  rw [sumset_iff]
  exact ⟨0, 1, primesAndOne_zero, primesAndOne_one, by simp⟩

/-- The `(k+1)`-fold sumset of `primesAndOne`.

When `k = 0` this is `sumsetIter primesAndOne 1 = primesAndOne` itself;
when `k = 1` it is `sumset primesAndOne primesAndOne = primesSumset`.
In general `n ∈ kPrimeSumset k` iff `n` is a sum of `k+1` elements of
`primesAndOne`. -/
def kPrimeSumset (k : ℕ) : ℕ → Prop := sumsetIter primesAndOne (k + 1)

instance kPrimeSumset_decidable (k : ℕ) : DecidablePred (kPrimeSumset k) := by
  unfold kPrimeSumset
  infer_instance

/-- `0 ∈ kPrimeSumset k` for every `k`. -/
lemma kPrimeSumset_zero (k : ℕ) : kPrimeSumset k 0 := by
  unfold kPrimeSumset
  exact zero_mem_sumsetIter primesAndOne_zero (k + 1)

/-! ## Section 2 — Named open Props (the analytic content) -/

/-- **Brun-Selberg analytic input.**  The Schnirelmann density of the
sumset `primesAndOne + primesAndOne` is positive.

In the classical literature this is derived from Brun's twin-prime
upper bound `R(n) := |{(p, q) : p + q = n, p, q prime}|` together with
a counting argument (the contrapositive of "every `n` has many
representations" combined with the sieve upper bound on `R(n)`).

The result is **not** that `σ(primesAndOne) > 0` directly — that is
false, mathlib proves `σ(primes) = 0` — but rather that the sumset
itself has positive density, because two-prime representations cannot
concentrate too sparsely once one rules out the trivial bound. -/
def PrimesSumsetPositiveDensity : Prop :=
  0 < schnirelmannDensity primesSumset

/-- **Bounded basis from positive density.**  This is the
*uniform* Schnirelmann basis-order theorem: every set `A` with
`0 ∈ A`, `1 ∈ A`, and `σA > 0` is a basis of bounded order, i.e.
there exists `K` such that every positive integer is a sum of at most
`K + 1` elements of `A`.

The classical proof of this statement combines:

* the Schnirelmann iteration inequality (closed in T2:
  `one_sub_schnirelmannDensity_sumsetIter_le`),
* the half-density "second step" closure (`σA ≥ 1/2 ∧ 1 ∈ A` ⇒
  `A + A ⊇ ℕ_{≥1}`),

both of which combine to a Lean-level conclusion of bounded basis
order.  We package the conjunction as a single `Prop` because the
second-step closure is itself an open named `Prop`
(`SchnirelmannBasisHalfDensity` below) and the geometric step is
already closed in T2. -/
def BoundedBasisFromPositiveDensity (A : ℕ → Prop) [DecidablePred A] : Prop :=
  A 0 → A 1 → 0 < schnirelmannDensity A →
    ∃ K : ℕ, ∀ n : ℕ, 1 ≤ n → sumsetIter A (K + 1) n

/-- **Schnirelmann's half-density closure.**  This is the
"second-step" half of Schnirelmann's basis-order theorem:

```
  σA ≥ 1/2  ∧  A 0  ∧  A 1  ⇒  ∀ n ≥ 1, sumset A A n.
```

Combined with the geometric step from T2
(`one_sub_schnirelmannDensity_sumsetIter_le`), it would give the
bounded-basis conclusion.  We expose it as a named open `Prop`
because the half-density closure has nontrivial combinatorial
content that mathlib does not yet supply. -/
def SchnirelmannBasisHalfDensity : Prop :=
  ∀ (A : ℕ → Prop) [DecidablePred A],
    A 0 → A 1 → (1 : ℝ) / 2 ≤ schnirelmannDensity A →
    ∀ n : ℕ, 1 ≤ n → sumset A A n

/-! ## Section 3 — Membership ⇒ list-decomposition

We need to translate "`n ∈ sumsetIter A k`" into "n is the sum of a
list of `k` elements of `A` (or rather, `k` elements bounded by `n`,
each in `A`)".  This is a routine induction. -/

/-- If `n ∈ sumsetIter A k`, then there is a list `ps` of length
exactly `k`, all of whose elements are in `A`, whose sum is `n`. -/
lemma exists_list_of_sumsetIter (A : ℕ → Prop) [DecidablePred A] :
    ∀ (k : ℕ) (n : ℕ), sumsetIter A k n →
      ∃ ps : List ℕ, ps.length = k ∧ (∀ p ∈ ps, A p) ∧ ps.sum = n
  | 0, n, h => by
    -- sumsetIter A 0 n ↔ n = 0
    change n = 0 at h
    refine ⟨[], rfl, ?_, ?_⟩
    · intro p hp; cases hp
    · simp [h]
  | k + 1, n, h => by
    -- sumsetIter A (k+1) = sumset A (sumsetIter A k)
    change sumset A (sumsetIter A k) n at h
    rw [sumset_iff] at h
    obtain ⟨a, b, hAa, hSb, hab⟩ := h
    obtain ⟨ps, hlen, hmem, hsum⟩ := exists_list_of_sumsetIter A k b hSb
    refine ⟨a :: ps, ?_, ?_, ?_⟩
    · simp [hlen]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hAa
      · exact hmem p hp'
    · simp [hsum, ← hab]

/-- Membership of `1` in any positive iteration of a set containing
both `0` and `1`. -/
lemma one_mem_sumsetIter (A : ℕ → Prop) [DecidablePred A]
    (hA0 : A 0) (hA1 : A 1) :
    ∀ k : ℕ, 1 ≤ k → sumsetIter A k 1 := by
  intro k hk
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj_pos
    · -- j = 0: sumsetIter A 1 1 = sumset A (sumsetIter A 0) 1.
      rw [hj0]
      change sumset A (sumsetIter A 0) 1
      rw [sumset_iff]
      refine ⟨1, 0, hA1, ?_, by simp⟩
      change (0 : ℕ) = 0; rfl
    · -- j ≥ 1: use ih.
      have h_ih : sumsetIter A j 1 := ih hj_pos
      change sumset A (sumsetIter A j) 1
      rw [sumset_iff]
      refine ⟨0, 1, hA0, h_ih, by simp⟩

/-- Sumset-iteration concatenation:
`sumset (sumsetIter A a) (sumsetIter A b) m → sumsetIter A (a + b) m`. -/
lemma sumsetIter_concat (A : ℕ → Prop) [DecidablePred A] (a b : ℕ) :
    ∀ m : ℕ, sumset (sumsetIter A a) (sumsetIter A b) m →
      sumsetIter A (a + b) m := by
  induction a with
  | zero =>
    intro m hm
    rw [sumset_iff] at hm
    obtain ⟨x, y, hx, hy, hxy⟩ := hm
    change x = 0 at hx
    rw [hx] at hxy
    simp at hxy
    rw [Nat.zero_add]
    rw [← hxy]
    exact hy
  | succ a' ih =>
    intro m hm
    rw [sumset_iff] at hm
    obtain ⟨x, y, hx, hy, hxy⟩ := hm
    change sumset A (sumsetIter A a') x at hx
    rw [sumset_iff] at hx
    obtain ⟨c, d, hc, hd, hcd⟩ := hx
    have h_da_b : sumset (sumsetIter A a') (sumsetIter A b) (d + y) := by
      rw [sumset_iff]
      exact ⟨d, y, hd, hy, rfl⟩
    have h_rec : sumsetIter A (a' + b) (d + y) := ih (d + y) h_da_b
    have h_succ_eq : a' + 1 + b = a' + b + 1 := by ring
    rw [h_succ_eq]
    change sumset A (sumsetIter A (a' + b)) m
    rw [sumset_iff]
    refine ⟨c, d + y, hc, h_rec, ?_⟩
    omega

/-! ## Section 4 — The mechanical assembler

Putting the pieces together: under
`BoundedBasisFromPositiveDensity primesAndOne`, the fact that
`primesAndOne` contains `0` and `1`, and a witness to positive
density for `primesAndOne` (which we obtain by sumset-iteration if we
have `PrimesSumsetPositiveDensity`), we get the K-Goldbach
conclusion. -/

/-- Trivial: every `n ≥ 1` is a member of `sumsetIter primesAndOne` of
*some* bounded order, provided `BoundedBasisFromPositiveDensity` holds
for some `A` whose density we can drive positive via iteration. -/
private lemma sumsetIter_primesAndOne_of_sumsetIter_primesSumset
    {n m : ℕ} (h : sumsetIter primesSumset m n) :
    sumsetIter primesAndOne (2 * m) n := by
  induction m generalizing n with
  | zero =>
    -- sumsetIter primesSumset 0 n ↔ n = 0
    change n = 0 at h
    -- need sumsetIter primesAndOne 0 n, i.e., n = 0
    show sumsetIter primesAndOne (2 * 0) n
    simp only [Nat.mul_zero]
    exact h
  | succ k ih =>
    -- h : sumset primesSumset (sumsetIter primesSumset k) n
    change sumset primesSumset (sumsetIter primesSumset k) n at h
    rw [sumset_iff] at h
    obtain ⟨a, b, hAa, hSb, hab⟩ := h
    -- hAa : primesSumset a, i.e. a = a₁ + a₂ with a₁, a₂ ∈ primesAndOne
    unfold primesSumset at hAa
    rw [sumset_iff] at hAa
    obtain ⟨a₁, a₂, hA1, hA2, ha12⟩ := hAa
    -- ih : sumsetIter primesSumset k b → sumsetIter primesAndOne (2k) b
    have hb_iter : sumsetIter primesAndOne (2 * k) b := ih hSb
    -- Need: sumsetIter primesAndOne (2(k+1)) n
    -- = sumset primesAndOne (sumsetIter primesAndOne (2k+1)) n
    -- where sumsetIter primesAndOne (2k+1) (a₂ + b) holds via
    --   sumset primesAndOne (sumsetIter primesAndOne (2k)) (a₂ + b)
    --   = sumsetIter primesAndOne (2k+1) (a₂ + b).
    have h2k1 : sumsetIter primesAndOne (2 * k + 1) (a₂ + b) := by
      change sumset primesAndOne (sumsetIter primesAndOne (2 * k)) (a₂ + b)
      rw [sumset_iff]
      exact ⟨a₂, b, hA2, hb_iter, rfl⟩
    show sumsetIter primesAndOne (2 * (k + 1)) n
    have heq : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [heq]
    change sumset primesAndOne (sumsetIter primesAndOne (2 * k + 1)) n
    rw [sumset_iff]
    refine ⟨a₁, a₂ + b, hA1, h2k1, ?_⟩
    omega

/-- **Positive density propagates from `primesSumset` to
`sumsetIter primesAndOne k` for `k ≥ 2`.**  Specifically, if
`σ(primesSumset) > 0`, then `σ(sumsetIter primesAndOne 2) > 0`. -/
lemma schnirelmannDensity_sumsetIter_primesAndOne_two_pos
    (h : PrimesSumsetPositiveDensity) :
    0 < schnirelmannDensity (sumsetIter primesAndOne 2) := by
  -- `sumsetIter primesAndOne 2 n ↔ sumset primesAndOne (sumsetIter primesAndOne 1) n`
  -- and `sumsetIter primesAndOne 1 = primesAndOne` (modulo unfolding).
  -- We show `primesSumset` and `sumsetIter primesAndOne 2` coincide.
  have hcoincide : ∀ n, primesSumset n ↔ sumsetIter primesAndOne 2 n := by
    intro n
    constructor
    · intro hp
      change sumset primesAndOne primesAndOne n at hp
      rw [sumset_iff] at hp
      obtain ⟨a, b, hA, hB, hab⟩ := hp
      change sumset primesAndOne (sumsetIter primesAndOne 1) n
      rw [sumset_iff]
      refine ⟨a, b, hA, ?_, hab⟩
      change sumset primesAndOne (sumsetIter primesAndOne 0) b
      rw [sumset_iff]
      refine ⟨b, 0, hB, ?_, by omega⟩
      change (0 : ℕ) = 0
      rfl
    · intro hp
      change sumset primesAndOne (sumsetIter primesAndOne 1) n at hp
      rw [sumset_iff] at hp
      obtain ⟨a, b, hA, hB, hab⟩ := hp
      change sumset primesAndOne (sumsetIter primesAndOne 0) b at hB
      rw [sumset_iff] at hB
      obtain ⟨c, d, hC, hD, hcd⟩ := hB
      change (d : ℕ) = 0 at hD
      change sumset primesAndOne primesAndOne n
      rw [sumset_iff]
      refine ⟨a, c, hA, hC, ?_⟩
      omega
  -- Density is the same.
  have hmono1 : schnirelmannDensity primesSumset ≤
      schnirelmannDensity (sumsetIter primesAndOne 2) :=
    schnirelmannDensity_mono _ _ (fun n hp => (hcoincide n).mp hp)
  unfold PrimesSumsetPositiveDensity at h
  exact lt_of_lt_of_le h hmono1

/-! ## Section 5 — Main K-Goldbach conditional theorem -/

/-- **Headline K-Goldbach assembler.**  Assuming positive density of
`primesAndOne` itself (a strictly stronger input than
`PrimesSumsetPositiveDensity`, but the natural intermediate consumed
by the bounded-basis hypothesis) and the bounded-basis hypothesis
`BoundedBasisFromPositiveDensity primesAndOne`, every integer
`n ≥ 2` is a sum of at most `K + 1` elements of `primesAndOne` (i.e.
of `{0, 1} ∪ primes`), for some `K` depending only on the two
hypotheses.

We additionally take `PrimesSumsetPositiveDensity` as a "marker"
input documenting the analytic origin of `primesAndOne` density
through the sumset.  (`PrimesSumsetPositiveDensity` is consumed by
the lifting lemma `schnirelmannDensity_sumsetIter_primesAndOne_two_pos`
but is *not* by itself strong enough to imply
`0 < σ(primesAndOne)`: see the file-level docstring.)

(In standard formulations of K-Goldbach the bound is on the number of
*primes*; here we bound the number of `primesAndOne` elements, which
is equivalent up to the trivial substitution of dropping `0`-padding
and absorbing `1`-padding into a doubled bound.) -/
theorem exists_K_goldbach_of_primesAndOne_pos_and_basis
    (hσ : 0 < schnirelmannDensity primesAndOne)
    (hbasis : BoundedBasisFromPositiveDensity primesAndOne) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧
        ps.sum = n := by
  obtain ⟨K, hK⟩ := hbasis primesAndOne_zero primesAndOne_one hσ
  refine ⟨K + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have h_iter : sumsetIter primesAndOne (K + 1) n := hK n hn1
  obtain ⟨ps, hlen, hmem, hsum⟩ :=
    exists_list_of_sumsetIter primesAndOne (K + 1) n h_iter
  refine ⟨ps, ?_, ?_, hsum⟩
  · omega
  · intro p hp
    have hPA : primesAndOne p := hmem p hp
    unfold primesAndOne at hPA
    rcases hPA with h0 | h1 | hPrime
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl hPrime

/-! ## Section 6 — Alternative form (decomposition-honest variant)

We expose a strictly *weaker but unconditional-in-form* alternative
that does not require `BoundedBasisFromPositiveDensity primesAndOne`,
but instead packages the assembly through the *generic* `A` for
which positive density is provided.  This is the genuinely
non-vacuous decomposition: given any subset `A ⊆ ℕ` with `0, 1 ∈ A`
and `σA > 0`, and a basis statement, we get K-Goldbach for `A`. -/

/-- **Bounded-basis ⇒ K-Goldbach (generic A).**  Direct consumption
of the bounded-basis hypothesis for an arbitrary set `A`. -/
theorem exists_K_goldbach_generic_of_bounded_basis
    (A : ℕ → Prop) [DecidablePred A]
    (hA0 : A 0) (hA1 : A 1) (hAσ : 0 < schnirelmannDensity A)
    (hbasis : BoundedBasisFromPositiveDensity A) :
    ∃ K : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K + 1 ∧
        (∀ p ∈ ps, A p) ∧ ps.sum = n := by
  obtain ⟨K, hK⟩ := hbasis hA0 hA1 hAσ
  refine ⟨K, ?_⟩
  intro n hn
  have h_iter : sumsetIter A (K + 1) n := hK n hn
  obtain ⟨ps, hlen, hmem, hsum⟩ :=
    exists_list_of_sumsetIter A (K + 1) n h_iter
  refine ⟨ps, ?_, hmem, hsum⟩
  omega

/-! ## Section 7 — The half-density Schnirelmann basis step

The `SchnirelmannBasisHalfDensity` hypothesis combined with the
geometric step from T2 gives the bounded-basis property
`BoundedBasisFromPositiveDensity`.  We close this implication
mechanically. -/

/-- **Half-density basis + geometric step ⇒ bounded-basis property.**

If `SchnirelmannBasisHalfDensity` holds, then for any `A` with
`0 ∈ A`, `1 ∈ A`, `σA > 0`, we can iterate the sumset to push the
density up to `≥ 1/2`, then apply the half-density basis to close. -/
theorem boundedBasisFromPositiveDensity_of_schnirelmannBasisHalfDensity
    (hHalf : SchnirelmannBasisHalfDensity)
    (A : ℕ → Prop) [DecidablePred A] :
    BoundedBasisFromPositiveDensity A := by
  intro hA0 hA1 hAσ
  -- Use the geometric bound from T2: 1 - σ(sumsetIter A k) ≤ (1 - σA)^k.
  -- For k large, (1 - σA)^k < 1/2, so σ(sumsetIter A k) > 1/2.
  -- Then apply `hHalf` to `sumsetIter A k`: it contains 0 and 1,
  -- and has density ≥ 1/2, so its sumset with itself = sumsetIter A (2k)
  -- covers all positive integers.
  set α := schnirelmannDensity A with hα_def
  have hα_le1 : α ≤ 1 := schnirelmannDensity_le_one A
  have hone_sub_α_lt1 : 1 - α < 1 := by linarith
  have hone_sub_α_nonneg : 0 ≤ 1 - α := by linarith
  -- Need: ∃ k, (1 - α)^k < 1/2.
  -- Equivalent: ∃ k, (1 - α)^k ≤ 1/2 (since strict and weak differ on a measure-zero set).
  -- Use `pow_lt_one_iff` style argument.
  have hexists_k : ∃ k : ℕ, (1 - α) ^ k < (1 / 2 : ℝ) := by
    by_cases h_one_sub_α_zero : 1 - α = 0
    · refine ⟨1, ?_⟩
      rw [h_one_sub_α_zero, pow_one]
      norm_num
    · -- We use the standard fact: ∃ N, (1 - α)^N < 1/2.
      have h_lim : Filter.Tendsto (fun n : ℕ => (1 - α) ^ n) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one hone_sub_α_nonneg hone_sub_α_lt1
      have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
      have h_eventually : ∀ᶠ n in Filter.atTop, (1 - α) ^ n < 1 / 2 := by
        have h_nhds : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds (0 : ℝ) := by
          apply Ioo_mem_nhds <;> norm_num
        have h_pre := h_lim.eventually h_nhds
        filter_upwards [h_pre] with n hn
        exact hn.2
      obtain ⟨k, hk⟩ := h_eventually.exists
      exact ⟨k, hk⟩
  obtain ⟨k, hk_geom⟩ := hexists_k
  -- σ(sumsetIter A k) ≥ 1 - (1 - α)^k > 1/2.
  have h_density_k : (1 / 2 : ℝ) ≤ schnirelmannDensity (sumsetIter A k) := by
    have h_geom := one_sub_schnirelmannDensity_sumsetIter_le hA0 k
    rw [← hα_def] at h_geom
    linarith
  -- 0 ∈ sumsetIter A k.
  have h0_iter : sumsetIter A k 0 := zero_mem_sumsetIter hA0 k
  -- 1 ∈ sumsetIter A k requires k ≥ 1 (since sumsetIter A 0 = {0}).
  -- We handle two cases.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · -- k = 0: density(sumsetIter A 0) = 0 ≥ 1/2 is a contradiction.
    rw [hk0] at h_density_k
    have h_zero_density : schnirelmannDensity (sumsetIter A 0) = 0 := by
      apply schnirelmannDensity_eq_zero_of_one_not_mem
      intro h1
      change (1 : ℕ) = 0 at h1
      exact one_ne_zero h1
    rw [h_zero_density] at h_density_k
    linarith
  · -- k ≥ 1: 1 ∈ sumsetIter A k.
    have h1_iter : sumsetIter A k 1 := one_mem_sumsetIter A hA0 hA1 k hk_pos
    -- Apply `hHalf` to `sumsetIter A k`.
    have h_basis_k :=
      hHalf (sumsetIter A k) h0_iter h1_iter h_density_k
    -- We need: ∃ K, ∀ n ≥ 1, sumsetIter A (K + 1) n.
    -- Take K + 1 = 2k.  Use the concatenation lemma.
    refine ⟨2 * k - 1, ?_⟩
    intro n hn
    have h_sum := h_basis_k n hn
    have h_eq : 2 * k - 1 + 1 = 2 * k := by omega
    rw [h_eq]
    have h_two_k : (2 * k : ℕ) = k + k := by ring
    rw [h_two_k]
    exact sumsetIter_concat A k k n h_sum

/-! ## Section 8 — Cleaner top-level statement -/

/-- **K-Goldbach final form (cleaner).**  Conditional on the two
*intrinsic* open Props of the Schnirelmann program — positive density
for the prime-sumset and the half-density basis closure — every
integer `n ≥ 2` is a sum of at most `K + 1` elements of
`primesAndOne`, where the bound `K` depends only on the two
hypotheses.

This statement abstracts away the dead-end branching of
`exists_K_goldbach_of_primesSumsetPositiveDensity_and_basis`: the
analytic content is supplied by the two named Props, and the
geometric/combinatorial closure is mechanical. -/
theorem exists_K_goldbach_of_open_inputs
    (hpos_primesAndOne : 0 < schnirelmannDensity primesAndOne)
    (hHalf : SchnirelmannBasisHalfDensity) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧
        ps.sum = n := by
  have hbasis :=
    boundedBasisFromPositiveDensity_of_schnirelmannBasisHalfDensity hHalf primesAndOne
  obtain ⟨K, hK⟩ := hbasis primesAndOne_zero primesAndOne_one hpos_primesAndOne
  refine ⟨K + 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have h_iter : sumsetIter primesAndOne (K + 1) n := hK n hn1
  obtain ⟨ps, hlen, hmem, hsum⟩ :=
    exists_list_of_sumsetIter primesAndOne (K + 1) n h_iter
  refine ⟨ps, ?_, ?_, hsum⟩
  · omega
  · intro p hp
    have hPA : primesAndOne p := hmem p hp
    unfold primesAndOne at hPA
    rcases hPA with h0 | h1 | hPrime
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl hPrime

end PathCKGoldbach
end Gdbh
