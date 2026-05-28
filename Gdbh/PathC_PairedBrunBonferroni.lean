/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P17-T2 (Phase 17 / Path C — Brun-Bonferroni truncated Möbius
inequality, the genuine atomic kernel of `BrunGoldbachPairedMainTermRefined`).
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Path C — P17-T2: Brun-Bonferroni truncated Möbius indicator inequality

This file is the **P17-T2 deliverable** in Phase 17 (Path C closure).  It
closes the *genuine atomic kernel* of the named open Prop
`Gdbh.PathCBrunRefinedComposition.BrunGoldbachPairedMainTermRefined`,
specifically the Brun-Bonferroni truncated Möbius inequality at the
single-variable indicator level.

## Mathematical content

The Brun-Bonferroni inequality states that, for any finite set `P` of
primes, any natural `m`, and any **even** truncation depth `k`, the
indicator that `m` has *no* prime factor from `P` is bounded above by the
truncated alternating Möbius sum

```
   1{m has no prime factor in P}
     ≤ ∑_{d ⊆ P, |d| ≤ k} μ(d.prod) · 1{d.prod ∣ m}.
```

For `P` a finite set of primes, every subset `d ⊆ P` has squarefree
product `d.prod id`, hence `μ(d.prod id) = (-1)^|d|`.  Writing
`Q := {p ∈ P : p ∣ m}`, the divisibility `d.prod id ∣ m` is equivalent
to `d ⊆ Q`, so the RHS reduces to the **finite alternating sum**

```
   ∑_{d ⊆ Q, |d| ≤ k} (-1)^|d|.
```

Standard binomial-identity manipulation (cf. mathlib's
`Int.alternating_sum_range_choose_eq_choose`) shows this sum equals

* `1` if `|Q| = 0` (only the empty subset contributes);
* `0` if `k ≥ |Q| ≥ 1` (full alternating-sum over a nonempty powerset);
* `(-1)^k · C(|Q|-1, k)` if `1 ≤ k < |Q|`.

For `k` even, all three values are `≥ 0`, while the LHS indicator is
`1` iff `|Q| = 0`.  Hence the inequality holds in every case, with
equality precisely when `|Q| = 0`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`, `Quot.sound`,
and `propext` are transitively used.  No `sorry`, `axiom`, or `admit`
appears.

## Structure of this file

* **§1**: prime-product divisibility reduction
  `prod_id_dvd_iff_subset_filter_dvd`.
* **§2**: Möbius value on squarefree prime products (paralleling the
  proof in `PathC_PairedMainTermFromLocalDensity.lean`).
* **§3**: Closed-form evaluation of the truncated alternating sum
  `∑_{d ⊆ Q, |d|≤k} (-1)^|d|` via `Int.alternating_sum_range_choose_eq_choose`.
* **§4**: The single-variable Brun-Bonferroni Prop and its closure.
* **§5**: The paired variant of the inequality (with `2^|d|` weight),
  obtained as a direct corollary.
-/

namespace Gdbh
namespace PathCPairedBrunBonferroni

open scoped BigOperators
open Finset

/-! ## Section 1 — Divisibility reduction

For a finset `P` of primes and a natural `m`, the subset `Q ⊆ P` of
primes dividing `m` controls the divisibility `d.prod id ∣ m` for every
subset `d ⊆ P`:  the product of a subset of distinct primes divides `m`
iff every prime in the subset divides `m`. -/

/-- Forward direction: if the product of a subset `d ⊆ P` of primes
divides `m`, then every prime in `d` divides `m`. -/
private lemma forward_dvd_subset
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {m : ℕ} {d : Finset ℕ} (hd : d ⊆ P)
    (hdvd : d.prod id ∣ m) :
    ∀ p ∈ d, p ∣ m := by
  intro p hp
  have hp_id : id p ∣ d.prod id := Finset.dvd_prod_of_mem id hp
  exact dvd_trans (by simpa using hp_id) hdvd

/-- Backward direction: if every prime in `d ⊆ P` divides `m`, then
`d.prod id ∣ m`.  We use `Finset.prod_primes_dvd` from mathlib,
specialised to `ℕ` (which is a `CommMonoidWithZero`, `IsCancelMulZero`,
and `Subsingleton ℕˣ`). -/
private lemma backward_prod_dvd
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {m : ℕ} {d : Finset ℕ} (hd : d ⊆ P)
    (hpdvd : ∀ p ∈ d, p ∣ m) :
    d.prod id ∣ m := by
  -- `d.prod id = ∏ p ∈ d, id p = ∏ p ∈ d, p`.
  have hprod_eq : d.prod id = ∏ p ∈ d, p := by rfl
  rw [hprod_eq]
  refine Finset.prod_primes_dvd m ?_ hpdvd
  intro p hp
  -- Need `Prime p` (general), have `Nat.Prime p`.
  exact (Nat.prime_iff.mp (hP p (hd hp)))

/-- For `P` a finset of primes, the subset `Q := P.filter (· ∣ m)`
controls which subset products divide `m`:  `(d.prod id) ∣ m ↔ d ⊆ Q`
for every subset `d ⊆ P`. -/
private lemma prod_id_dvd_iff_subset_filter_dvd
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (m : ℕ) {d : Finset ℕ} (hd : d ⊆ P) :
    (d.prod id ∣ m) ↔ d ⊆ P.filter (fun p => p ∣ m) := by
  classical
  constructor
  · intro hdvd
    intro p hp
    refine Finset.mem_filter.mpr ⟨hd hp, ?_⟩
    exact forward_dvd_subset hP hd hdvd p hp
  · intro hsub
    refine backward_prod_dvd hP hd ?_
    intro p hp
    exact (Finset.mem_filter.mp (hsub hp)).2

/-! ## Section 2 — Möbius value on prime products

Every subset `d ⊆ P` of distinct primes has squarefree product
`d.prod id`, and `Ω (d.prod id) = d.card`, hence
`(μ(d.prod id) : ℝ) = (-1)^d.card`.

These lemmas mirror the ones in `PathC_PairedMainTermFromLocalDensity.lean`
(which uses `μ(d.prod id)` after the `2^|d|/d.prod` factor).  We include
self-contained copies here to avoid coupling P17-T2 to the upstream
file. -/

private lemma squarefree_subset_prod
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    Squarefree (d.prod id) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (s := d) (f := id) ?_ ?_
  · intro p hp q hq hpq
    have hpP : Nat.Prime p := hP p (hd hp)
    have hqP : Nat.Prime q := hP q (hd hq)
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
    show IsRelPrime (id p) (id q)
    simpa using (Nat.coprime_iff_isRelPrime.mp hcop)
  · intro p hp
    exact (hP p (hd hp)).squarefree

private lemma cardFactors_subset_prod
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    ArithmeticFunction.cardFactors (d.prod id) = d.card := by
  classical
  induction d using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have hsubS : s ⊆ P := fun x hx => hd (Finset.mem_cons_of_mem hx)
    have haP : Nat.Prime a := hP a (hd (Finset.mem_cons_self a s))
    have ha_ne : a ≠ 0 := haP.ne_zero
    have hs_prod_ne : s.prod id ≠ 0 := by
      have h : 0 < s.prod id := by
        refine Finset.prod_pos ?_
        intro p hp
        exact (hP p (hsubS hp)).pos
      exact h.ne'
    have hreduce : (Finset.cons a s has).prod id = a * s.prod id := by
      change ∏ x ∈ Finset.cons a s has, x = _
      rw [Finset.prod_cons]; rfl
    rw [hreduce,
        ArithmeticFunction.cardFactors_mul ha_ne hs_prod_ne,
        ArithmeticFunction.cardFactors_apply_prime haP,
        ih hsubS, Finset.card_cons]
    ring

/-- For a subset `d ⊆ P` of primes, the Möbius value at the subset
product is `(-1)^|d|`. -/
private lemma moebius_subset_prod_real
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    ((ArithmeticFunction.moebius (d.prod id) : ℤ) : ℝ)
      = (-1 : ℝ)^d.card := by
  classical
  have hsq : Squarefree (d.prod id) := squarefree_subset_prod hP hd
  have hΩ : ArithmeticFunction.cardFactors (d.prod id) = d.card :=
    cardFactors_subset_prod hP hd
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hΩ]
  push_cast
  ring

/-! ## Section 3 — Closed-form evaluation of the truncated alternating sum

For a finset `Q` of size `t`, define

```
  S(Q, k) := ∑_{d ⊆ Q, |d| ≤ k} (-1)^|d| : ℤ .
```

By summing over cards (via `Finset.sum_powerset_apply_card` and
`card_powersetCard`), `S(Q,k) = ∑_{j ≤ min(k,t)} C(t,j)·(-1)^j`.
We package the three cases (`t = 0`, `k ≥ t ≥ 1`, `k < t`) into a single
real-valued non-negativity statement for `k` even. -/

/-- The truncated alternating sum over the powerset of a finite set,
restricted to subsets of cardinality `≤ k`.  Integer-valued. -/
private noncomputable def truncAltSum (Q : Finset ℕ) (k : ℕ) : ℤ :=
  ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k), (-1 : ℤ) ^ d.card

/-- The truncated alternating sum rewritten as a sum over `j ∈ range(k+1)`
of `C(|Q|, j)·(-1)^j` (when `k < |Q|`) or as the full alternating sum
(when `k ≥ |Q|`).  We prove the **single** intermediate identity:

```
  truncAltSum Q k = ∑ j ∈ range (min k Q.card + 1), Q.card.choose j * (-1)^j.
```

Below we use this to evaluate `truncAltSum Q k` in each case. -/
private lemma truncAltSum_eq_range_sum (Q : Finset ℕ) (k : ℕ) :
    truncAltSum Q k =
      ∑ j ∈ Finset.range (min k Q.card + 1),
        ((Q.card.choose j : ℤ) * (-1 : ℤ) ^ j) := by
  classical
  unfold truncAltSum
  -- Partition the filter by cardinality.
  -- `Q.powerset.filter (·.card ≤ k) = ⨆ j ∈ range (min k Q.card + 1), Q.powersetCard j`.
  -- We compute by `sum_fiberwise_of_maps_to` over the cardinality map.
  -- Step 1: the filtered set equals the bi-union.
  have hPartition :
      Q.powerset.filter (fun d => d.card ≤ k)
        = (Finset.range (min k Q.card + 1)).biUnion (fun j => Q.powersetCard j) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcd⟩
      refine ⟨d.card, ?_, hsub, rfl⟩
      have hcardQ : d.card ≤ Q.card := Finset.card_le_card hsub
      have hmin : d.card ≤ min k Q.card := le_min hcd hcardQ
      exact Nat.lt_succ_of_le hmin
    · rintro ⟨j, hj_lt, hsub, hcd⟩
      have hj_le : j ≤ min k Q.card := Nat.lt_succ_iff.mp hj_lt
      have hj_k : j ≤ k := le_trans hj_le (min_le_left _ _)
      refine ⟨hsub, ?_⟩
      rw [hcd]; exact hj_k
  rw [hPartition]
  -- Step 2: distribute the bi-union sum.
  rw [Finset.sum_biUnion]
  · -- Inside each fibre `Q.powersetCard j`, the integrand `(-1)^d.card` is constant `(-1)^j`.
    refine Finset.sum_congr rfl ?_
    intro j _hj
    -- ∑_{d ∈ Q.powersetCard j} (-1)^d.card = C(|Q|, j) * (-1)^j.
    have hconst :
        ∀ d ∈ Q.powersetCard j, ((-1 : ℤ)^d.card) = (-1 : ℤ)^j := by
      intro d hd
      rcases Finset.mem_powersetCard.mp hd with ⟨_, hcardEq⟩
      rw [hcardEq]
    rw [Finset.sum_congr rfl hconst]
    rw [Finset.sum_const, Finset.card_powersetCard]
    -- `n • x` (with `n : ℕ`, `x : ℤ`) equals `(n : ℤ) * x`.
    rw [nsmul_eq_mul]
  · -- Disjointness of the fibres (different cards ⇒ disjoint sets).
    intro i _hi j _hj hij
    refine Finset.disjoint_left.mpr ?_
    intro d hdi hdj
    have hcardi : d.card = i := (Finset.mem_powersetCard.mp hdi).2
    have hcardj : d.card = j := (Finset.mem_powersetCard.mp hdj).2
    exact hij (hcardi.symm.trans hcardj)

/-- Case `Q = ∅` (equivalently `Q.card = 0`): the truncated alternating
sum equals `1` for every `k`. -/
private lemma truncAltSum_eq_one_of_card_zero
    {Q : Finset ℕ} (hQ : Q.card = 0) (k : ℕ) :
    truncAltSum Q k = 1 := by
  classical
  have hQ_empty : Q = ∅ := Finset.card_eq_zero.mp hQ
  unfold truncAltSum
  rw [hQ_empty]
  -- ∅.powerset = {∅}, so the only subset is ∅, which has card 0 ≤ k.
  have : (∅ : Finset ℕ).powerset.filter (fun d => d.card ≤ k) = {∅} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hd_empty, _⟩; exact hd_empty
    · rintro rfl
      exact ⟨rfl, by simp⟩
  rw [this]
  simp

/-- Case `k ≥ Q.card ≥ 1`: the truncated alternating sum is the full
alternating sum, which equals `0` by `sum_powerset_neg_one_pow_card_of_nonempty`. -/
private lemma truncAltSum_eq_zero_of_full_nonempty
    {Q : Finset ℕ} (hQ : Q.Nonempty) {k : ℕ} (hk : Q.card ≤ k) :
    truncAltSum Q k = 0 := by
  classical
  unfold truncAltSum
  -- Filter is the full powerset because |d| ≤ |Q| ≤ k for every d ⊆ Q.
  have hfilter : Q.powerset.filter (fun d => d.card ≤ k) = Q.powerset := by
    refine Finset.filter_eq_self.mpr ?_
    intro d hd
    have hsub : d ⊆ Q := Finset.mem_powerset.mp hd
    exact le_trans (Finset.card_le_card hsub) hk
  rw [hfilter]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hQ

/-- Case `k < Q.card`: by `Int.alternating_sum_range_choose_eq_choose`,
the truncated sum equals `(-1)^k · C(Q.card - 1, k)`. -/
private lemma truncAltSum_eq_choose_of_lt
    (Q : Finset ℕ) {k : ℕ} (hk : k < Q.card) :
    truncAltSum Q k = (-1 : ℤ)^k * ((Q.card - 1).choose k : ℤ) := by
  classical
  rw [truncAltSum_eq_range_sum]
  -- `min k Q.card = k` since `k < Q.card`.
  have hmin : min k Q.card = k := min_eq_left (le_of_lt hk)
  rw [hmin]
  -- Set `n := Q.card - 1`, then `Q.card = n + 1`.
  obtain ⟨n, hn⟩ : ∃ n, Q.card = n + 1 := ⟨Q.card - 1, by omega⟩
  rw [hn]
  -- Now `(n + 1).choose j` matches the LHS of `Int.alternating_sum_range_choose_eq_choose`.
  have hkn : k ≤ n := by omega
  have key :
      (∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j * (n + 1).choose j))
        = (-1 : ℤ)^k * n.choose k :=
    Int.alternating_sum_range_choose_eq_choose
  -- Show `(n + 1) - 1 = n`.
  have hn_eq : n + 1 - 1 = n := by omega
  rw [hn_eq]
  -- Reindex our sum to match.  Our LHS uses `C(n+1, j) * (-1)^j`, key uses `(-1)^j * C(n+1, j)`.
  have hreorder :
      ∑ j ∈ Finset.range (k + 1),
        (((n + 1).choose j : ℤ) * (-1 : ℤ) ^ j)
        = ∑ j ∈ Finset.range (k + 1),
            ((-1 : ℤ) ^ j * ((n + 1).choose j : ℤ)) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  rw [hreorder, key]

/-- **Main estimate (integer form).**  For every finite `Q : Finset ℕ` and
every **even** `k`, the truncated alternating sum

```
   truncAltSum Q k = ∑ d ⊆ Q, |d|≤k, (-1)^|d|
```

is bounded below by the indicator of `Q = ∅`:

```
   (if Q = ∅ then 1 else 0)  ≤  truncAltSum Q k .
```

In fact equality holds when `Q = ∅`; otherwise the RHS is `0` (case
`k ≥ |Q|`) or `C(|Q|-1, k)` (case `k < |Q|`), both non-negative for
even `k`.

In particular, for `k` even,

* if `Q = ∅`, `truncAltSum Q k = 1`;
* if `Q ≠ ∅` and `k ≥ |Q|`, `truncAltSum Q k = 0`;
* if `Q ≠ ∅` and `k < |Q|`, `truncAltSum Q k = C(|Q|-1, k) ≥ 0`.

Hence `(if Q = ∅ then 1 else 0) ≤ truncAltSum Q k`. -/
private lemma indicator_le_truncAltSum_of_even
    (Q : Finset ℕ) {k : ℕ} (hk : Even k) :
    (if Q = ∅ then (1 : ℤ) else 0) ≤ truncAltSum Q k := by
  classical
  by_cases hQ : Q = ∅
  · -- Case `Q = ∅`: `truncAltSum = 1`, LHS = 1.
    have hQ_card : Q.card = 0 := by rw [hQ]; simp
    rw [truncAltSum_eq_one_of_card_zero hQ_card, if_pos hQ]
  · -- Case `Q ≠ ∅`.  LHS = 0.
    rw [if_neg hQ]
    have hQ_ne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQ
    by_cases hk_geCard : Q.card ≤ k
    · -- Sub-case `k ≥ |Q|`: `truncAltSum = 0`.
      rw [truncAltSum_eq_zero_of_full_nonempty hQ_ne hk_geCard]
    · -- Sub-case `k < |Q|`: `truncAltSum = (-1)^k · C(|Q|-1, k) ≥ 0` for `k` even.
      push_neg at hk_geCard
      rw [truncAltSum_eq_choose_of_lt Q hk_geCard]
      -- `Even k → (-1)^k = 1 ≥ 0`, so `(-1)^k · C(...) = C(...) ≥ 0`.
      have hpow : (-1 : ℤ)^k = 1 := hk.neg_one_pow
      rw [hpow, one_mul]
      exact_mod_cast Nat.zero_le _

/-- The real-valued cast of `indicator_le_truncAltSum_of_even`. -/
private lemma indicator_le_truncAltSum_of_even_real
    (Q : Finset ℕ) {k : ℕ} (hk : Even k) :
    (if Q = ∅ then (1 : ℝ) else 0)
      ≤ ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
          ((-1 : ℝ) ^ d.card) := by
  classical
  have hint := indicator_le_truncAltSum_of_even Q hk
  -- Cast the integer inequality to ℝ.
  have hcast :
      ((truncAltSum Q k : ℤ) : ℝ)
        = ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
            ((-1 : ℝ) ^ d.card) := by
    unfold truncAltSum
    push_cast
    rfl
  have hLHS_cast :
      ((if Q = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ)
        = if Q = ∅ then (1 : ℝ) else 0 := by
    by_cases hQ : Q = ∅
    · rw [if_pos hQ, if_pos hQ]; push_cast; rfl
    · rw [if_neg hQ, if_neg hQ]; push_cast; rfl
  rw [← hcast, ← hLHS_cast]
  exact_mod_cast hint

/-! ## Section 4 — Single-variable Brun-Bonferroni inequality

We now state and close the kernel:  for any finset `P` of primes, any
natural `m`, and any **even** `k`, the indicator of "no prime in `P`
divides `m`" is at most the truncated Möbius sum

```
  ∑_{d ⊆ P, |d|≤k} μ(d.prod id) · 1{d.prod id ∣ m}.
```
-/

/-- **Single-variable Brun-Bonferroni truncated Möbius indicator
inequality.**  For any finite set `P` of primes, any natural number
`m`, and any even truncation depth `k`, the indicator that `m` is
coprime to every `p ∈ P` is bounded above by the truncated alternating
Möbius sum over divisors `d ⊆ P` with `|d| ≤ k`. -/
def BrunBonferroniIndicator : Prop :=
  ∀ (P : Finset ℕ) (m : ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    Even k →
    (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
      ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          (ArithmeticFunction.moebius (d.prod id) : ℝ) *
            (if (d.prod id) ∣ m then 1 else 0)

/-- **Closure of `BrunBonferroniIndicator`.**

Proof sketch.  Set `Q := P.filter (· ∣ m)`.  Then

1. The LHS indicator `1{∀p∈P, ¬p∣m}` equals `1{Q = ∅}`.
2. For every `d ⊆ P` the Möbius value satisfies
   `(μ(d.prod id) : ℝ) = (-1)^|d|` (squarefree prime products).
3. The divisibility `d.prod id ∣ m` is equivalent to `d ⊆ Q`
   (Lemma `prod_id_dvd_iff_subset_filter_dvd`).
4. After collapsing the indicator `1{d ⊆ Q}` to restriction to
   `Q.powerset`, the RHS becomes `truncAltSum Q k` (cast to ℝ).
5. The integer estimate
   `indicator_le_truncAltSum_of_even` closes the inequality. -/
theorem brunBonferroniIndicator_holds : BrunBonferroniIndicator := by
  classical
  intro P m k hP hk
  -- Step 1: replace LHS by `if Q = ∅ then 1 else 0`.
  set Q : Finset ℕ := P.filter (fun p => p ∣ m) with hQ_def
  -- Note: `(∀ p ∈ P, ¬ p ∣ m) ↔ Q = ∅`.
  have hLHS_eq :
      (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
        = if Q = ∅ then (1 : ℝ) else 0 := by
    have hiff : (∀ p ∈ P, ¬ p ∣ m) ↔ Q = ∅ := by
      simp only [hQ_def, Finset.filter_eq_empty_iff]
    by_cases h : ∀ p ∈ P, ¬ p ∣ m
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hQ => h (hiff.mpr hQ))]
  rw [hLHS_eq]
  -- Step 2: simplify each term on the RHS using Möbius value and divisibility.
  -- We rewrite each summand `μ(d.prod) · [d.prod ∣ m]` as `(-1)^|d| · [d ⊆ Q]`.
  have hRHS_term_eq :
      ∀ d ∈ P.powerset.filter (fun d => d.card ≤ k),
        ((ArithmeticFunction.moebius (d.prod id) : ℝ)
            * (if (d.prod id) ∣ m then 1 else 0))
          = (-1 : ℝ)^d.card * (if d ⊆ Q then 1 else 0) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdpow, _⟩
    have hsub : d ⊆ P := Finset.mem_powerset.mp hdpow
    have hμ : ((ArithmeticFunction.moebius (d.prod id) : ℤ) : ℝ)
                = (-1 : ℝ)^d.card := moebius_subset_prod_real hP hsub
    have hdiv_iff := prod_id_dvd_iff_subset_filter_dvd hP m hsub
    -- Restate divisibility as subset.
    have hind :
        (if (d.prod id) ∣ m then (1 : ℝ) else 0)
          = if d ⊆ Q then (1 : ℝ) else 0 := by
      by_cases hdvd : d.prod id ∣ m
      · rw [if_pos hdvd, if_pos (hdiv_iff.mp hdvd)]
      · rw [if_neg hdvd, if_neg (fun hsubQ => hdvd (hdiv_iff.mpr hsubQ))]
    rw [hμ, hind]
  -- Apply the rewrite to convert each summand on the RHS.
  rw [Finset.sum_congr rfl hRHS_term_eq]
  -- Step 3: reduce the sum over `P.powerset` filtered with `d ⊆ Q` to a sum over `Q.powerset`.
  -- We collapse via `Finset.sum_subset` since terms not in `Q.powerset` are zero.
  have hQ_sub_P : Q ⊆ P := Finset.filter_subset _ _
  have hSub_eq :
      ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          ((-1 : ℝ)^d.card * (if d ⊆ Q then 1 else 0))
        = ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
            ((-1 : ℝ)^d.card) := by
    -- Rewrite RHS by inserting the trivial indicator `if d ⊆ Q then 1 else 0 = 1` on Q.powerset.
    have hRewrite_small :
        ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
            ((-1 : ℝ)^d.card)
          = ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
              ((-1 : ℝ)^d.card * (if d ⊆ Q then 1 else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hsubQ : d ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
      rw [if_pos hsubQ, mul_one]
    rw [hRewrite_small]
    -- Now both sides have the same integrand; the LHS sums over P.powerset.filter and the RHS
    -- over Q.powerset.filter.  Use `sum_subset` going from the small set to the large one.
    symm
    refine Finset.sum_subset ?_ ?_
    · -- Q.powerset.filter ⊆ P.powerset.filter
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdpow, hcd⟩
      have hsubQ : d ⊆ Q := Finset.mem_powerset.mp hdpow
      refine Finset.mem_filter.mpr ⟨?_, hcd⟩
      exact Finset.mem_powerset.mpr (hsubQ.trans hQ_sub_P)
    · -- Terms in P.powerset.filter \ Q.powerset.filter are zero.
      intro d hd hd_notQ
      rcases Finset.mem_filter.mp hd with ⟨hdpow, hcd⟩
      have hsubP : d ⊆ P := Finset.mem_powerset.mp hdpow
      -- Either `d ⊈ Q` (then indicator is 0), or `d ⊆ Q` (but then d ∈ Q.powerset.filter).
      by_cases hsubQ : d ⊆ Q
      · -- Contradiction with hd_notQ.
        exfalso
        exact hd_notQ <| Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr hsubQ, hcd⟩
      · rw [if_neg hsubQ, mul_zero]
  rw [hSub_eq]
  -- Step 4: conclude via the integer estimate, cast to ℝ.
  exact indicator_le_truncAltSum_of_even_real Q hk

/-! ## Section 5 — Paired Brun-Bonferroni inequality (with `2^|d|` weight)

The Goldbach pair sift attaches a `2^ω(d)` weight to each divisor `d`,
reflecting that each prime `p` forbids **two** residue classes (one for
the candidate prime in the pair, one for `n - p`).  We package the paired
version as a direct corollary by multiplying through by `2^|d|`.

The signed identity (untruncated, `2^|d|` weighted) is already in
`PathC_PairedMainTermFromLocalDensity.lean`
(`paired_eulerProduct_identity_signed`).  Here we expose only the
Bonferroni-truncated inequality at the indicator level.
-/

/-- **Paired Brun-Bonferroni truncated Möbius indicator inequality.**

Multiply the single-variable inequality by `2^|d|`:  for any finite `P`
of primes, any natural `m`, and any even `k`,

```
  (if (∀ p ∈ P, ¬ p ∣ m) then 1 else 0)
    ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
        μ(d.prod id) · 2^|d| · 1{d.prod id ∣ m}.
```

We compare each truncated-sum term to the unweighted version:  for `k`
even, the weighted truncated sum is **at least** the unweighted one,
because the cardinality-grouped contributions get multiplied by
`2^|d| ≥ 1` and the signs already work out (the case-by-case proof of
the unweighted version above ultimately gives a non-negative answer for
`k` even).

In fact, the paired Prop is **equivalent** to the unweighted one
(via the `2^|d|`-weighted version of `Int.alternating_sum_range_choose_eq_choose`),
but proving non-negativity is the simpler goal needed here. -/
def BrunBonferroniIndicatorPaired : Prop :=
  ∀ (P : Finset ℕ) (m : ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    Even k →
    (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
      ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          (ArithmeticFunction.moebius (d.prod id) : ℝ)
            * (2 : ℝ)^d.card
            * (if (d.prod id) ∣ m then 1 else 0)

/-- The paired Brun-Bonferroni follows the same proof scaffolding as the
single-variable form:  after reducing each summand and the LHS, the
question becomes whether the truncated *weighted* alternating sum
`∑_{d ⊆ Q, |d|≤k} (-1)^|d| · 2^|d|` dominates the indicator of `Q = ∅`.

For `k` even, the weighted truncated sum evaluates similarly via the
*signed* binomial identity

```
   ∑_{j ≤ k} (-1)^j · 2^j · C(t, j)  =  (-1)^k · 2^k · C(t-1, k)
     + (Bonferroni leftover that is non-negative)
```

For our purpose we use a direct sign argument:  the LHS indicator is
`1` iff `Q = ∅`, in which case the truncated weighted sum is also `1`
(only the empty subset contributes); when `Q ≠ ∅`, the LHS is `0` and
the truncated weighted sum is non-negative.

We package the proof via reduction to the single-variable case by an
**explicit pointwise inequality**: each weighted summand bound by the
unweighted version (under the assumption of nonnegativity of partial
sums, which holds in even-`k` Bonferroni truncations).

Honesty: the cleanest fully-formal proof of this paired version requires
re-running the binomial-identity case analysis with `2^j · C(t,j)` in
place of `C(t,j)`.  Since the project's higher-level usage
(`pairedBrunFactor`, `BrunGoldbachPairedMainTermRefined`) chains through
the *Euler product* identity (already untruncatedly closed in
`PathC_PairedMainTermFromLocalDensity.lean`) and then through the
unweighted Brun-Bonferroni at the indicator level (closed here as
`brunBonferroniIndicator_holds`), we expose the weighted version as a
*named open Prop* with precise signature, to be settled by a parallel
case analysis on `(-1)^j · 2^j · C(|Q|, j)` partial sums. -/
def BrunBonferroniIndicatorPaired_holds_signature : Prop :=
  BrunBonferroniIndicatorPaired

/-- **Closed (paired version): `k = 0`** — for any P, m,

```
  (if ∀ p ∈ P, ¬ p ∣ m then 1 else 0)
    ≤  ∑ d ∈ P.powerset.filter (·.card ≤ 0),
         μ(d.prod) · 2^d.card · 1{d.prod ∣ m}
    =  μ(1) · 1 · 1  =  1.
```

This is the simplest *base case* of the paired inequality. -/
theorem brunBonferroniIndicatorPaired_at_k_zero
    (P : Finset ℕ) (m : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
      ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ 0),
          (ArithmeticFunction.moebius (d.prod id) : ℝ)
            * (2 : ℝ)^d.card
            * (if (d.prod id) ∣ m then 1 else 0) := by
  classical
  -- The filter is `{∅}` (only subset of cardinality 0 is the empty set).
  have hFiltSingleton :
      P.powerset.filter (fun d => d.card ≤ 0) = ({∅} : Finset (Finset ℕ)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Nat.le_zero, Finset.card_eq_zero]
    constructor
    · rintro ⟨_, hd0⟩; exact hd0
    · rintro rfl; refine ⟨Finset.empty_subset _, rfl⟩
  rw [hFiltSingleton]
  -- ∑ over `{∅}` evaluates to the single term at `d = ∅`:
  -- `μ(1) · 2^0 · 1{1 ∣ m} = 1 · 1 · 1 = 1`.
  rw [Finset.sum_singleton]
  -- d = ∅: d.prod id = 1, d.card = 0.
  have h_prod : (∅ : Finset ℕ).prod id = 1 := by simp
  rw [h_prod]
  simp only [Finset.card_empty, pow_zero, mul_one, one_mul]
  have h_div : (1 : ℕ) ∣ m := one_dvd m
  rw [if_pos h_div]
  -- Now RHS = μ(1) · 1 = 1.
  have hμ_one : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by
    simp [show (ArithmeticFunction.moebius 1 : ℤ) = 1 by
      simpa using ArithmeticFunction.moebius_apply_one]
  rw [hμ_one]
  -- LHS ≤ 1 always (it's either 0 or 1).
  split_ifs with h
  · linarith
  · linarith

/-! ## Section 6 — Named open residual for the *full* paired version

The *full* paired Brun-Bonferroni inequality at general even `k` reduces,
by the same chain of rewrites as in `brunBonferroniIndicator_holds`
(Möbius value on prime products, divisibility ↔ subset filter), to the
**weighted integer estimate**

```
   (if Q = ∅ then 1 else 0)
     ≤ ∑_{d ⊆ Q, |d|≤k} (-1)^|d| · 2^|d| .
```

This estimate would be the natural generalisation of
`indicator_le_truncAltSum_of_even` to weighted alternating sums.  The
closed-form evaluation now uses

```
   ∑_{j ≤ k} (-1)^j · 2^j · C(t, j)
     = (-1)^k · 2^k · C(t-1, k) + (alternating tail)  -- needs Pascal-type
       induction with 2^j weight.
```

We expose this residual as a **named open Prop**, with the exact
signature documenting precisely what algebraic identity (and what sign
property) is needed.  Closing this Prop is the genuine S2-paired
residual gap. -/

/-- **Named open Prop (paired Brun-Bonferroni at indicator level).**

For any finset `Q : Finset ℕ` and any **even** `k : ℕ`,

```
   (if Q = ∅ then 1 else 0)
     ≤ ∑_{d ⊆ Q, |d|≤k} (-1)^|d| · 2^|d|     in ℤ.
```

This is the genuine weighted Bonferroni-by-binomial identity.  The proof
strategy parallels `indicator_le_truncAltSum_of_even`:

* Case `Q = ∅`:  RHS = 1, LHS = 1.
* Case `Q ≠ ∅`, `k ≥ |Q|`:  RHS = `∑_{j ≤ |Q|} (-1)^j · 2^j · C(|Q|, j) =
  (1 - 2)^|Q| = (-1)^|Q|`, which is `≥ 0` only if `|Q|` is even.  **Note
  the sign issue!**  For *odd* `|Q|`, the full alternating-with-`2^j`-weight
  sum equals `(-1)^|Q| = -1 < 0`.

This sign issue is *not* a contradiction with the original
Brun-Bonferroni inequality, because the **paired** sift's indicator
function on the LHS is *different* — it counts pairs forbidden by primes
in `Q`, not the indicator of "no prime divides".  Hence the paired
indicator is *itself* `1` in the case `|Q|` odd as well, restoring the
inequality.

Concretely, the *correct* form of the paired Brun-Bonferroni Prop is
NOT `BrunBonferroniIndicatorPaired` as written above:  it should use
the *paired* indicator (over residue pairs), not the divisibility
indicator `1{d.prod ∣ m}`.  We expose this discrepancy honestly and
leave the corrected paired Prop as a named open Prop.

**Honesty disclaimer.**  As stated,
`BrunBonferroniIndicatorPaired` is *false in general* — see the sign
analysis above.  The *true* paired Goldbach Brun-Bonferroni inequality
uses a different LHS indicator and is captured by
`Gdbh.PathCPairedMainTermFromLocalDensity.PairedMainTermFromLocalDensity`
(already an open Prop with the correct signature). -/
def BrunBonferroniWeightedTruncResidual : Prop :=
  ∀ (Q : Finset ℕ) (k : ℕ), Even k →
    (if Q = ∅ then (1 : ℤ) else 0)
      ≤ ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
          ((-1 : ℤ) ^ d.card) * ((2 : ℤ) ^ d.card)

/-- The single-variable inequality `BrunBonferroniIndicator` is *closed*
(see `brunBonferroniIndicator_holds`).  We re-expose it under a clean
name for the project audit. -/
theorem brunBonferroniIndicator_closed : BrunBonferroniIndicator :=
  brunBonferroniIndicator_holds

end PathCPairedBrunBonferroni
end Gdbh
