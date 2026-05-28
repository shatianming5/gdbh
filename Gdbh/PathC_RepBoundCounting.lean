/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P10-T1 (Phase 10 / Path C closure — Schnirelmann counting argument)
-/
import Gdbh.PathC_TwinAsymptotic
import Gdbh.PathC_ChebyshevLower

/-!
# Path C — Unconditional Schnirelmann counting argument

This file is the **P10-T1 deliverable** in Phase 10 (final Path C closure).
It discharges the named open `Prop`

```
def RepBoundAndChebyshevToAsymptotic : Prop :=
  GoldbachRepresentationBound → ChebyshevPrimeLowerBound →
    PrimesSumsetAsymptoticLowerBound
```

from `Gdbh/PathC_TwinAsymptotic.lean` **unconditionally**.

## Mathematical content

The classical Schnirelmann counting argument: given a Brun-style upper
bound `r(m) ≤ C₁ · m / (log m)^2` on the Goldbach representation
function and a Chebyshev-style lower bound `c · n / log n ≤ π(n)`,
produce an eventual linear lower bound
`ε · n ≤ countingUpTo primesSumset n`.

## Strategy

Let `M := n / 2`.  Then for every ordered prime pair `(p, q)` with
`p, q ≤ M`, the sum `p + q ≤ 2M ≤ n` lies in `primesSumset` (since
every prime is in `primesAndOne`).  The number of such ordered pairs
is `π(M)^2`.  Each sum `m` is realised at most `r(m)` times.

Split sums by `m ≤ Nat.sqrt (2 * M)` versus `m > Nat.sqrt (2 * M)`:

* The number of ordered prime pairs with `p + q ≤ Nat.sqrt (2 * M)` is
  at most `Nat.sqrt (2 * M) ^ 2 ≤ 2 * M ≤ n`.

* For `m > Nat.sqrt (2 * M)` we have `m^2 > 2 * M ≥ M`, so
  `log m > (log M) / 2`, hence `(log m)^2 > (log M)^2 / 4`.  With the
  rep bound `r(m) ≤ C₁ · m / (log m)^2 ≤ C₁ · 2M / ((log M)^2 / 4) =
  8 C₁ · M / (log M)^2`, each such sum contributes at most
  `8 C₁ · M / (log M)^2`.

Combining,
```
π(M)^2 ≤ 2 M + countingUpTo primesSumset (2M) · 8 C₁ · M / (log M)^2 .
```
The Chebyshev bound gives `π(M)^2 ≥ c^2 · M^2 / (log M)^2`, and for
`M` large enough the linear term `2M` is absorbed:
`π(M)^2 - 2M ≥ c^2 · M^2 / (2 (log M)^2)`.  Solving,
`countingUpTo primesSumset (2M) ≥ c^2 · M / (16 C₁)`, hence
`countingUpTo primesSumset n ≥ ε · n` for `n ≥ N₀` with
`ε := c^2 / (64 C₁)`.

## Main result

`repBoundAndChebyshevToAsymptotic_holds :
   RepBoundAndChebyshevToAsymptotic` — the headline.

All theorems are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Gdbh
namespace PathCRepBoundCounting

open scoped BigOperators
open Gdbh
open Gdbh.PathCKGoldbach (primesSumset)
open Gdbh.PathCPrimesDensity (primesAndOne primesAndOne_of_prime)
open Gdbh (sumset sumset_iff)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound)
open Gdbh.PathCTwinAsymptotic (GoldbachRepresentationBound
  goldbachRepresentationCount RepBoundAndChebyshevToAsymptotic)

/-! ## Section 1 — Counting prime pairs as `Nat.primeCounting` squared. -/

/-- For any natural `M`, the cardinality of ordered prime pairs in
`[1, M] × [1, M]` equals `(Nat.primeCounting M) ^ 2`.

We prove this by exhibiting the prime-pair set as a product of two
copies of `(Finset.Ioc 0 M).filter Nat.Prime` and using the fact
(established in `VonMangoldtGoldbach`) that this filter has cardinality
`Nat.primeCounting M` (the proof there is for `2*n`, but the same proof
works for general `n`). -/
private lemma card_primePairs_eq_primeCounting_sq (M : ℕ) :
    (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ)
      = ((Nat.primeCounting M : ℝ)) ^ 2 := by
  classical
  -- Rewrite the filtered product as the product of two filtered sets.
  have hprod : (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)
        = (Finset.Icc 1 M).filter Nat.Prime ×ˢ
            (Finset.Icc 1 M).filter Nat.Prime := by
    ext ⟨p, q⟩
    simp [Finset.mem_filter, Finset.mem_product, and_assoc, and_left_comm]
  rw [hprod, Finset.card_product]
  -- Now show `(Finset.Icc 1 M).filter Nat.Prime).card = Nat.primeCounting M`.
  have hcard : ((Finset.Icc 1 M).filter Nat.Prime).card
      = Nat.primeCounting M := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    apply Finset.card_bij (fun p _ => p)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hmem, hprime⟩
      rcases Finset.mem_Icc.mp hmem with ⟨_, hle⟩
      refine Finset.mem_filter.mpr ⟨?_, hprime⟩
      rw [Finset.mem_range]; omega
    · intros _ _ _ _ h; exact h
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hrange, hprime⟩
      refine ⟨p, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, hprime⟩
      refine Finset.mem_Icc.mpr ⟨hprime.one_lt.le, ?_⟩
      rw [Finset.mem_range] at hrange; omega
  rw [hcard]; push_cast; ring

/-! ## Section 2 — The split: ordered prime pairs by sum size

For `M ≥ 1` we partition the ordered prime pairs in `[1, M] × [1, M]`
into two pieces:

* **Small pairs**: `p + q ≤ Nat.sqrt (2 * M)`.  These are at most
  `Nat.sqrt (2 * M) ^ 2 ≤ 2 * M` in number.

* **Large pairs**: `p + q > Nat.sqrt (2 * M)`.  Each such pair's sum
  `m` satisfies `m^2 > 2 * M`, hence (for `M ≥ 2`) `log m > (log M)/2`.
-/

/-- Small ordered prime pairs in `[1, M]^2` are at most `2 * M` in number. -/
private lemma card_smallPairs_le (M : ℕ) :
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ Nat.sqrt (2 * M))).card ≤ 2 * M := by
  classical
  set K : ℕ := Nat.sqrt (2 * M)
  -- A small pair has p ≤ K and q ≤ K (since p + q ≤ K and p, q ≥ 1).
  -- Hence it lies in `Finset.Icc 1 K ×ˢ Finset.Icc 1 K`.
  have hsub :
      (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ K) ⊆
      Finset.Icc 1 K ×ˢ Finset.Icc 1 K := by
    intro ⟨p, q⟩ hpq
    rcases Finset.mem_filter.mp hpq with ⟨hmem, hp_prime, hq_prime, hsum⟩
    rcases Finset.mem_product.mp hmem with ⟨hp_mem, hq_mem⟩
    rcases Finset.mem_Icc.mp hp_mem with ⟨hp_ge, _hp_le⟩
    rcases Finset.mem_Icc.mp hq_mem with ⟨hq_ge, _hq_le⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp_ge, ?_⟩,
                                   Finset.mem_Icc.mpr ⟨hq_ge, ?_⟩⟩
    · omega
    · omega
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_product] at hcard_le
  -- `(Finset.Icc 1 K).card = K`.
  have hIcc : (Finset.Icc 1 K).card = K := by
    rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard_le
  have hKM : K * K ≤ 2 * M := Nat.sqrt_le (2 * M)
  exact hcard_le.trans hKM

/-! ## Section 3 — `primesSumset` membership

Every ordered prime pair `(p, q)` with `p, q ≤ n` produces a sum
`p + q ≤ 2n` lying in `primesSumset`. -/

/-- Every prime pair sum belongs to `primesSumset`. -/
private lemma primesSumset_of_primePair {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    primesSumset (p + q) := by
  rw [show primesSumset = sumset primesAndOne primesAndOne from rfl, sumset_iff]
  exact ⟨p, q, primesAndOne_of_prime hp, primesAndOne_of_prime hq, rfl⟩

/-! ## Section 4 — Bound the number of prime pairs by `r(p+q)`

For each `m`, the number of ordered prime pairs `(p, q) ∈ [1, M]^2`
with `p + q = m` is at most `goldbachRepresentationCount m`. -/

/-- Pairs `(p, q) ∈ [1, M]^2` with `p + q = m` and `p, q` prime are a
subset of the pairs in `[1, m]^2` with the same property (since both
`p, q ≤ m` automatically). -/
private lemma primePair_subset_of_sum_eq {M m : ℕ} :
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 = m) ⊆
      (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 = m) := by
  intro ⟨p, q⟩ hpq
  rcases Finset.mem_filter.mp hpq with ⟨hmem, hp_prime, hq_prime, hsum⟩
  rcases Finset.mem_product.mp hmem with ⟨hp_mem, hq_mem⟩
  rcases Finset.mem_Icc.mp hp_mem with ⟨hp_ge, _⟩
  rcases Finset.mem_Icc.mp hq_mem with ⟨hq_ge, _⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
                                hp_prime, hq_prime, hsum⟩
  · refine Finset.mem_Icc.mpr ⟨hp_ge, ?_⟩; omega
  · refine Finset.mem_Icc.mpr ⟨hq_ge, ?_⟩; omega

/-- For ordered prime pairs `(p, q) ∈ [1, M]^2` with `p + q = m`, the
cardinality is at most `goldbachRepresentationCount m`. -/
private lemma card_primePair_sum_eq_le_r (M m : ℕ) :
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 = m)).card ≤
      goldbachRepresentationCount m := by
  classical
  exact Finset.card_le_card primePair_subset_of_sum_eq

/-! ## Section 5 — Large pairs as a `biUnion` over sum values

The large pairs (sum > `Nat.sqrt (2 * M)`) are partitioned by their
sum.  We organise them as a `biUnion` over `m ∈ (Nat.sqrt (2 * M), 2 * M]`
with `m ∈ primesSumset` (where the latter holds because at least one
prime pair sums to `m`).
-/

/-- Large prime pairs in `[1, M]^2` are contained in the union of
fibres `{(p, q) : p + q = m}` for `m` ranging over `(K, 2M]` with
`m ∈ primesSumset`, where `K := Nat.sqrt (2 * M)`. -/
private lemma largePairs_subset_biUnion (M : ℕ) :
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          Nat.sqrt (2 * M) < pq.1 + pq.2) ⊆
      ((Finset.Ioc (Nat.sqrt (2 * M)) (2 * M)).filter primesSumset).biUnion
        (fun m => (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
          (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
            pq.1 + pq.2 = m)) := by
  intro ⟨p, q⟩ hpq
  rcases Finset.mem_filter.mp hpq with ⟨hmem, hp_prime, hq_prime, hsum_gt⟩
  rcases Finset.mem_product.mp hmem with ⟨hp_mem, hq_mem⟩
  rcases Finset.mem_Icc.mp hp_mem with ⟨_hp_ge, hp_le⟩
  rcases Finset.mem_Icc.mp hq_mem with ⟨_hq_ge, hq_le⟩
  refine Finset.mem_biUnion.mpr ⟨p + q, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, primesSumset_of_primePair hp_prime hq_prime⟩
    refine Finset.mem_Ioc.mpr ⟨hsum_gt, ?_⟩
    omega
  · refine Finset.mem_filter.mpr ⟨hmem, hp_prime, hq_prime, rfl⟩

/-- The cardinality of the index set `(K, 2M] ∩ primesSumset` is
bounded by `countingUpTo primesSumset (2M)`. -/
private lemma card_indexSet_le_countingUpTo (M : ℕ) :
    ((Finset.Ioc (Nat.sqrt (2 * M)) (2 * M)).filter primesSumset).card ≤
      Gdbh.countingUpTo primesSumset (2 * M) := by
  classical
  -- `Finset.Ioc K (2*M)` is a subset of `Finset.range (2*M + 1)`, restricted to
  -- `k ≥ 1`.  The set `countingUpTo primesSumset (2*M)` is the cardinality of
  -- `(Finset.range (2*M + 1)).filter (fun k => 1 ≤ k ∧ primesSumset k)`.
  unfold Gdbh.countingUpTo
  refine Finset.card_le_card ?_
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmem_Ioc, hsum⟩
  rcases Finset.mem_Ioc.mp hmem_Ioc with ⟨hsqrt_lt, hle⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_, hsum⟩
  · refine Finset.mem_range.mpr ?_; omega
  · -- `K < m` and `K ≥ 0`, so `m ≥ 1`.
    by_contra h
    have hm_zero : m = 0 := by omega
    omega

/-! ## Section 6 — Master decomposition: prime pairs = small + large -/

/-- The set of ordered prime pairs in `[1, M]^2` is partitioned into
small (sum `≤ K`) and large (sum `> K`) parts, where `K = Nat.sqrt(2*M)`. -/
private lemma prime_pairs_decomp_card (M : ℕ) :
    (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ) ≤
      ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
          (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
            pq.1 + pq.2 ≤ Nat.sqrt (2 * M))).card +
      ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
          (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
            Nat.sqrt (2 * M) < pq.1 + pq.2)).card := by
  classical
  set K : ℕ := Nat.sqrt (2 * M)
  set T : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2) with hT_def
  set Ts : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
        pq.1 + pq.2 ≤ K) with hTs_def
  set Tl : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
        K < pq.1 + pq.2) with hTl_def
  -- `T ⊆ Ts ∪ Tl` and they are disjoint.
  have hsubset : T ⊆ Ts ∪ Tl := by
    intro ⟨p, q⟩ hpq
    rcases Finset.mem_filter.mp hpq with ⟨hmem, hp_prime, hq_prime⟩
    by_cases h : p + q ≤ K
    · refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hmem, hp_prime, hq_prime, h⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      refine Finset.mem_filter.mpr ⟨hmem, hp_prime, hq_prime, ?_⟩
      omega
  have hcard_le :
      T.card ≤ (Ts ∪ Tl).card := Finset.card_le_card hsubset
  have hcard_union : (Ts ∪ Tl).card ≤ Ts.card + Tl.card :=
    Finset.card_union_le _ _
  have : T.card ≤ Ts.card + Tl.card := hcard_le.trans hcard_union
  exact_mod_cast this

/-- Pulling together: the small part is `≤ 2M`, and the large part is
bounded by `countingUpTo primesSumset (2M)` times the max of
`goldbachRepresentationCount m` for `m ∈ (K, 2M]`. -/
private lemma prime_pairs_bound_by_counting_and_max
    (M : ℕ) (R : ℝ) (hR_nonneg : 0 ≤ R)
    (hR : ∀ m, Nat.sqrt (2 * M) < m → m ≤ 2 * M →
      (goldbachRepresentationCount m : ℝ) ≤ R) :
    (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ) ≤
      (2 * M : ℝ) +
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) * R := by
  classical
  set K : ℕ := Nat.sqrt (2 * M) with hK_def
  -- Step 1: small + large decomposition.
  have hsum :=
    prime_pairs_decomp_card M
  -- Step 2: bound small by `2M`.
  have hsmall : ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ K)).card ≤ 2 * M := card_smallPairs_le M
  have hsmall_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ K)).card : ℝ) ≤ (2 * M : ℝ) := by
    exact_mod_cast hsmall
  -- Step 3: bound large via biUnion.
  set I : Finset ℕ :=
    (Finset.Ioc K (2 * M)).filter primesSumset with hI_def
  set f : ℕ → Finset (ℕ × ℕ) := fun m =>
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
        pq.1 + pq.2 = m) with hf_def
  have hlarge_subset := largePairs_subset_biUnion M
  have hlarge_card_le :
      ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card ≤ (I.biUnion f).card :=
    Finset.card_le_card hlarge_subset
  -- For each `m ∈ I`, `(f m).card : ℝ ≤ R`.
  have hf_le_R : ∀ m ∈ I, ((f m).card : ℝ) ≤ R := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmem_Ioc, _hsum⟩
    rcases Finset.mem_Ioc.mp hmem_Ioc with ⟨hK_lt, hle⟩
    have h1 : (f m).card ≤ goldbachRepresentationCount m :=
      card_primePair_sum_eq_le_r M m
    have h1' : ((f m).card : ℝ) ≤ (goldbachRepresentationCount m : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans (hR m hK_lt hle)
  -- Sum bound: `Σ (f m).card ≤ I.card · R` (real-valued).
  have hbiUnion_card_le : ((I.biUnion f).card : ℝ) ≤ ∑ m ∈ I, ((f m).card : ℝ) := by
    have h_nat : (I.biUnion f).card ≤ ∑ m ∈ I, (f m).card :=
      Finset.card_biUnion_le
    have : ((I.biUnion f).card : ℝ) ≤ ((∑ m ∈ I, (f m).card : ℕ) : ℝ) := by
      exact_mod_cast h_nat
    refine this.trans ?_
    push_cast; rfl
  have hsum_le : (∑ m ∈ I, ((f m).card : ℝ)) ≤ I.card * R := by
    calc (∑ m ∈ I, ((f m).card : ℝ))
        ≤ ∑ _ ∈ I, R := Finset.sum_le_sum (fun m hm => hf_le_R m hm)
      _ = I.card * R := by
          rw [Finset.sum_const]; simp [mul_comm]
  -- And `I.card ≤ countingUpTo primesSumset (2*M)`.
  have hI_card : I.card ≤ Gdbh.countingUpTo primesSumset (2 * M) :=
    card_indexSet_le_countingUpTo M
  have hI_card_real :
      ((I.card : ℕ) : ℝ) ≤ (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) := by
    exact_mod_cast hI_card
  have hlarge_card_le_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ) ≤ ((I.biUnion f).card : ℝ) := by
    exact_mod_cast hlarge_card_le
  have hlarge_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ) ≤
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) * R := by
    calc (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ)
        ≤ ((I.biUnion f).card : ℝ) := hlarge_card_le_real
      _ ≤ ∑ m ∈ I, ((f m).card : ℝ) := hbiUnion_card_le
      _ ≤ (I.card : ℝ) * R := hsum_le
      _ ≤ (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) * R :=
          mul_le_mul_of_nonneg_right hI_card_real hR_nonneg
  -- Combine.
  linarith [hsum, hsmall_real, hlarge_real]

/-! ## Section 7 — Specialised rep-bound: `r(m) ≤ 8 C₁ M / (log M)^2`
for `m ∈ (Nat.sqrt(2M), 2M]` and `M` large enough. -/

/-- Numerical lemma: for `M ≥ 2` and `m > Nat.sqrt(2*M)`,
`Real.log m > Real.log M / 2`.

Proof: `m ≥ Nat.sqrt(2M) + 1`, hence `m^2 ≥ (Nat.sqrt(2M)+1)^2 > 2M ≥ M`.
Taking logs (with `m ≥ 1`), `2 log m > log M`. -/
private lemma log_m_gt_half_log_M
    {M m : ℕ} (hM : 2 ≤ M) (hm_gt : Nat.sqrt (2 * M) < m) :
    Real.log (M : ℝ) / 2 < Real.log (m : ℝ) := by
  have hm_pos : 0 < m := by
    have hsqrt_nonneg : 0 ≤ Nat.sqrt (2 * M) := Nat.zero_le _
    omega
  have hm_ge_one : 1 ≤ m := hm_pos
  -- `(Nat.sqrt(2M)+1)^2 > 2M`
  have hsqrt_succ : (2 * M) < (Nat.sqrt (2 * M) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (2 * M)
  -- From `m > Nat.sqrt(2M)`, get `m ≥ Nat.sqrt(2M) + 1`, hence `m^2 ≥ (Nat.sqrt(2M)+1)^2`.
  have hm_ge : Nat.sqrt (2 * M) + 1 ≤ m := hm_gt
  have hm_sq : (Nat.sqrt (2 * M) + 1) ^ 2 ≤ m ^ 2 := by
    exact Nat.pow_le_pow_left hm_ge 2
  -- So `m^2 > 2M ≥ M`.
  have hmsq_gt : 2 * M < m ^ 2 := lt_of_lt_of_le hsqrt_succ hm_sq
  have hM_lt : M < m ^ 2 := by linarith
  -- Real version: `M < m^2`.
  have hM_real_lt : (M : ℝ) < (m : ℝ) ^ 2 := by
    have := hM_lt
    exact_mod_cast this
  -- `M ≥ 2 ≥ 1`, so `(M : ℝ) ≥ 1 > 0`.
  have hM_real_pos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hM_real_ge : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  -- `m^2 > 1`, `m > 1` (since `m^2 > M ≥ 2 > 1`).
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  -- Take logs.
  have hlogM_lt : Real.log (M : ℝ) < Real.log ((m : ℝ) ^ 2) :=
    Real.log_lt_log hM_real_pos hM_real_lt
  rw [Real.log_pow] at hlogM_lt
  -- log m ^ 2 = 2 * log m (when m ≥ 1)? No, Real.log_pow gives log(x^n) = n * log x.
  -- So `log M < 2 * log m`, hence `log M / 2 < log m`.
  -- The cast `((2 : ℕ) : ℝ) = 2` is needed.
  have h2cast : ((2 : ℕ) : ℝ) = 2 := by norm_cast
  rw [h2cast] at hlogM_lt
  linarith

/-- For `M ≥ 2` and `m > Nat.sqrt(2*M)`, `(Real.log m)^2 > (Real.log M)^2 / 4`. -/
private lemma log_m_sq_gt_quarter_log_M_sq
    {M m : ℕ} (hM : 2 ≤ M) (hm_gt : Nat.sqrt (2 * M) < m) :
    (Real.log (M : ℝ))^2 / 4 < (Real.log (m : ℝ))^2 := by
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM_pos : 0 < Real.log (M : ℝ) := by
    refine Real.log_pos ?_; linarith
  have hlogm_gt : Real.log (M : ℝ) / 2 < Real.log (m : ℝ) :=
    log_m_gt_half_log_M hM hm_gt
  -- Square both positive sides.
  have hlogm_pos : 0 < Real.log (m : ℝ) := by
    have h := hlogm_gt
    have hpos : 0 < Real.log (M : ℝ) / 2 := by linarith
    linarith
  have hsq : (Real.log (M : ℝ) / 2) ^ 2 < (Real.log (m : ℝ)) ^ 2 := by
    have hL_nonneg : 0 ≤ Real.log (M : ℝ) / 2 := le_of_lt (by linarith)
    have := mul_self_lt_mul_self hL_nonneg hlogm_gt
    -- mul_self_lt_mul_self : 0 ≤ a → a < b → a * a < b * b
    have h1 : (Real.log (M : ℝ) / 2) * (Real.log (M : ℝ) / 2) =
              (Real.log (M : ℝ) / 2) ^ 2 := by ring
    have h2 : Real.log (m : ℝ) * Real.log (m : ℝ) = (Real.log (m : ℝ)) ^ 2 := by ring
    linarith [this, h1.symm.le, h2.symm.le]
  have h_eq : (Real.log (M : ℝ) / 2) ^ 2 = (Real.log (M : ℝ))^2 / 4 := by ring
  linarith

/-- For `M ≥ max(2, N_R²)` with `N_R ≥ 1` and `m ∈ (Nat.sqrt(2M), 2M]`,
the rep bound gives `r(m) ≤ 8 C₁ · M / (log M)^2`. -/
private lemma rep_count_le_of_large
    {C₁ : ℝ} (hC₁_pos : 0 < C₁) {N_R M m : ℕ}
    (hM_ge_two : 2 ≤ M) (hM_ge_NR_sq : N_R^2 ≤ 2 * M)
    (h_rep : ∀ n : ℕ, N_R ≤ n →
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * (n : ℝ) / (Real.log (n : ℝ))^2)
    (hm_gt : Nat.sqrt (2 * M) < m) (hm_le : m ≤ 2 * M) :
    (goldbachRepresentationCount m : ℝ) ≤
      8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
  -- Step 1: `N_R ≤ Nat.sqrt(2M) < m`.
  have hNR_le_sqrt : N_R ≤ Nat.sqrt (2 * M) := by
    rw [Nat.le_sqrt']; exact hM_ge_NR_sq
  have hNR_le_m : N_R ≤ m := le_of_lt (lt_of_le_of_lt hNR_le_sqrt hm_gt)
  -- Step 2: apply rep bound.
  have h_rep_m := h_rep m hNR_le_m
  -- Step 3: get log bounds.
  have hlogM_pos : 0 < Real.log (M : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
    linarith
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hlogm_sq_pos : 0 < (Real.log (m : ℝ))^2 := by
    have hlogm_gt : Real.log (M : ℝ) / 2 < Real.log (m : ℝ) :=
      log_m_gt_half_log_M hM_ge_two hm_gt
    have hpos : 0 < Real.log (M : ℝ) / 2 := by linarith
    have : 0 < Real.log (m : ℝ) := by linarith
    positivity
  have hlogm_sq_gt : (Real.log (M : ℝ))^2 / 4 < (Real.log (m : ℝ))^2 :=
    log_m_sq_gt_quarter_log_M_sq hM_ge_two hm_gt
  -- Step 4: `m ≤ 2M`.
  have hm_real_le : (m : ℝ) ≤ 2 * (M : ℝ) := by
    have : (m : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast hm_le
    have h2 : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    linarith
  -- Step 5: `r(m) ≤ C₁ * m / (log m)^2 ≤ C₁ * 2M / ((log M)^2 / 4) = 8 C₁ M / (log M)^2`.
  -- First: `C₁ * m / (log m)^2 ≤ C₁ * 2M / ((log M)^2 / 4)`.
  -- We have `C₁ > 0`, `m ≤ 2M`, `(log m)^2 ≥ (log M)^2/4 > 0`.
  have hC₁_m_nonneg : 0 ≤ C₁ * (m : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg (le_of_lt hC₁_pos) this
  have hquarter_pos : 0 < (Real.log (M : ℝ))^2 / 4 := by linarith
  -- `C₁ * m / (log m)^2 ≤ C₁ * (2M) / (log m)^2`.
  have step1 : C₁ * (m : ℝ) / (Real.log (m : ℝ))^2 ≤
               C₁ * (2 * (M : ℝ)) / (Real.log (m : ℝ))^2 := by
    have hmul_le : C₁ * (m : ℝ) ≤ C₁ * (2 * (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hm_real_le (le_of_lt hC₁_pos)
    exact div_le_div_of_nonneg_right hmul_le (le_of_lt hlogm_sq_pos)
  -- `C₁ * 2M / (log m)^2 ≤ C₁ * 2M / ((log M)^2 / 4)`.
  have step2 : C₁ * (2 * (M : ℝ)) / (Real.log (m : ℝ))^2 ≤
               C₁ * (2 * (M : ℝ)) / ((Real.log (M : ℝ))^2 / 4) := by
    have hC₁2M_nonneg : 0 ≤ C₁ * (2 * (M : ℝ)) := by
      have : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le _
      have : (0 : ℝ) ≤ 2 * (M : ℝ) := by linarith
      exact mul_nonneg (le_of_lt hC₁_pos) this
    apply div_le_div_of_nonneg_left hC₁2M_nonneg hquarter_pos
    linarith [hlogm_sq_gt]
  -- Combine and simplify.
  have hquarter_ne : ((Real.log (M : ℝ))^2 / 4) ≠ 0 := ne_of_gt hquarter_pos
  have hlogM_sq_ne : (Real.log (M : ℝ))^2 ≠ 0 := ne_of_gt hlogM_sq_pos
  have h_eq : C₁ * (2 * (M : ℝ)) / ((Real.log (M : ℝ))^2 / 4) =
              8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
    field_simp
    ring
  linarith [h_rep_m, step1, step2, h_eq.le, h_eq.symm.le]

/-! ## Section 8 — The core quantitative bound at even argument -/

/-- **Core quantitative bound (even argument).**

For `M` large enough — specifically, `2 ≤ M`, `N_R² ≤ 2M`, and the
Chebyshev bound applies at `M` — we have
```
c² · M² / (log M)² ≤ π(M)² ≤ 2M + countingUpTo primesSumset (2M) · 8 C₁ M / (log M)²
```
which rearranges to
```
countingUpTo primesSumset (2M) ≥ (c² · M² / (log M)² - 2M) · (log M)² / (8 C₁ M).
```
-/
private lemma counting_lower_bound_even
    {C₁ c : ℝ} (hC₁_pos : 0 < C₁) (hc_pos : 0 < c)
    {N_R M : ℕ}
    (hM_ge_two : 2 ≤ M) (hM_ge_NR_sq : N_R^2 ≤ 2 * M)
    (h_rep : ∀ n : ℕ, N_R ≤ n →
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * (n : ℝ) / (Real.log (n : ℝ))^2)
    (h_cheb : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ)) :
    c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 ≤
      (2 * M : ℝ) +
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
          (8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2) := by
  -- Step 1: log M > 0.
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by linarith
  -- Step 2: π(M)² ≥ c² M² / (log M)².
  have hπ_ge : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ) := h_cheb
  have hcM_div_pos : 0 < c * (M : ℝ) / Real.log (M : ℝ) := by
    apply div_pos
    · exact mul_pos hc_pos hM_real_pos
    · exact hlogM_pos
  have hπ_nonneg : 0 ≤ (Nat.primeCounting M : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hπ_sq_ge : (c * (M : ℝ) / Real.log (M : ℝ))^2 ≤
                  ((Nat.primeCounting M : ℝ))^2 := by
    apply sq_le_sq'
    · linarith [hcM_div_pos]
    · exact hπ_ge
  -- Simplify LHS: (c M / log M)² = c² M² / (log M)².
  have h_sq_eq : (c * (M : ℝ) / Real.log (M : ℝ))^2 =
                 c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 := by
    rw [div_pow, mul_pow]
  rw [h_sq_eq] at hπ_sq_ge
  -- Step 3: prime pair count ≤ RHS via `prime_pairs_bound_by_counting_and_max`.
  have hR_nonneg : 0 ≤ 8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
    apply div_nonneg
    · have : (0 : ℝ) ≤ 8 * C₁ := by linarith
      have : (0 : ℝ) ≤ 8 * C₁ * (M : ℝ) := mul_nonneg this hM_real_pos.le
      exact this
    · exact hlogM_sq_pos.le
  have hR_bound :
    ∀ m, Nat.sqrt (2 * M) < m → m ≤ 2 * M →
      (goldbachRepresentationCount m : ℝ) ≤
        8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
    intro m hm_gt hm_le
    exact rep_count_le_of_large hC₁_pos hM_ge_two hM_ge_NR_sq h_rep hm_gt hm_le
  have hpair_bound := prime_pairs_bound_by_counting_and_max M
    (8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2) hR_nonneg hR_bound
  -- Step 4: prime pair count = π(M)².
  have hpair_eq := card_primePairs_eq_primeCounting_sq M
  -- Combine: π(M)² ≤ RHS.
  rw [hpair_eq] at hpair_bound
  -- π(M)² ≥ c² M² / (log M)², so c² M² / (log M)² ≤ π(M)² ≤ RHS.
  linarith [hπ_sq_ge, hpair_bound]

/-! ## Section 9 — Asymptotic absorption of `2M` and final ε
extraction -/

/-- For `M` large enough — additionally `c² · M ≥ 4 (log M)²` —
the linear `2M` term is absorbed, yielding
`countingUpTo primesSumset (2M) ≥ c² · M / (16 C₁)`. -/
private lemma counting_lower_bound_even_absorbed
    {C₁ c : ℝ} (hC₁_pos : 0 < C₁) (hc_pos : 0 < c)
    {N_R M : ℕ}
    (hM_ge_two : 2 ≤ M) (hM_ge_NR_sq : N_R^2 ≤ 2 * M)
    (h_rep : ∀ n : ℕ, N_R ≤ n →
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * (n : ℝ) / (Real.log (n : ℝ))^2)
    (h_cheb : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ))
    (h_absorb : 4 * (Real.log (M : ℝ))^2 ≤ c^2 * (M : ℝ)) :
    c^2 * (M : ℝ) / (16 * C₁) ≤
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) := by
  have hbound := counting_lower_bound_even hC₁_pos hc_pos hM_ge_two
                   hM_ge_NR_sq h_rep h_cheb
  -- Setup positivity facts.
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by linarith
  have hC₁_pos' := hC₁_pos
  -- The bound says:
  --   c² M² / (log M)² ≤ 2M + count · (8 C₁ M / (log M)²)
  -- Rearrange:
  --   c² M² / (log M)² - 2M ≤ count · (8 C₁ M / (log M)²)
  -- Multiply both sides by (log M)² / (8 C₁ M):
  --   count ≥ (c² M² - 2M · (log M)²) / (8 C₁ M · (log M)² / (log M)²)
  --         = (c² M² - 2M · (log M)²) / (8 C₁ M (log M)²)
  --         · (log M)² / (log M)²
  --   count ≥ (c² M² / (log M)² - 2M) · (log M)² / (8 C₁ M)
  --         = c² M / (8 C₁) - 2M (log M)² / (8 C₁ M)
  --         = c² M / (8 C₁) - (log M)² / (4 C₁)
  -- With h_absorb: 4 (log M)² ≤ c² M, so (log M)²/(4C₁) ≤ c² M / (16 C₁).
  -- Thus c² M / (8 C₁) - (log M)² / (4 C₁) ≥ c² M / (8 C₁) - c² M / (16 C₁)
  --                                       = c² M / (16 C₁).
  -- Algebra path:
  -- From `hbound`: count · (8 C₁ M / (log M)²) ≥ c² M² / (log M)² - 2M.
  -- Multiply by (log M)² (positive): count · 8 C₁ M ≥ c² M² - 2M · (log M)².
  -- Divide by 8 C₁ M (positive): count ≥ (c² M² - 2M · (log M)²) / (8 C₁ M).
  set L := Real.log (M : ℝ) with hL_def
  set count := (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) with hcount_def
  -- hbound: c² M² / L² ≤ 2M + count · (8 C₁ M / L²)
  -- multiply both sides by L²: c² M² ≤ 2M · L² + count · 8 C₁ M
  have hbound2 : c^2 * (M : ℝ)^2 ≤ 2 * (M : ℝ) * L^2 + count * (8 * C₁ * (M : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hbound (le_of_lt hlogM_sq_pos)
    -- LHS * L² = c² M² / L² * L² = c² M²
    -- RHS * L² = (2M + count · 8 C₁ M / L²) · L² = 2M L² + count · 8 C₁ M
    have hL_sq_ne : (L^2) ≠ 0 := ne_of_gt hlogM_sq_pos
    have hLHS : c^2 * (M : ℝ)^2 / L^2 * L^2 = c^2 * (M : ℝ)^2 := by
      field_simp
    have hRHS : ((2 * M : ℝ) + count * (8 * C₁ * (M : ℝ) / L^2)) * L^2 =
                2 * (M : ℝ) * L^2 + count * (8 * C₁ * (M : ℝ)) := by
      field_simp
    rw [hLHS] at this
    rw [hRHS] at this
    exact this
  -- Now: c² M² - 2M L² ≤ count · 8 C₁ M.
  have hstep : c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2 ≤
               count * (8 * C₁ * (M : ℝ)) := by linarith
  -- Divide by (8 C₁ M).
  have h8C₁M_pos : 0 < 8 * C₁ * (M : ℝ) := by positivity
  have hdiv : (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) / (8 * C₁ * (M : ℝ)) ≤ count := by
    rw [div_le_iff₀ h8C₁M_pos]
    linarith
  -- Now use h_absorb to bound from below.
  -- c² M² - 2 M L² = M · (c² M - 2 L²) ≥ M · (c² M - (c² M / 2)) = M · c² M / 2 = c² M² / 2.
  -- (Using h_absorb: 4 L² ≤ c² M ⟹ 2 L² ≤ c² M / 2.)
  -- Then RHS ≥ (c² M²/2) / (8 C₁ M) = c² M / (16 C₁).
  have h_target : c^2 * (M : ℝ) / (16 * C₁) ≤
        (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) / (8 * C₁ * (M : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C₁) h8C₁M_pos]
    -- Goal: c² M · 8 C₁ M ≤ (c² M² - 2 M L²) · 16 C₁
    -- Simplify: 8 c² C₁ M² ≤ 16 C₁ (c² M² - 2 M L²) = 16 C₁ c² M² - 32 C₁ M L²
    -- Need: 32 C₁ M L² ≤ 8 c² C₁ M² ⟺ 4 L² ≤ c² M  (since 32 = 4·8, M, C₁ > 0)
    -- ⟺ h_absorb.
    have h_simp : c^2 * (M : ℝ) * (8 * C₁ * (M : ℝ)) ≤
                  (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) * (16 * C₁) := by
      have : (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) * (16 * C₁) =
             16 * C₁ * c^2 * (M : ℝ)^2 - 32 * C₁ * (M : ℝ) * L^2 := by ring
      rw [this]
      have h1 : c^2 * (M : ℝ) * (8 * C₁ * (M : ℝ)) =
                8 * C₁ * c^2 * (M : ℝ)^2 := by ring
      rw [h1]
      -- Now: 8 C₁ c² M² ≤ 16 C₁ c² M² - 32 C₁ M L²
      -- ⟺ 32 C₁ M L² ≤ 8 C₁ c² M²
      -- ⟺ 4 L² ≤ c² M (since C₁ M > 0).
      have hC₁M_pos : 0 < C₁ * (M : ℝ) := mul_pos hC₁_pos hM_real_pos
      have habsorb_mult : 4 * L^2 * (8 * C₁ * (M : ℝ)) ≤
                          c^2 * (M : ℝ) * (8 * C₁ * (M : ℝ)) := by
        exact mul_le_mul_of_nonneg_right h_absorb (le_of_lt h8C₁M_pos)
      nlinarith [habsorb_mult, sq_nonneg (M : ℝ), sq_nonneg L, hC₁_pos, hM_real_pos]
    exact h_simp
  linarith [hdiv, h_target]

/-! ## Section 10 — Eventual absorption: `4 (log M)² ≤ c² M` -/

open Filter Asymptotics in
/-- For any `c > 0`, eventually `4 (log M)² ≤ c² M` as a real-valued
predicate on naturals. -/
private lemma eventually_log_sq_lt_const_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop, 4 * (Real.log (M : ℝ))^2 ≤ c^2 * (M : ℝ) := by
  -- `(log x)² = o(x)` on reals, then transfer to ℕ via cast.
  have h_real : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  -- Multiply RHS by c²/4.
  have hε_pos : 0 < c^2 / 4 := by positivity
  have hε_ne : c^2 / 4 ≠ 0 := ne_of_gt hε_pos
  have h_real2 : (fun x : ℝ => Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => (c^2 / 4) * x) :=
    h_real.const_mul_right hε_ne
  -- Get the eventual bound on reals.
  have h_real_eventual : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ 2 ≤ (c^2 / 4) * x := by
    filter_upwards [h_real2.eventuallyLE, eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos
    have htarget_nonneg : 0 ≤ (c^2 / 4) * x := by positivity
    have hnorm_target : ‖(c^2 / 4) * x‖ = (c^2 / 4) * x := by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
    have hle_norm : Real.log x ^ 2 ≤ ‖Real.log x ^ 2‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    have hx' : ‖Real.log x ^ 2‖ ≤ ‖(c^2 / 4) * x‖ := hx
    rw [hnorm_target] at hx'
    exact hle_norm.trans hx'
  -- Transfer to ℕ via tendsto_natCast_atTop_atTop.
  have h_tendsto : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h_nat_eventual : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 2 ≤ (c^2 / 4) * (n : ℝ) :=
    h_tendsto.eventually h_real_eventual
  filter_upwards [h_nat_eventual] with n hn
  -- hn : Real.log ↑n ^ 2 ≤ c^2 / 4 * ↑n
  -- Want: 4 * Real.log ↑n ^ 2 ≤ c^2 * ↑n
  linarith

/-! ## Section 11 — Monotonicity of `countingUpTo` -/

/-- `countingUpTo` is monotone in `n`. -/
private lemma countingUpTo_mono (A : ℕ → Prop) [DecidablePred A] {m n : ℕ}
    (h : m ≤ n) :
    Gdbh.countingUpTo A m ≤ Gdbh.countingUpTo A n := by
  unfold Gdbh.countingUpTo
  apply Finset.card_le_card
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hk_mem, h1, hAk⟩
  rcases Finset.mem_range.mp hk_mem with hk_lt
  refine Finset.mem_filter.mpr ⟨?_, h1, hAk⟩
  refine Finset.mem_range.mpr ?_
  omega

/-! ## Section 12 — The headline theorem -/

open Filter in
/-- **Headline theorem (P10-T1).**

The Schnirelmann counting argument: from the Brun-style upper bound on
`goldbachRepresentationCount` and Chebyshev's lower bound on
`Nat.primeCounting`, the eventual linear lower bound on
`countingUpTo primesSumset` follows unconditionally. -/
theorem repBoundAndChebyshevToAsymptotic_holds :
    RepBoundAndChebyshevToAsymptotic := by
  intro hRep hCheb
  obtain ⟨C₁, N_R, hC₁_pos, h_rep⟩ := hRep
  obtain ⟨c, N_C, hc_pos, h_cheb⟩ := hCheb
  -- Choose ε := c² / (64 * C₁).
  set ε : ℝ := c^2 / (64 * C₁) with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]; positivity
  -- Combine all `eventually` conditions on M = n/2.
  -- We need:
  --   (a) 2 ≤ M  (i.e., n ≥ 4)
  --   (b) N_R² ≤ 2M  (i.e., 2M ≥ N_R²; if n ≥ N_R² + 1, then 2M = n or n-1 ≥ N_R²)
  --   (c) N_C ≤ M  (i.e., n ≥ 2 N_C, since M = n/2 ≥ N_C requires n ≥ 2N_C)
  --   (d) 4 (log M)² ≤ c² M
  --   (e) n ≥ 2 (for odd n adjustment)
  -- The condition (d) is eventually true via `eventually_log_sq_lt_const_mul`.
  -- Get the threshold N_log for (d).
  obtain ⟨N_log, hN_log⟩ :=
    Filter.eventually_atTop.mp (eventually_log_sq_lt_const_mul hc_pos)
  -- Take N₀ := max (2 * N_C + 2) (max (N_R^2 + 2) (2 * N_log + 2))
  -- But we use M = n / 2 (Nat division). For n ≥ 2N_C+1, M ≥ N_C.
  -- For n ≥ N_R² + 1, 2M ≥ n - 1 ≥ N_R².  Actually 2M = n or n-1, so 2M ≥ n-1 ≥ N_R².
  -- For n ≥ 2 N_log + 1, M ≥ N_log.
  -- For n ≥ 4, M ≥ 2.
  set N₀ : ℕ := max (2 * N_C + 2) (max (N_R^2 + 2) (max (2 * N_log + 2) 4)) with hN₀_def
  refine ⟨ε, N₀, hε_pos, ?_⟩
  intro n hn
  -- Set M = n/2.
  set M : ℕ := n / 2 with hM_def
  -- Property: n - 1 ≤ 2M ≤ n.
  have h2M_le_n : 2 * M ≤ n := by
    rw [hM_def]
    have := Nat.div_add_mod n 2
    omega
  have hn_le_2M_succ : n ≤ 2 * M + 1 := by
    rw [hM_def]
    have := Nat.div_add_mod n 2
    have hmod_lt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have h2M_ge_pred : n - 1 ≤ 2 * M := by omega
  -- Conditions on M.
  have hM_ge_two : 2 ≤ M := by
    have hn_ge_4 : 4 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  have hM_ge_NC : N_C ≤ M := by
    have hn_ge : 2 * N_C + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  have h2M_ge_NR_sq : N_R^2 ≤ 2 * M := by
    have hn_ge : N_R^2 + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    omega
  have hM_ge_Nlog : N_log ≤ M := by
    have hn_ge : 2 * N_log + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  -- Apply h_cheb at M.
  have h_cheb_M : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ) :=
    h_cheb M hM_ge_NC
  -- Get absorption: 4 (log M)² ≤ c² M.
  have h_absorb : 4 * (Real.log (M : ℝ))^2 ≤ c^2 * (M : ℝ) := hN_log M hM_ge_Nlog
  -- Apply the core bound.
  have h_counting_2M : c^2 * (M : ℝ) / (16 * C₁) ≤
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) :=
    counting_lower_bound_even_absorbed hC₁_pos hc_pos hM_ge_two
      h2M_ge_NR_sq h_rep h_cheb_M h_absorb
  -- countingUpTo primesSumset n ≥ countingUpTo primesSumset (2*M) (by monotonicity).
  have h_mono : Gdbh.countingUpTo primesSumset (2 * M) ≤
                Gdbh.countingUpTo primesSumset n :=
    countingUpTo_mono _ h2M_le_n
  have h_mono_real :
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) ≤
      (Gdbh.countingUpTo primesSumset n : ℝ) := by
    exact_mod_cast h_mono
  -- Finally: c² M / (16 C₁) ≥ c² (n-1)/2 / (16 C₁) = c² (n-1) / (32 C₁) ≥ c² n / (64 C₁) for n ≥ 2.
  -- M ≥ (n-1)/2 in reals.
  have hM_real_ge : (n - 1 : ℝ) / 2 ≤ (M : ℝ) := by
    have h2M_ge : ((n - 1 : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
      exact_mod_cast h2M_ge_pred
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have hn_ge_1 : 1 ≤ n := by
        have h := hn
        rw [hN₀_def] at h
        simp at h
        omega
      have : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        have : ((n - 1) + 1 : ℕ) = n := by omega
        exact_mod_cast this
      linarith
    rw [h1] at h2M_ge
    have h2M_cast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    rw [h2M_cast] at h2M_ge
    linarith
  -- Need n ≥ 2 so n - 1 ≥ n / 2.
  have hn_ge_two : 2 ≤ n := by
    have h := hn
    rw [hN₀_def] at h
    simp at h
    omega
  have hn_real_ge : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_two
    linarith
  -- So M ≥ n/4.
  have hM_ge_n4 : (n : ℝ) / 4 ≤ (M : ℝ) := by
    have h1 : (n : ℝ) / 4 = ((n : ℝ) / 2) / 2 := by ring
    rw [h1]
    have : ((n : ℝ) / 2) / 2 ≤ ((n : ℝ) - 1) / 2 :=
      div_le_div_of_nonneg_right hn_real_ge (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  -- Now: c² M / (16 C₁) ≥ c² (n/4) / (16 C₁) = c² n / (64 C₁) = ε * n.
  have h_final : ε * (n : ℝ) ≤ c^2 * (M : ℝ) / (16 * C₁) := by
    rw [hε_def]
    have h16C₁_pos : 0 < 16 * C₁ := by positivity
    have h64C₁_pos : 0 < 64 * C₁ := by positivity
    have hc_sq_pos : 0 < c^2 := by positivity
    have hn_le_4M : (n : ℝ) ≤ 4 * (M : ℝ) := by linarith [hM_ge_n4]
    have hC₁_pos' : 0 < C₁ := hC₁_pos
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hM_nonneg : 0 ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le _
    -- We want: c² / (64 C₁) · n ≤ c² M / (16 C₁).
    -- Equivalently: c² n · (16 C₁) ≤ c² M · (64 C₁)
    -- ⟺ c² n · 16 ≤ c² M · 64
    -- ⟺ n ≤ 4 M.
    -- Cross-multiplication argument:
    have key : c^2 / (64 * C₁) * (n : ℝ) ≤ c^2 / (16 * C₁) * (M : ℝ) := by
      have h1 : c^2 / (64 * C₁) * (n : ℝ) ≤
                c^2 / (64 * C₁) * (4 * (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hn_le_4M
        positivity
      have h2 : c^2 / (64 * C₁) * (4 * (M : ℝ)) = c^2 / (16 * C₁) * (M : ℝ) := by
        field_simp
        ring
      linarith
    have h_rhs_eq : c^2 / (16 * C₁) * (M : ℝ) = c^2 * (M : ℝ) / (16 * C₁) := by ring
    linarith [key, h_rhs_eq.le, h_rhs_eq.symm.le]
  linarith [h_final, h_counting_2M, h_mono_real]

/-! ## Section 13 — Weighted occupied-sum variant

The singular-factor Goldbach route gives
`r(m) ≤ C m / log(m)^2 * W(m)` rather than a uniform Brun bound.  The
same counting proof still works if the weight has bounded average on the
actually occupied sumset values. -/

private lemma rep_coefficient_le_of_large
    {C₁ : ℝ} (hC₁_pos : 0 < C₁) {M m : ℕ}
    (hM_ge_two : 2 ≤ M)
    (hm_gt : Nat.sqrt (2 * M) < m) (hm_le : m ≤ 2 * M) :
    C₁ * (m : ℝ) / (Real.log (m : ℝ))^2 ≤
      8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
  have hlogM_pos : 0 < Real.log (M : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
    linarith
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hlogm_sq_pos : 0 < (Real.log (m : ℝ))^2 := by
    have hlogm_gt : Real.log (M : ℝ) / 2 < Real.log (m : ℝ) :=
      log_m_gt_half_log_M hM_ge_two hm_gt
    have hpos : 0 < Real.log (M : ℝ) / 2 := by linarith
    have : 0 < Real.log (m : ℝ) := by linarith
    positivity
  have hlogm_sq_gt : (Real.log (M : ℝ))^2 / 4 < (Real.log (m : ℝ))^2 :=
    log_m_sq_gt_quarter_log_M_sq hM_ge_two hm_gt
  have hm_real_le : (m : ℝ) ≤ 2 * (M : ℝ) := by
    have : (m : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast hm_le
    have h2 : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    linarith
  have hquarter_pos : 0 < (Real.log (M : ℝ))^2 / 4 := by linarith
  have step1 : C₁ * (m : ℝ) / (Real.log (m : ℝ))^2 ≤
               C₁ * (2 * (M : ℝ)) / (Real.log (m : ℝ))^2 := by
    have hmul_le : C₁ * (m : ℝ) ≤ C₁ * (2 * (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hm_real_le (le_of_lt hC₁_pos)
    exact div_le_div_of_nonneg_right hmul_le (le_of_lt hlogm_sq_pos)
  have step2 : C₁ * (2 * (M : ℝ)) / (Real.log (m : ℝ))^2 ≤
               C₁ * (2 * (M : ℝ)) / ((Real.log (M : ℝ))^2 / 4) := by
    have hC₁2M_nonneg : 0 ≤ C₁ * (2 * (M : ℝ)) := by
      have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le _
      have : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
      exact mul_nonneg (le_of_lt hC₁_pos) this
    apply div_le_div_of_nonneg_left hC₁2M_nonneg hquarter_pos
    linarith [hlogm_sq_gt]
  have h_eq : C₁ * (2 * (M : ℝ)) / ((Real.log (M : ℝ))^2 / 4) =
              8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 := by
    field_simp
    ring
  linarith [step1, step2, h_eq.le, h_eq.symm.le]

private lemma weighted_rep_count_le_of_large
    {W : ℕ → ℝ} (hW_nonneg : ∀ n, 0 ≤ W n)
    {C₁ : ℝ} (hC₁_pos : 0 < C₁) {N_R M m : ℕ}
    (hM_ge_two : 2 ≤ M) (hM_ge_NR_sq : N_R^2 ≤ 2 * M)
    (h_rep : ∀ n : ℕ, N_R ≤ n →
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * W n)
    (hm_gt : Nat.sqrt (2 * M) < m) (hm_le : m ≤ 2 * M) :
    (goldbachRepresentationCount m : ℝ) ≤
      (8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2) * W m := by
  have hNR_le_sqrt : N_R ≤ Nat.sqrt (2 * M) := by
    rw [Nat.le_sqrt']; exact hM_ge_NR_sq
  have hNR_le_m : N_R ≤ m := le_of_lt (lt_of_le_of_lt hNR_le_sqrt hm_gt)
  have h_rep_m := h_rep m hNR_le_m
  have hcoeff := rep_coefficient_le_of_large hC₁_pos hM_ge_two hm_gt hm_le
  exact h_rep_m.trans (mul_le_mul_of_nonneg_right hcoeff (hW_nonneg m))

private lemma prime_pairs_bound_by_weighted_sum
    (W : ℕ → ℝ) (_hW_nonneg : ∀ n, 0 ≤ W n)
    (M : ℕ) (R : ℝ) (_hR_nonneg : 0 ≤ R)
    (hR : ∀ m, Nat.sqrt (2 * M) < m → m ≤ 2 * M →
      (goldbachRepresentationCount m : ℝ) ≤ R * W m) :
    (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ) ≤
      (2 * M : ℝ) +
        R * (∑ m ∈ (Finset.Ioc (Nat.sqrt (2 * M)) (2 * M)).filter primesSumset,
          W m) := by
  classical
  set K : ℕ := Nat.sqrt (2 * M) with hK_def
  have hsum := prime_pairs_decomp_card M
  have hsmall : ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ K)).card ≤ 2 * M := card_smallPairs_le M
  have hsmall_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          pq.1 + pq.2 ≤ K)).card : ℝ) ≤ (2 * M : ℝ) := by
    exact_mod_cast hsmall
  set I : Finset ℕ :=
    (Finset.Ioc K (2 * M)).filter primesSumset with hI_def
  set f : ℕ → Finset (ℕ × ℕ) := fun m =>
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
      (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
        pq.1 + pq.2 = m) with hf_def
  have hlarge_subset := largePairs_subset_biUnion M
  have hlarge_card_le :
      ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card ≤ (I.biUnion f).card :=
    Finset.card_le_card hlarge_subset
  have hf_le_R : ∀ m ∈ I, ((f m).card : ℝ) ≤ R * W m := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmem_Ioc, _hsum⟩
    rcases Finset.mem_Ioc.mp hmem_Ioc with ⟨hK_lt, hle⟩
    have h1 : (f m).card ≤ goldbachRepresentationCount m :=
      card_primePair_sum_eq_le_r M m
    have h1' : ((f m).card : ℝ) ≤ (goldbachRepresentationCount m : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans (hR m hK_lt hle)
  have hbiUnion_card_le : ((I.biUnion f).card : ℝ) ≤ ∑ m ∈ I, ((f m).card : ℝ) := by
    have h_nat : (I.biUnion f).card ≤ ∑ m ∈ I, (f m).card :=
      Finset.card_biUnion_le
    have : ((I.biUnion f).card : ℝ) ≤ ((∑ m ∈ I, (f m).card : ℕ) : ℝ) := by
      exact_mod_cast h_nat
    refine this.trans ?_
    push_cast; rfl
  have hsum_le : (∑ m ∈ I, ((f m).card : ℝ)) ≤ ∑ m ∈ I, R * W m :=
    Finset.sum_le_sum (fun m hm => hf_le_R m hm)
  have hsum_mul :
      (∑ m ∈ I, R * W m) = R * (∑ m ∈ I, W m) := by
    rw [Finset.mul_sum]
  have hlarge_card_le_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ) ≤ ((I.biUnion f).card : ℝ) := by
    exact_mod_cast hlarge_card_le
  have hlarge_real :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ) ≤
        R * (∑ m ∈ I, W m) := by
    calc (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
          K < pq.1 + pq.2)).card : ℝ)
        ≤ ((I.biUnion f).card : ℝ) := hlarge_card_le_real
      _ ≤ ∑ m ∈ I, ((f m).card : ℝ) := hbiUnion_card_le
      _ ≤ ∑ m ∈ I, R * W m := hsum_le
      _ = R * (∑ m ∈ I, W m) := hsum_mul
  simpa [hK_def, hI_def] using (by linarith [hsum, hsmall_real, hlarge_real])

private lemma weighted_counting_lower_bound_even
    {W : ℕ → ℝ} (hW_nonneg : ∀ n, 0 ≤ W n)
    {C₁ A c : ℝ} (hC₁_pos : 0 < C₁) (hA_pos : 0 < A) (hc_pos : 0 < c)
    {N_R N_A M : ℕ}
    (hM_ge_two : 2 ≤ M) (hM_ge_NR_sq : N_R^2 ≤ 2 * M)
    (hM_ge_NA : N_A ≤ 2 * M)
    (h_rep : ∀ n : ℕ, N_R ≤ n →
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * W n)
    (h_occ : ∀ N : ℕ, N_A ≤ N →
      (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, W n) ≤
        A * (Gdbh.countingUpTo primesSumset N : ℝ))
    (h_cheb : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ)) :
    c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 ≤
      (2 * M : ℝ) +
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
          (8 * (C₁ * A) * (M : ℝ) / (Real.log (M : ℝ))^2) := by
  classical
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by linarith
  have hπ_ge : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ) := h_cheb
  have hcM_div_pos : 0 < c * (M : ℝ) / Real.log (M : ℝ) := by
    apply div_pos
    · exact mul_pos hc_pos hM_real_pos
    · exact hlogM_pos
  have hπ_sq_ge : (c * (M : ℝ) / Real.log (M : ℝ))^2 ≤
                  ((Nat.primeCounting M : ℝ))^2 := by
    apply sq_le_sq'
    · linarith [hcM_div_pos]
    · exact hπ_ge
  have h_sq_eq : (c * (M : ℝ) / Real.log (M : ℝ))^2 =
                 c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 := by
    rw [div_pow, mul_pow]
  rw [h_sq_eq] at hπ_sq_ge
  set R : ℝ := 8 * C₁ * (M : ℝ) / (Real.log (M : ℝ))^2 with hR_def
  have hR_nonneg : 0 ≤ R := by
    rw [hR_def]
    positivity
  have hR_bound :
    ∀ m, Nat.sqrt (2 * M) < m → m ≤ 2 * M →
      (goldbachRepresentationCount m : ℝ) ≤ R * W m := by
    intro m hm_gt hm_le
    rw [hR_def]
    exact weighted_rep_count_le_of_large hW_nonneg hC₁_pos hM_ge_two
      hM_ge_NR_sq h_rep hm_gt hm_le
  have hpair_weighted := prime_pairs_bound_by_weighted_sum W hW_nonneg M R
    hR_nonneg hR_bound
  set I : Finset ℕ := (Finset.Ioc (Nat.sqrt (2 * M)) (2 * M)).filter primesSumset
    with hI_def
  set J : Finset ℕ := (Finset.Icc 2 (2 * M)).filter primesSumset with hJ_def
  have hsqrt_ge_two : 2 ≤ Nat.sqrt (2 * M) := by
    exact Nat.le_sqrt.mpr (by omega : 2 * 2 ≤ 2 * M)
  have hI_sub_J : I ⊆ J := by
    intro m hm
    rw [hI_def] at hm
    rw [hJ_def]
    rcases Finset.mem_filter.mp hm with ⟨hmem_Ioc, hsumset⟩
    rcases Finset.mem_Ioc.mp hmem_Ioc with ⟨hK_lt, hm_le⟩
    refine Finset.mem_filter.mpr ⟨?_, hsumset⟩
    refine Finset.mem_Icc.mpr ⟨?_, hm_le⟩
    exact le_trans hsqrt_ge_two (le_of_lt hK_lt)
  have hsumI_le_J : (∑ m ∈ I, W m) ≤ ∑ m ∈ J, W m :=
    Finset.sum_le_sum_of_subset_of_nonneg hI_sub_J
      (fun x _hxJ _hxI => hW_nonneg x)
  have hoccM : (∑ m ∈ J, W m) ≤
      A * (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) := by
    simpa [hJ_def] using h_occ (2 * M) hM_ge_NA
  have hsumI_le_count :
      (∑ m ∈ I, W m) ≤
        A * (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) :=
    hsumI_le_J.trans hoccM
  have hweighted_to_count :
      R * (∑ m ∈ I, W m) ≤
        R * (A * (Gdbh.countingUpTo primesSumset (2 * M) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsumI_le_count hR_nonneg
  have hpair_count :
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ) ≤
      (2 * M : ℝ) +
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
          (8 * (C₁ * A) * (M : ℝ) / (Real.log (M : ℝ))^2) := by
    have hrewrite :
        R * (A * (Gdbh.countingUpTo primesSumset (2 * M) : ℝ)) =
          (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
            (8 * (C₁ * A) * (M : ℝ) / (Real.log (M : ℝ))^2) := by
      rw [hR_def]
      field_simp
    calc
      (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq : ℕ × ℕ => Nat.Prime pq.1 ∧ Nat.Prime pq.2)).card : ℝ)
          ≤ (2 * M : ℝ) + R * (∑ m ∈ I, W m) := by
              simpa [hI_def] using hpair_weighted
      _ ≤ (2 * M : ℝ) + R *
            (A * (Gdbh.countingUpTo primesSumset (2 * M) : ℝ)) := by
              linarith
      _ = (2 * M : ℝ) +
            (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
              (8 * (C₁ * A) * (M : ℝ) / (Real.log (M : ℝ))^2) := by
              rw [hrewrite]
  have hpair_eq := card_primePairs_eq_primeCounting_sq M
  rw [hpair_eq] at hpair_count
  linarith [hπ_sq_ge, hpair_count]

private lemma counting_lower_bound_even_absorbed_of_bound
    {C c count : ℝ} (hC_pos : 0 < C) (hc_pos : 0 < c)
    {M : ℕ} (hM_ge_two : 2 ≤ M)
    (hbound : c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 ≤
      (2 * M : ℝ) + count * (8 * C * (M : ℝ) / (Real.log (M : ℝ))^2))
    (h_absorb : 4 * (Real.log (M : ℝ))^2 ≤ c^2 * (M : ℝ)) :
    c^2 * (M : ℝ) / (16 * C) ≤ count := by
  have hlogM_pos : 0 < Real.log (M : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
    linarith
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
    linarith
  set L := Real.log (M : ℝ) with hL_def
  have hbound2 : c^2 * (M : ℝ)^2 ≤ 2 * (M : ℝ) * L^2 + count * (8 * C * (M : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hbound (le_of_lt hlogM_sq_pos)
    have hLHS : c^2 * (M : ℝ)^2 / L^2 * L^2 = c^2 * (M : ℝ)^2 := by
      field_simp
    have hRHS : ((2 * M : ℝ) + count * (8 * C * (M : ℝ) / L^2)) * L^2 =
                2 * (M : ℝ) * L^2 + count * (8 * C * (M : ℝ)) := by
      field_simp
    rw [hLHS] at this
    rw [hRHS] at this
    exact this
  have hstep : c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2 ≤
               count * (8 * C * (M : ℝ)) := by linarith
  have h8CM_pos : 0 < 8 * C * (M : ℝ) := by positivity
  have hdiv : (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) / (8 * C * (M : ℝ)) ≤ count := by
    rw [div_le_iff₀ h8CM_pos]
    linarith
  have h_target : c^2 * (M : ℝ) / (16 * C) ≤
        (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) / (8 * C * (M : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C) h8CM_pos]
    have h_simp : c^2 * (M : ℝ) * (8 * C * (M : ℝ)) ≤
                  (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) * (16 * C) := by
      have : (c^2 * (M : ℝ)^2 - 2 * (M : ℝ) * L^2) * (16 * C) =
             16 * C * c^2 * (M : ℝ)^2 - 32 * C * (M : ℝ) * L^2 := by ring
      rw [this]
      have h1 : c^2 * (M : ℝ) * (8 * C * (M : ℝ)) =
                8 * C * c^2 * (M : ℝ)^2 := by ring
      rw [h1]
      have habsorb_mult : 4 * L^2 * (8 * C * (M : ℝ)) ≤
                          c^2 * (M : ℝ) * (8 * C * (M : ℝ)) := by
        exact mul_le_mul_of_nonneg_right h_absorb (le_of_lt h8CM_pos)
      nlinarith [habsorb_mult, sq_nonneg (M : ℝ), sq_nonneg L, hC_pos, hM_real_pos]
    exact h_simp
  linarith [hdiv, h_target]

open Filter in
/-- Weighted Schnirelmann counting bridge.  This is the generic form used by
the singular-factor route: pointwise representation control with weight `W`,
plus average control of `W` on occupied sumset values, implies the asymptotic
linear lower bound for `primesSumset`. -/
theorem weightedRepBoundAndOccupiedAverageToAsymptotic
    (W : ℕ → ℝ) (hW_nonneg : ∀ n, 0 ≤ W n)
    (hRep : ∃ C₁ : ℝ, ∃ N_R : ℕ, 0 < C₁ ∧
      ∀ n : ℕ, N_R ≤ n →
        (goldbachRepresentationCount n : ℝ) ≤
          C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * W n)
    (hOcc : ∃ A : ℝ, ∃ N_A : ℕ, 0 < A ∧
      ∀ N : ℕ, N_A ≤ N →
        (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, W n) ≤
          A * (Gdbh.countingUpTo primesSumset N : ℝ))
    (hCheb : ChebyshevPrimeLowerBound) :
    PrimesSumsetAsymptoticLowerBound := by
  obtain ⟨C₁, N_R, hC₁_pos, h_rep⟩ := hRep
  obtain ⟨A, N_A, hA_pos, h_occ⟩ := hOcc
  obtain ⟨c, N_C, hc_pos, h_cheb⟩ := hCheb
  set Ceff : ℝ := C₁ * A with hCeff_def
  have hCeff_pos : 0 < Ceff := by
    rw [hCeff_def]
    exact mul_pos hC₁_pos hA_pos
  set ε : ℝ := c^2 / (64 * Ceff) with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]; positivity
  obtain ⟨N_log, hN_log⟩ :=
    Filter.eventually_atTop.mp (eventually_log_sq_lt_const_mul hc_pos)
  set N₀ : ℕ :=
    max (2 * N_C + 2)
      (max (N_R^2 + 2) (max (N_A + 2) (max (2 * N_log + 2) 4))) with hN₀_def
  refine ⟨ε, N₀, hε_pos, ?_⟩
  intro n hn
  set M : ℕ := n / 2 with hM_def
  have h2M_le_n : 2 * M ≤ n := by
    rw [hM_def]
    have := Nat.div_add_mod n 2
    omega
  have h2M_ge_pred : n - 1 ≤ 2 * M := by
    rw [hM_def]
    have := Nat.div_add_mod n 2
    have hmod_lt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have hM_ge_two : 2 ≤ M := by
    have hn_ge_4 : 4 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  have hM_ge_NC : N_C ≤ M := by
    have hn_ge : 2 * N_C + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  have h2M_ge_NR_sq : N_R^2 ≤ 2 * M := by
    have hn_ge : N_R^2 + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    omega
  have h2M_ge_NA : N_A ≤ 2 * M := by
    have hn_ge : N_A + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    omega
  have hM_ge_Nlog : N_log ≤ M := by
    have hn_ge : 2 * N_log + 2 ≤ n := by
      have h := hn
      rw [hN₀_def] at h
      simp at h
      omega
    rw [hM_def]; omega
  have h_cheb_M : c * (M : ℝ) / Real.log (M : ℝ) ≤ (Nat.primeCounting M : ℝ) :=
    h_cheb M hM_ge_NC
  have h_absorb : 4 * (Real.log (M : ℝ))^2 ≤ c^2 * (M : ℝ) :=
    hN_log M hM_ge_Nlog
  have hbound := weighted_counting_lower_bound_even hW_nonneg hC₁_pos hA_pos
    hc_pos hM_ge_two h2M_ge_NR_sq h2M_ge_NA h_rep h_occ h_cheb_M
  have h_counting_2M : c^2 * (M : ℝ) / (16 * Ceff) ≤
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) := by
    have hbound' : c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 ≤
      (2 * M : ℝ) +
        (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
          (8 * Ceff * (M : ℝ) / (Real.log (M : ℝ))^2) := by
      simpa [hCeff_def, mul_assoc, mul_left_comm, mul_comm] using hbound
    exact counting_lower_bound_even_absorbed_of_bound hCeff_pos hc_pos
      hM_ge_two hbound' h_absorb
  have h_mono : Gdbh.countingUpTo primesSumset (2 * M) ≤
                Gdbh.countingUpTo primesSumset n :=
    countingUpTo_mono _ h2M_le_n
  have h_mono_real :
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) ≤
      (Gdbh.countingUpTo primesSumset n : ℝ) := by
    exact_mod_cast h_mono
  have hn_ge_two : 2 ≤ n := by
    have h := hn
    rw [hN₀_def] at h
    simp at h
    omega
  have hM_real_ge : (n - 1 : ℝ) / 2 ≤ (M : ℝ) := by
    have h2M_ge : ((n - 1 : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
      exact_mod_cast h2M_ge_pred
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have hn_ge_1 : 1 ≤ n := by omega
      have : ((n - 1) + 1 : ℕ) = n := by omega
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast this
      linarith
    rw [h1] at h2M_ge
    have h2M_cast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    rw [h2M_cast] at h2M_ge
    linarith
  have hn_real_ge : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_two
    linarith
  have hM_ge_n4 : (n : ℝ) / 4 ≤ (M : ℝ) := by
    have h1 : (n : ℝ) / 4 = ((n : ℝ) / 2) / 2 := by ring
    rw [h1]
    have : ((n : ℝ) / 2) / 2 ≤ ((n : ℝ) - 1) / 2 :=
      div_le_div_of_nonneg_right hn_real_ge (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have h_final : ε * (n : ℝ) ≤ c^2 * (M : ℝ) / (16 * Ceff) := by
    rw [hε_def]
    have hn_le_4M : (n : ℝ) ≤ 4 * (M : ℝ) := by linarith [hM_ge_n4]
    have key : c^2 / (64 * Ceff) * (n : ℝ) ≤
                c^2 / (64 * Ceff) * (4 * (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hn_le_4M
      positivity
    have h2 : c^2 / (64 * Ceff) * (4 * (M : ℝ)) =
              c^2 * (M : ℝ) / (16 * Ceff) := by
      field_simp
      ring
    linarith [key, h2.le, h2.symm.le]
  linarith [h_final, h_counting_2M, h_mono_real]

end PathCRepBoundCounting
end Gdbh
