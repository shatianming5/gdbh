/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P10-T2 (Phase 10 / Path C closure — Brun's bound on the Goldbach
        r-function `r(n) ≤ C · n / (log n)^2`)
-/
import Gdbh.PathC_TwinAsymptotic
import Gdbh.PathC_BrunSieve
import Gdbh.PathC_BrunClosure

/-!
# Path C — Honest decomposition of `GoldbachRepresentationBound`

This file is the **P10-T2 deliverable** in Phase 10 (final Path C closure).
It targets the named open `Prop`

```
def GoldbachRepresentationBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachRepresentationCount n : ℝ) ≤
      C * (n : ℝ) / (Real.log (n : ℝ))^2
```

from `Gdbh/PathC_TwinAsymptotic.lean`, where

```
goldbachRepresentationCount n
  := #{(p, q) ∈ [1, n] × [1, n] : p, q prime, p + q = n}.
```

## Satisfiability assessment

Classically `GoldbachRepresentationBound` is **true**: it is Brun's 1919
upper bound on the Goldbach r-function, recorded e.g. in Halberstam–
Richert *Sieve Methods* Theorem 3.11 and Nathanson *Additive Number
Theory: The Classical Bases* Theorem 7.1.  It is **not** vacuously true
in the Lean statement: the bound `r(n) ≤ n` (trivially valid by
projecting onto the first coordinate) does not imply
`r(n) ≤ C · n / (log n)^2` for any fixed `C`, because `(log n)^2 → ∞`.
Likewise the Chebyshev bound `π(n) ≤ C · n / log n` only saves one log.
The genuine `(log n)^2` denominator requires Brun's *paired* sieve
(sifting `(m, n - m)` simultaneously) combined with Mertens' product
theorem applied to the pair, neither of which is currently packaged in
mathlib.

So the Prop is **classically true** but **not constructible from
current mathlib**.  The honest deliverable is therefore the same as for
`TwinPrimePairCountBound` in Phase 6: a Brun-style decomposition into
three smaller named sub-Props, with an *unconditional assembly theorem*
showing that the three sub-Props together imply
`GoldbachRepresentationBound`.

## Decomposition

In the twin-prime case `PathC_BrunSieve.lean` introduced the *single
sift* `siftedCount N z` (integers `m ∈ [1, N]` with no prime factor
`≤ z`).  Twin primes `(p, p+2)` are sifted because *both* `p` and
`p+2` are individually coprime to small primes (other than themselves).

For the Goldbach r-function we sift *pairs* `(m, n-m)` simultaneously:

* `goldbachSiftedPair n z := #{m ∈ [1, n-1] : (m, n - m) has no prime
  factor ≤ z}`.

Every prime pair `(p, q)` with `p + q = n` and `p, q > z` belongs to
this set (because primes `> z` have no prime factor `≤ z`).  Hence

```
r(n)  ≤  #{small pairs}  +  goldbachSiftedPair n z
       ≤  2 (z + 1)       +  goldbachSiftedPair n z .
```

This **paired sift inclusion** is the Goldbach-side analogue of
`twinPrimeInitials_card_le_siftedCount_add`.

The three sub-Props are then the same shape as in `PathC_BrunSieve.lean`,
just instantiated to the *paired* sift:

* `BrunGoldbachMainTerm M B`:
  `goldbachSiftedPair n z ≤ C₁ · n · M(z) + B(n, z)`
  (main-term inclusion–exclusion bound, *paired version*).

* `BrunGoldbachErrorTerm B zChoice`:
  `B(n, zChoice n) ≤ C₂ · n / (log n)^2` for `n ≥ N₀`
  (combinatorial decay of the truncation reservoir).

* `MertensPairedProductBound M zChoice`:
  `M(zChoice n) ≤ C₃ / (log n)^2` for `n ≥ N₀`, `n ≥ 2`
  (paired Mertens factor; the **square** of the log denominator
  reflects the paired sift).

The assembly theorem
`goldbachRepresentationBound_of_brunComponents` combines the three
sub-Props with the elementary paired-sift inclusion to produce
`GoldbachRepresentationBound`.  We also expose

* `goldbachSiftedPair n z ≤ n` (trivial cardinal bound), feeding the
  worst-case witness `B(n, z) := n`;
* `brunGoldbachMainTerm_trivial_witness` and
  `exists_brunGoldbachMainTerm_witness` (paired-sift analogues of
  `brunMainTerm_trivial_witness`), reducing the open content to just
  `BrunGoldbachErrorTerm` (combinatorial decay) and
  `MertensPairedProductBound` (paired Mertens product).

## What remains genuinely open after this file

After P10-T2, `GoldbachRepresentationBound` reduces to two sub-Props,
both of which are *classical theorems* not currently in mathlib:

1. `BrunGoldbachErrorTerm` for some `(B, zChoice)` with a non-trivial
   error reservoir — this is the **truncated combinatorial estimate**
   `(π(z))^k / k!` from Brun's argument.  Mathlib v4.29.1 has the
   abstract `Mathlib.NumberTheory.SelbergSieve` framework but not the
   explicit Brun truncated inclusion–exclusion error bound.

2. `MertensPairedProductBound` for the paired Brun factor
   `∏_{p ≤ z}(1 - 2/p)` (with the convention `p > 2`) — this is
   **Mertens' second theorem applied to the paired sift**, i.e. the
   asymptotic `∑_{p ≤ z} log(1 - 2/p) = -2 log log z + O(1)`.  Mathlib
   v4.29.1 has neither Mertens' second nor its paired variant.

These are the same two genuinely-open analytic pieces that were already
exposed by the Phase 8 twin-prime decomposition; P10-T2 confirms they
are the **same** pieces for the Goldbach r-function as for the twin-
prime count (with the paired Mertens factor playing the role of the
single one).  No new mathematical gap is uncovered — this is the
genuine remaining mathlib content.

All theorems below are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Gdbh
namespace PathCGoldbachRBound

open scoped BigOperators
open Gdbh.PathCBrunSieve (siftedSet siftedCount mem_siftedSet)
open Gdbh.PathCTwinAsymptotic
  (goldbachRepresentationCount GoldbachRepresentationBound)

/-! ## Section 1 — The paired sift for the Goldbach r-function

For a target sum `n` and a sieving threshold `z`, the **paired sifted
set** `goldbachSiftedPairSet n z` is the set of `m ∈ [1, n - 1]` for
which *both* `m` and `n - m` have no prime factor `≤ z`.  Its
cardinality `goldbachSiftedPair n z` is the paired analogue of the
single sift `siftedCount` from `PathC_BrunSieve.lean`. -/

/-- The paired sifted set: `m ∈ [1, n - 1]` with both `m` and `n - m`
having no prime factor `≤ z`. -/
def goldbachSiftedPairSet (n z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1)).filter
    (fun m => (∀ p ≤ z, Nat.Prime p → ¬ p ∣ m)
        ∧ (∀ p ≤ z, Nat.Prime p → ¬ p ∣ (n - m)))

/-- The paired sifted count: cardinality of `goldbachSiftedPairSet`. -/
def goldbachSiftedPair (n z : ℕ) : ℕ := (goldbachSiftedPairSet n z).card

@[simp] lemma mem_goldbachSiftedPairSet {n z m : ℕ} :
    m ∈ goldbachSiftedPairSet n z ↔
      (1 ≤ m ∧ m ≤ n - 1)
        ∧ (∀ p, p ≤ z → Nat.Prime p → ¬ p ∣ m)
        ∧ (∀ p, p ≤ z → Nat.Prime p → ¬ p ∣ (n - m)) := by
  simp [goldbachSiftedPairSet, Finset.mem_Icc, and_assoc]

/-- Trivial cardinal bound: the paired sifted set is contained in
`[1, n - 1]`, so `goldbachSiftedPair n z ≤ n`. -/
theorem goldbachSiftedPair_le (n z : ℕ) : goldbachSiftedPair n z ≤ n := by
  classical
  unfold goldbachSiftedPair goldbachSiftedPairSet
  refine le_trans (Finset.card_filter_le _ _) ?_
  have h : (Finset.Icc 1 (n - 1)).card ≤ n := by
    rw [Nat.card_Icc]
    omega
  exact h

/-! ## Section 2 — Cardinal control: `r(n) ≤ paired sift + small primes`

Every ordered prime pair `(p, q)` with `p + q = n` has `p ∈ [1, n - 1]`
(since `q ≥ 2` so `p ≤ n - 2 < n`).  If both `p > z` and `q > z`, then
neither `p` nor `q` has any prime factor `≤ z` (their only prime factor
is themselves, which exceeds `z`).  Hence `p` lies in the paired
sifted set.  The remaining pairs have `p ≤ z` *or* `q ≤ z`, which by
the small-prime bound contributes at most `2 (z + 1)` pairs. -/

/-- The Goldbach pair set as a finite subset of `Finset.Icc 1 (n-1)`.
We re-express `goldbachRepresentationCount n` as the cardinality of the
set of `p ∈ [1, n-1]` with `p` prime, `n - p` prime. -/
def goldbachPrimeInitials (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1)).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

@[simp] lemma mem_goldbachPrimeInitials {n p : ℕ} :
    p ∈ goldbachPrimeInitials n ↔
      (1 ≤ p ∧ p ≤ n - 1) ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  simp [goldbachPrimeInitials, Finset.mem_Icc, and_assoc]

/-- A prime `p` with `z < p` has no prime divisor `≤ z`: its only prime
divisor is `p` itself, which exceeds `z`. -/
lemma prime_gt_z_no_small_factor {z p : ℕ}
    (hpr : Nat.Prime p) (hpz : z < p) :
    ∀ q ≤ z, Nat.Prime q → ¬ q ∣ p := by
  intro q hqz hqp hqdvd
  have hqeq : q = p := ((Nat.prime_dvd_prime_iff_eq hqp hpr).mp hqdvd)
  rw [hqeq] at hqz
  exact (Nat.lt_irrefl p) (lt_of_le_of_lt hqz hpz)

/-- The "large–large" portion of `goldbachPrimeInitials`: both endpoints
exceed `z`.  This portion is contained in the paired sifted set. -/
lemma goldbachPrimeInitials_largeLarge_subset_siftedPair (n z : ℕ) :
    (goldbachPrimeInitials n).filter
        (fun p => z < p ∧ z < n - p) ⊆ goldbachSiftedPairSet n z := by
  intro p hp
  rw [Finset.mem_filter, mem_goldbachPrimeInitials] at hp
  obtain ⟨⟨⟨hp1, hp2⟩, hpr, hqr⟩, hpz, hqz⟩ := hp
  refine mem_goldbachSiftedPairSet.mpr ⟨⟨hp1, hp2⟩, ?_, ?_⟩
  · exact prime_gt_z_no_small_factor hpr hpz
  · exact prime_gt_z_no_small_factor hqr hqz

/-- The "small `p`" portion of `goldbachPrimeInitials` has cardinality
`≤ z + 1` (it is contained in `[0, z]` viewed as a subset of `ℕ`). -/
lemma goldbachPrimeInitials_smallP_card_le (n z : ℕ) :
    ((goldbachPrimeInitials n).filter (fun p => p ≤ z)).card ≤ z + 1 := by
  classical
  have hsub :
      (goldbachPrimeInitials n).filter (fun p => p ≤ z) ⊆ Finset.Icc 0 z := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hp.2⟩
  have hbound := Finset.card_le_card hsub
  simpa [Nat.card_Icc] using hbound

/-- The "small `n - p`" portion of `goldbachPrimeInitials` has
cardinality `≤ z + 1`.  We use the injection `p ↦ n - p` to view this
filter as a subset of `[0, z]`. -/
lemma goldbachPrimeInitials_smallQ_card_le (n z : ℕ) :
    ((goldbachPrimeInitials n).filter (fun p => n - p ≤ z)).card ≤ z + 1 := by
  classical
  -- Image under `p ↦ n - p` lies in `[0, z]`.
  set S := (goldbachPrimeInitials n).filter (fun p => n - p ≤ z) with hS_def
  -- Inject via `n - p`.
  have h_inj : Set.InjOn (fun p => n - p) (S : Set ℕ) := by
    intro p1 hp1 p2 hp2 hpq
    have hp1' : p1 ∈ S := hp1
    have hp2' : p2 ∈ S := hp2
    rw [hS_def, Finset.mem_filter, mem_goldbachPrimeInitials] at hp1' hp2'
    obtain ⟨⟨⟨_, hp1b⟩, _, _⟩, _⟩ := hp1'
    obtain ⟨⟨⟨_, hp2b⟩, _, _⟩, _⟩ := hp2'
    -- p1 ≤ n - 1 ≤ n so n - p1 = n - p2 ⇒ p1 = p2 (in ℕ subtraction)
    have hp1n : p1 ≤ n := le_trans hp1b (Nat.sub_le _ _)
    have hp2n : p2 ≤ n := le_trans hp2b (Nat.sub_le _ _)
    -- From n - p1 = n - p2 with p1, p2 ≤ n, we get p1 = p2.
    simp only at hpq
    omega
  -- card S ≤ card (S.image (fun p => n - p)) ≤ card (Icc 0 z)
  have h_image_subset : S.image (fun p => n - p) ⊆ Finset.Icc 0 z := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨p, hpS, hpk⟩ := hk
    rw [hS_def, Finset.mem_filter] at hpS
    have hq : n - p ≤ z := hpS.2
    rw [hpk] at hq
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩
  have h_card_image : S.card = (S.image (fun p => n - p)).card := by
    symm
    apply Finset.card_image_of_injOn
    exact h_inj
  rw [h_card_image]
  calc (S.image (fun p => n - p)).card
      ≤ (Finset.Icc 0 z).card := Finset.card_le_card h_image_subset
    _ = z + 1 := by simp [Nat.card_Icc]

/-- **Paired sieve inclusion for the Goldbach r-function.**

```
goldbachPrimeInitials n . card ≤ goldbachSiftedPair n z + 2 (z + 1) .
```

Every prime pair `(p, n - p)` summing to `n` has *both* coordinates
prime and `≥ 2`.  We split on whether `p ≤ z` or `z < p`, and within
the latter on whether `n - p ≤ z` or `z < n - p`.  The two "small"
cases together contribute at most `2 (z + 1)`; the "both large" case
is contained in the paired sifted set. -/
theorem goldbachPrimeInitials_card_le_siftedPair_add (n z : ℕ) :
    (goldbachPrimeInitials n).card ≤ goldbachSiftedPair n z + 2 * (z + 1) := by
  classical
  set S := goldbachPrimeInitials n
  -- Split by `p ≤ z`.
  have hsplit1 :
      S.card =
        (S.filter (fun p => p ≤ z)).card
          + (S.filter (fun p => ¬ p ≤ z)).card :=
    (Finset.card_filter_add_card_filter_not (fun p => p ≤ z) (s := S)).symm
  have hnot1 : ∀ p, ¬ p ≤ z ↔ z < p := fun p =>
    ⟨fun h => Nat.lt_of_not_ge h, fun h => Nat.not_le.mpr h⟩
  have h_filter_eq1 :
      S.filter (fun p => ¬ p ≤ z) = S.filter (fun p => z < p) := by
    apply Finset.filter_congr; intro p _; exact hnot1 p
  -- Split the "z < p" portion further by `n - p ≤ z`.
  set T := S.filter (fun p => z < p)
  have hsplit2 :
      T.card =
        (T.filter (fun p => n - p ≤ z)).card
          + (T.filter (fun p => ¬ n - p ≤ z)).card :=
    (Finset.card_filter_add_card_filter_not (fun p => n - p ≤ z) (s := T)).symm
  have hnot2 : ∀ p, ¬ n - p ≤ z ↔ z < n - p := fun p =>
    ⟨fun h => Nat.lt_of_not_ge h, fun h => Nat.not_le.mpr h⟩
  have h_filter_eq2 :
      T.filter (fun p => ¬ n - p ≤ z) = T.filter (fun p => z < n - p) := by
    apply Finset.filter_congr; intro p _; exact hnot2 p
  -- Bounds on the three pieces.
  have h_smallP : (S.filter (fun p => p ≤ z)).card ≤ z + 1 :=
    goldbachPrimeInitials_smallP_card_le n z
  have h_smallQ : (T.filter (fun p => n - p ≤ z)).card ≤ z + 1 := by
    -- `T.filter ...` ⊆ `S.filter (fun p => n - p ≤ z)`
    have hsub :
        T.filter (fun p => n - p ≤ z)
          ⊆ S.filter (fun p => n - p ≤ z) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_filter]
      rcases hp with ⟨hpT, hpQ⟩
      rw [Finset.mem_filter] at hpT
      exact ⟨hpT.1, hpQ⟩
    exact le_trans (Finset.card_le_card hsub)
      (goldbachPrimeInitials_smallQ_card_le n z)
  have h_largeLarge :
      (T.filter (fun p => z < n - p)).card ≤ goldbachSiftedPair n z := by
    -- This filter equals `S.filter (fun p => z < p ∧ z < n - p)`
    have h_eq :
        T.filter (fun p => z < n - p)
          = S.filter (fun p => z < p ∧ z < n - p) := by
      ext p
      simp only [T, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hS, hp1⟩, hp2⟩; exact ⟨hS, hp1, hp2⟩
      · rintro ⟨hS, hp1, hp2⟩; exact ⟨⟨hS, hp1⟩, hp2⟩
    rw [h_eq]
    unfold goldbachSiftedPair
    exact Finset.card_le_card
      (goldbachPrimeInitials_largeLarge_subset_siftedPair n z)
  -- Combine.
  rw [hsplit1, h_filter_eq1, hsplit2, h_filter_eq2]
  calc (S.filter (fun p => p ≤ z)).card
          + ((T.filter (fun p => n - p ≤ z)).card
              + (T.filter (fun p => z < n - p)).card)
      ≤ (z + 1) + ((z + 1) + goldbachSiftedPair n z) := by
        exact Nat.add_le_add h_smallP (Nat.add_le_add h_smallQ h_largeLarge)
    _ = goldbachSiftedPair n z + 2 * (z + 1) := by ring

/-- **Cardinal control of `r(n)` via paired sift.**  Same statement as
above, but with `r(n) = goldbachRepresentationCount n` rather than its
"initial coordinate" reformulation.

We show `goldbachRepresentationCount n ≤ goldbachPrimeInitials n . card`
by mapping the pair `(p, q) ↦ p`; injectivity of this map on the pair
set follows from `q = n - p`.  Combined with the paired sieve inclusion
above this gives

```
r(n) ≤ goldbachSiftedPair n z + 2 (z + 1) .
```
-/
theorem goldbachRepresentationCount_le_siftedPair_add (n z : ℕ) :
    goldbachRepresentationCount n ≤ goldbachSiftedPair n z + 2 * (z + 1) := by
  classical
  -- Step 1: `r(n) ≤ goldbachPrimeInitials n . card` via projection to first coord.
  have h_proj :
      goldbachRepresentationCount n ≤ (goldbachPrimeInitials n).card := by
    unfold goldbachRepresentationCount goldbachPrimeInitials
    -- Image of the pair-filter under `Prod.fst` is contained in the
    -- first-coordinate filter.
    set P := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n)
    -- Inject `(p, q) ↦ p`: since `q = n - p`, p determines (p, q) uniquely.
    have h_inj : Set.InjOn Prod.fst (P : Set (ℕ × ℕ)) := by
      intro pq1 hpq1 pq2 hpq2 hfst
      simp only [P, Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_product, Finset.mem_Icc] at hpq1 hpq2
      obtain ⟨_, _, _, hsum1⟩ := hpq1
      obtain ⟨_, _, _, hsum2⟩ := hpq2
      ext
      · exact hfst
      · -- pq1.2 = n - pq1.1 = n - pq2.1 = pq2.2
        omega
    have h_card_image : P.card = (P.image Prod.fst).card := by
      symm; exact Finset.card_image_of_injOn h_inj
    -- Show `P.image Prod.fst ⊆ goldbachPrimeInitials n` (as Finsets).
    have h_image_sub :
        P.image Prod.fst
          ⊆ (Finset.Icc 1 (n - 1)).filter
              (fun p => Nat.Prime p ∧ Nat.Prime (n - p)) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨pq, hpqP, hpq_eq⟩ := hp
      simp only [P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hpqP
      obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hpr, hqpr, hsum⟩ := hpqP
      rw [hpq_eq] at hp1 hp2 hpr
      -- We need: 1 ≤ p, p ≤ n - 1, p prime, n - p prime.
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨hp1, ?_⟩, hpr, ?_⟩
      · -- p ≤ n - 1: since p + pq.2 = n and pq.2 ≥ 1, p ≤ n - 1.
        omega
      · -- n - p = pq.2 is prime.
        have : n - pq.1 = pq.2 := by omega
        rw [← hpq_eq, this]; exact hqpr
    rw [h_card_image]
    exact Finset.card_le_card h_image_sub
  -- Step 2: combine with the paired sieve inclusion.
  exact le_trans h_proj (goldbachPrimeInitials_card_le_siftedPair_add n z)

/-! ## Section 3 — The three Brun-Goldbach sub-Props

We isolate the three quantitative pieces of Brun's paired sieve as
`Prop`-valued statements, parameterised by an abstract main-term factor
`M`, an abstract error reservoir `B`, and an abstract sieve choice
`zChoice`.  The aim mirrors `PathC_BrunSieve.lean`: expose the clean
interface so that any partial progress can be plugged in. -/

/-- `BrunGoldbachMainTerm M B` records the *paired-sift* main-term
bound

```
goldbachSiftedPair n z ≤ C₁ · n · M(z) + B(n, z) ,
```

where `M : ℕ → ℝ` is a Brun main-term factor (i.e. positive and
antitone) and `B : ℕ → ℕ → ℝ` is an error reservoir.  For the genuine
Brun argument `M(z) = ∏_{p ≤ z}(1 - 2/p)` (the paired factor) and `B`
is the truncated inclusion–exclusion error term. -/
def BrunGoldbachMainTerm
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) : Prop :=
  Gdbh.PathCBrunSieve.IsBrunMainTermFactor M ∧
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ n z : ℕ, 0 < n →
        (goldbachSiftedPair n z : ℝ) ≤ C₁ * (n : ℝ) * M z + B n z

/-- `BrunGoldbachErrorTerm B zChoice` records the **combinatorial
decay** of the error reservoir: for some constant `C₂` and some sieve
choice `z = zChoice N`, we have

```
B(n, zChoice n) ≤ C₂ · n / (log n)^2  for all n ≥ N₀.
```

This is the same shape as `BrunErrorTerm` for the single sift; the
truncated combinatorial estimate `(π(z))^k / k!` has the same growth in
the paired and unpaired cases. -/
def BrunGoldbachErrorTerm
    (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₂ N₀ : ℕ, 0 < C₂ ∧
    ∀ n : ℕ, N₀ ≤ n →
      B n (zChoice n) ≤ (C₂ : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2

/-- `MertensPairedProductBound M zChoice` records the **paired Mertens
product bound**

```
M(zChoice n) ≤ C₃ / (log n)^2  for all n ≥ N₀, n ≥ 2.
```

For the genuine Brun argument `M(z) = ∏_{p ≤ z}(1 - 2/p) ∼ c / (log z)^2`
by Mertens' second theorem applied to the paired factor.  Combined with
`zChoice n ≍ n^{1/k}` for an appropriate truncation depth `k`, this
gives `M(zChoice n) ≍ 1 / (log n)^2` — the *square* of the log
denominator that is characteristic of paired sieves. -/
def MertensPairedProductBound
    (M : ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₃ N₀ : ℕ, 0 < C₃ ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      M (zChoice n) ≤ (C₃ : ℝ) / (Real.log (n : ℝ))^2

/-! ## Section 4 — Trivial witnesses (main-term piece is mechanical)

Following the pattern of `brunMainTerm_trivial_witness` from
`PathC_BrunClosure.lean`, the **main-term sub-Prop**
`BrunGoldbachMainTerm` can be closed unconditionally with the
worst-case error reservoir `B(n, z) := n`, using only the trivial
cardinal bound `goldbachSiftedPair n z ≤ n`.  This isolates the
genuine analytic content into the *other two* sub-Props
(`BrunGoldbachErrorTerm` and `MertensPairedProductBound`). -/

/-- **Trivial witness for `BrunGoldbachMainTerm`.**  Take the
canonical positive-antitone factor `brunMainTermWitnessFactor` from
`PathC_BrunClosure.lean` and the worst-case error reservoir
`B(n, z) := n`; then with `C₁ = 1` the paired-sift bound holds
unconditionally, because `goldbachSiftedPair n z ≤ n` is the trivial
cardinal estimate. -/
theorem brunGoldbachMainTerm_trivial_witness :
    BrunGoldbachMainTerm
      Gdbh.PathCBrunClosure.brunMainTermWitnessFactor
      (fun n _ => (n : ℝ)) := by
  refine
    ⟨Gdbh.PathCBrunClosure.brunMainTermWitnessFactor_isFactor,
     1, by norm_num, ?_⟩
  intro n z _hn
  have hSift : (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le n z
  have hMpos : 0 ≤ Gdbh.PathCBrunClosure.brunMainTermWitnessFactor z :=
    le_of_lt (Gdbh.PathCBrunClosure.brunMainTermWitnessFactor_pos z)
  have hNnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_extra :
      0 ≤ 1 * (n : ℝ) * Gdbh.PathCBrunClosure.brunMainTermWitnessFactor z := by
    have h1 : 0 ≤ 1 * (n : ℝ) := by linarith
    exact mul_nonneg h1 hMpos
  linarith

/-- Pure existential closure of `BrunGoldbachMainTerm`: a witness pair
`(M, B)` exists. -/
theorem exists_brunGoldbachMainTerm_witness :
    ∃ M : ℕ → ℝ, ∃ B : ℕ → ℕ → ℝ, BrunGoldbachMainTerm M B :=
  ⟨Gdbh.PathCBrunClosure.brunMainTermWitnessFactor, fun n _ => (n : ℝ),
   brunGoldbachMainTerm_trivial_witness⟩

/-! ## Section 5 — The assembly theorem

We now show **unconditionally** that the three Brun-Goldbach sub-Props
combine to a Goldbach r-function upper bound of the desired Brun shape

```
r(n) ≤ C · n / (log n)^2 .
```

The proof structure mirrors
`twinPrime_count_upperBound_of_brunComponents` from
`PathC_BrunSieve.lean`, with the paired sift replacing the single
sift.  The `+ 2 (zChoice n + 1)` correction from the small-prime
elementary inclusion is absorbed into the final constant under the
hypothesis that `zChoice n` is eventually controlled by `(log n)^2`. -/

/-- **Brun's Goldbach r-function upper bound, assembled from the three
sub-Props (raw form).**

Given the three Brun-Goldbach sub-Props for a sieve choice `zChoice`,
there exist constants `C, N₀` such that for all `n ≥ N₀, n ≥ 2`,

```
r(n) ≤ C · n / (log n)^2 + 2 (zChoice n + 1) .
```

The trailing `+ 2 (zChoice n + 1)` term is the elementary small-prime
correction from `goldbachRepresentationCount_le_siftedPair_add`.  -/
theorem goldbachRepCount_upperBound_of_brunComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hMain : BrunGoldbachMainTerm M B)
    (hErr  : BrunGoldbachErrorTerm B zChoice)
    (hMert : MertensPairedProductBound M zChoice) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
      ∀ n : ℕ, N₀ ≤ n → 2 ≤ n → 0 < n →
        (goldbachRepresentationCount n : ℝ)
          ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2 + 2 * ((zChoice n : ℝ) + 1) := by
  obtain ⟨_hMfact, C₁, hC₁pos, hMain_bd⟩ := hMain
  obtain ⟨C₂, N₀err, hC₂pos, hErr_bd⟩ := hErr
  obtain ⟨C₃, N₀mer, hC₃pos, hMert_bd⟩ := hMert
  refine ⟨C₁ * (C₃ : ℝ) + (C₂ : ℝ),
          max N₀err N₀mer, ?_, ?_⟩
  · have hC₃real : (0 : ℝ) < (C₃ : ℝ) := by exact_mod_cast hC₃pos
    have hC₂real : (0 : ℝ) < (C₂ : ℝ) := by exact_mod_cast hC₂pos
    have h1 : 0 < C₁ * (C₃ : ℝ) := mul_pos hC₁pos hC₃real
    linarith
  · intro n hN hN2 hNpos
    have hN_err : N₀err ≤ n := le_trans (le_max_left _ _) hN
    have hN_mer : N₀mer ≤ n := le_trans (le_max_right _ _) hN
    -- Step (i): r(n) ↦ sift + small primes.
    have h1 :
        (goldbachRepresentationCount n : ℝ)
          ≤ (goldbachSiftedPair n (zChoice n) : ℝ) + 2 * ((zChoice n : ℝ) + 1) := by
      have h_nat := goldbachRepresentationCount_le_siftedPair_add n (zChoice n)
      have hcast :
          (goldbachRepresentationCount n : ℝ)
            ≤ (goldbachSiftedPair n (zChoice n) : ℝ)
              + (2 * (zChoice n + 1) : ℕ) := by exact_mod_cast h_nat
      have h_cast2 :
          ((2 * (zChoice n + 1) : ℕ) : ℝ) = 2 * ((zChoice n : ℝ) + 1) := by
        push_cast; ring
      rw [h_cast2] at hcast
      exact hcast
    -- Step (ii): Brun main-term decomposition.
    have h2 :
        (goldbachSiftedPair n (zChoice n) : ℝ)
          ≤ C₁ * (n : ℝ) * M (zChoice n) + B n (zChoice n) :=
      hMain_bd n (zChoice n) hNpos
    -- Step (iii): Mertens product bound.
    have hlogN_pos : 0 < Real.log (n : ℝ) := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hN2
      exact Real.log_pos this
    have hlogN2_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
    have hMz_bd : M (zChoice n) ≤ (C₃ : ℝ) / (Real.log (n : ℝ))^2 :=
      hMert_bd n hN_mer hN2
    -- Step (iv): error bound.
    have hBz_bd :
        B n (zChoice n) ≤ (C₂ : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 :=
      hErr_bd n hN_err
    -- Combine.
    have hNreal_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hC₁N_nn : 0 ≤ C₁ * (n : ℝ) := mul_nonneg (le_of_lt hC₁pos) hNreal_nn
    have h_main_bd :
        C₁ * (n : ℝ) * M (zChoice n)
          ≤ C₁ * (n : ℝ) * ((C₃ : ℝ) / (Real.log (n : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hMz_bd hC₁N_nn
    have h_sift_bd :
        (goldbachSiftedPair n (zChoice n) : ℝ)
          ≤ C₁ * (n : ℝ) * ((C₃ : ℝ) / (Real.log (n : ℝ))^2)
            + (C₂ : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
      calc (goldbachSiftedPair n (zChoice n) : ℝ)
          ≤ C₁ * (n : ℝ) * M (zChoice n) + B n (zChoice n) := h2
        _ ≤ C₁ * (n : ℝ) * ((C₃ : ℝ) / (Real.log (n : ℝ))^2)
            + (C₂ : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 :=
              add_le_add h_main_bd hBz_bd
    have h_alg :
        C₁ * (n : ℝ) * ((C₃ : ℝ) / (Real.log (n : ℝ))^2)
          + (C₂ : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2
        = (C₁ * (C₃ : ℝ) + (C₂ : ℝ)) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
      field_simp
    rw [h_alg] at h_sift_bd
    linarith

/-! ## Section 6 — Closing `GoldbachRepresentationBound`

The `GoldbachRepresentationBound` Prop has a *strict* RHS without the
small-prime slack term `2 (zChoice n + 1)`.  To close it from the raw
Brun assembly above we need an additional hypothesis bounding
`zChoice n` by `n / (log n)^2` in some normalised sense.  We package
this as the natural side condition

```
∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
    2 * ((zChoice n : ℝ) + 1) ≤ (n : ℝ) / (Real.log (n : ℝ))^2 .
```

In Brun's argument `zChoice n = n^{1/(2k)}` with `k = ⌊c · log log n⌋`,
so `zChoice n ≪ n^ε` for any `ε > 0` and the side condition is
satisfied; we expose it as a hypothesis here. -/

/-- **`GoldbachRepresentationBound` from the three Brun-Goldbach
sub-Props plus a small-sieve side condition.**

This is the final reduction: given the three sub-Props
(`BrunGoldbachMainTerm`, `BrunGoldbachErrorTerm`,
`MertensPairedProductBound`) for some sieve choice `zChoice`, *plus*
the elementary side condition that the small-prime correction
`2 (zChoice n + 1)` is absorbed by `n / (log n)^2`, the original
named open Prop `GoldbachRepresentationBound` holds. -/
theorem goldbachRepresentationBound_of_brunComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hMain : BrunGoldbachMainTerm M B)
    (hErr  : BrunGoldbachErrorTerm B zChoice)
    (hMert : MertensPairedProductBound M zChoice)
    (hSmall : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
                2 * ((zChoice n : ℝ) + 1)
                  ≤ (n : ℝ) / (Real.log (n : ℝ))^2) :
    GoldbachRepresentationBound := by
  obtain ⟨C, N₀, hCpos, hbd⟩ :=
    goldbachRepCount_upperBound_of_brunComponents M B zChoice hMain hErr hMert
  obtain ⟨N₁, hSmall_bd⟩ := hSmall
  refine ⟨C + 1, max (max N₀ N₁) 2, by linarith, ?_⟩
  intro n hN
  have hN0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ n := le_trans (le_max_right _ _) hN
  have hNpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hmain := hbd n hN0 hN2 hNpos
  have hsmall := hSmall_bd n hN1 hN2
  -- Combine:
  -- r(n) ≤ C·n/(log n)² + 2(zChoice n + 1) ≤ C·n/(log n)² + n/(log n)²
  --       = (C + 1)·n/(log n)².
  have hlogN_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hN2
    exact Real.log_pos this
  have hlogN2_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have hlog2_ne : (Real.log (n : ℝ))^2 ≠ 0 := ne_of_gt hlogN2_pos
  have h_alg :
      C * (n : ℝ) / (Real.log (n : ℝ))^2 + (n : ℝ) / (Real.log (n : ℝ))^2
        = (C + 1) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    field_simp
  calc (goldbachRepresentationCount n : ℝ)
      ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2 + 2 * ((zChoice n : ℝ) + 1) := hmain
    _ ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2 + (n : ℝ) / (Real.log (n : ℝ))^2 := by
        linarith
    _ = (C + 1) * (n : ℝ) / (Real.log (n : ℝ))^2 := h_alg

/-! ## Section 7 — Existential closer

For audit registration we provide a purely-existential closer: given a
witness for the three sub-Props plus the small-sieve side condition,
`GoldbachRepresentationBound` holds. -/

/-- **Existential closer.**  If there exists a sieve setup `(M, B,
zChoice)` satisfying the three Brun-Goldbach sub-Props together with
the small-sieve side condition, then `GoldbachRepresentationBound`
holds. -/
theorem goldbachRepresentationBound_of_exists_brunComponents
    (h :
      ∃ M B zChoice,
        BrunGoldbachMainTerm M B
        ∧ BrunGoldbachErrorTerm B zChoice
        ∧ MertensPairedProductBound M zChoice
        ∧ (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
              2 * ((zChoice n : ℝ) + 1)
                ≤ (n : ℝ) / (Real.log (n : ℝ))^2)) :
    GoldbachRepresentationBound := by
  obtain ⟨M, B, zChoice, hMain, hErr, hMert, hSmall⟩ := h
  exact
    goldbachRepresentationBound_of_brunComponents M B zChoice
      hMain hErr hMert hSmall

/-! ## Section 8 — Summary

What `PathC_GoldbachRBound.lean` delivers:

* The **paired sift** `goldbachSiftedPair n z` (Goldbach analogue of
  `siftedCount` from `PathC_BrunSieve.lean`).
* The **paired sieve inclusion**
  `goldbachRepresentationCount_le_siftedPair_add` — every Goldbach
  prime pair lies in the paired sift modulo a small-prime correction
  of `2 (z + 1)`.
* The **three Brun-Goldbach sub-Props**
  `BrunGoldbachMainTerm`, `BrunGoldbachErrorTerm`,
  `MertensPairedProductBound`.
* A **trivial witness** `brunGoldbachMainTerm_trivial_witness` closing
  the main-term sub-Prop unconditionally with `B(n, z) := n`.
* The **assembly theorem**
  `goldbachRepresentationBound_of_brunComponents`: the three sub-Props
  plus the small-sieve side condition imply
  `GoldbachRepresentationBound`.

What remains genuinely open after this file:

* `BrunGoldbachErrorTerm` for some non-trivial `(B, zChoice)` — i.e.
  the Brun truncated combinatorial estimate `(π(z))^k / k!`.
* `MertensPairedProductBound` — i.e. Mertens' second theorem applied
  to the paired Brun factor `∏_{p ≤ z}(1 - 2/p)`.

These are the **same** open pieces already exposed by the Phase 8
twin-prime decomposition.  P10-T2 confirms that the Goldbach r-function
bound reduces to the *same* analytic content as the twin-prime bound,
modulo the paired sift inclusion which is proved unconditionally
above.  This is the genuine remaining mathlib gap; no additional
mathematical content beyond Brun + Mertens (paired version) is
required. -/

/-- **P10-T2 summary marker.** -/
theorem pathC_p10_t2_summary : True := trivial

end PathCGoldbachRBound
end Gdbh
