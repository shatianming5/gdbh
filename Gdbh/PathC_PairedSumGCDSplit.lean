/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P26-T1 (Phase 26 / Path C — Paired sum rearrangement with
        gcd split: split the truncated double Bonferroni sum by the
        prime divisibility of `n`, for the HL §3.11 master form.)
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Path C — P26-T1: Paired sum rearrangement with gcd split

After the paired Bonferroni indicator + CRT counting steps, the paired
sieve double sum has the form

```
∑_{d₁ ⊆ P, |d₁| ≤ k}  ∑_{d₂ ⊆ P, |d₂| ≤ k}
    μ(d₁.prod) · μ(d₂.prod) · #{m ∈ [1, n-1] : d₁.prod ∣ m ∧ d₂.prod ∣ (n-m)} .
```

For the Hardy–Littlewood §3.11 master expansion, this double sum must be
**rearranged** by splitting each divisor variable according to whether
its primes divide `n` or not.

## The gcd split

Given a finset `P` of primes and a target `n`, define

* `P_n := P.filter (· ∣ n)`   — primes in `P` that divide `n`;
* `P_∁ := P.filter (¬ · ∣ n)` — primes in `P` that do not divide `n`.

Then `P` is the disjoint union of `P_n` and `P_∁`, and every subset
`d ⊆ P` decomposes **uniquely** as

```
d = (d ∩ P_n) ⊔ (d ∩ P_∁) = a ∪ b,
```

with `a ⊆ P_n`, `b ⊆ P_∁`, and `Disjoint a b`.  This pairs the
powerset of `P` bijectively with `P_n.powerset × P_∁.powerset`.

## Main deliverable

`pairedSum_split_by_gcd`: the truncated paired double sum equals a
quadruple sum over `(a₁, b₁, a₂, b₂)` with `aᵢ ⊆ P_n` and `bᵢ ⊆ P_∁`,
where the inner counting bracket depends only on the unions
`dᵢ := aᵢ ∪ bᵢ`.

The rearrangement is **purely Finset combinatorics** — it does not use
any number-theoretic fact about the primes in `P` or about `n`; only
the fact that the powerset of a disjoint union of finsets is bijective
to the Cartesian product of the powersets.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Only `Classical.choice`, `Quot.sound`, `propext`.

## Axiom budget

The closure relies on Finset/`Decidable` boilerplate; the axioms used
are exactly `Classical.choice`, `Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCPairedSumGCDSplit

open scoped BigOperators
open Finset

/-! ## Section 1 — The split structure on `P` by `· ∣ n`.

Define the two pieces `P_n` and `P_∁` and prove they form a disjoint
partition of `P`. -/

/-- The "dividing-`n`" primes in `P`. -/
def primesDvdN (P : Finset ℕ) (n : ℕ) : Finset ℕ := P.filter (fun p => p ∣ n)

/-- The "non-dividing-`n`" primes in `P`. -/
def primesNotDvdN (P : Finset ℕ) (n : ℕ) : Finset ℕ := P.filter (fun p => ¬ p ∣ n)

/-- `primesDvdN P n` and `primesNotDvdN P n` are disjoint. -/
lemma disjoint_primesDvdN_primesNotDvdN (P : Finset ℕ) (n : ℕ) :
    Disjoint (primesDvdN P n) (primesNotDvdN P n) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hp1 hp2
  have h1 := (Finset.mem_filter.mp hp1).2
  have h2 := (Finset.mem_filter.mp hp2).2
  exact h2 h1

/-- The union of `primesDvdN P n` and `primesNotDvdN P n` is `P`. -/
lemma union_primesDvdN_primesNotDvdN (P : Finset ℕ) (n : ℕ) :
    primesDvdN P n ∪ primesNotDvdN P n = P := by
  classical
  ext p
  simp only [primesDvdN, primesNotDvdN, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hpn : p ∣ n
    · exact Or.inl ⟨hp, hpn⟩
    · exact Or.inr ⟨hp, hpn⟩

/-! ## Section 2 — The combinatorial powerset bijection.

For two disjoint finsets `A` and `B`, the powerset of `A ∪ B` is in
bijection with `A.powerset ×ˢ B.powerset` via `d ↦ (d ∩ A, d ∩ B)`,
inverse `(a, b) ↦ a ∪ b`. -/

/-- Powerset sum identity for a disjoint union: any sum over the
powerset of `A ∪ B` (where `A` and `B` are disjoint) equals the double
sum over `(a, b) ∈ A.powerset × B.powerset` of the same function on
`a ∪ b`. -/
lemma sum_powerset_disjoint_union {R : Type*} [AddCommMonoid R]
    (A B : Finset ℕ) (hAB : Disjoint A B) (f : Finset ℕ → R) :
    ∑ d ∈ (A ∪ B).powerset, f d
      = ∑ a ∈ A.powerset, ∑ b ∈ B.powerset, f (a ∪ b) := by
  classical
  -- Bijection : `(A ∪ B).powerset ≃ A.powerset ×ˢ B.powerset`,
  -- `d ↦ (d ∩ A, d ∩ B)`, inverse `(a, b) ↦ a ∪ b`.
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun d => (d ∩ A, d ∩ B))
    (j := fun p => p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  -- (1) i sends powerset into product.
  · intro d hd
    have hdAB : d ⊆ A ∪ B := Finset.mem_powerset.mp hd
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.inter_subset_right)
    · exact Finset.mem_powerset.mpr (Finset.inter_subset_right)
  -- (2) j sends product into powerset.
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have haA : p.1 ⊆ A := Finset.mem_powerset.mp ha
    have hbB : p.2 ⊆ B := Finset.mem_powerset.mp hb
    exact Finset.mem_powerset.mpr (Finset.union_subset
      (haA.trans Finset.subset_union_left)
      (hbB.trans Finset.subset_union_right))
  -- (3) j ∘ i = id on powerset : `(d ∩ A) ∪ (d ∩ B) = d`.
  · intro d hd
    have hdAB : d ⊆ A ∪ B := Finset.mem_powerset.mp hd
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hxd, _⟩ | ⟨hxd, _⟩) <;> exact hxd
    · intro hxd
      rcases Finset.mem_union.mp (hdAB hxd) with hxA | hxB
      · exact Or.inl ⟨hxd, hxA⟩
      · exact Or.inr ⟨hxd, hxB⟩
  -- (4) i ∘ j = id on product : `((a ∪ b) ∩ A, (a ∪ b) ∩ B) = (a, b)`.
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have haA : p.1 ⊆ A := Finset.mem_powerset.mp ha
    have hbB : p.2 ⊆ B := Finset.mem_powerset.mp hb
    -- `(a ∪ b) ∩ A = a` since `a ⊆ A` and `b ∩ A = ∅` (disjoint).
    have h1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h1' | h2', hxA⟩
        · exact h1'
        · -- x ∈ p.2 ⊆ B, x ∈ A, but A, B disjoint.
          have hxB : x ∈ B := hbB h2'
          exact absurd hxA (Finset.disjoint_right.mp hAB hxB)
      · intro hxa
        exact ⟨Or.inl hxa, haA hxa⟩
    -- `(a ∪ b) ∩ B = b`.
    have h2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h1' | h2', hxB⟩
        · -- x ∈ p.1 ⊆ A, x ∈ B, contradiction.
          have hxA : x ∈ A := haA h1'
          exact absurd hxB (Finset.disjoint_left.mp hAB hxA)
        · exact h2'
      · intro hxb
        exact ⟨Or.inr hxb, hbB hxb⟩
    -- Show pair equality.
    apply Prod.ext
    · exact h1
    · exact h2
  -- (5) f-pointwise equality: f d = f ((d ∩ A) ∪ (d ∩ B)).
  · intro d hd
    have hdAB : d ⊆ A ∪ B := Finset.mem_powerset.mp hd
    have hunion : (d ∩ A) ∪ (d ∩ B) = d := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hxd, _⟩ | ⟨hxd, _⟩) <;> exact hxd
      · intro hxd
        rcases Finset.mem_union.mp (hdAB hxd) with hxA | hxB
        · exact Or.inl ⟨hxd, hxA⟩
        · exact Or.inr ⟨hxd, hxB⟩
    -- Goal: `f d = f ((d ∩ A) ∪ (d ∩ B))`, which follows from `hunion`.
    rw [hunion]

/-! ## Section 3 — Truncated powerset bijection.

The truncation `|d| ≤ k` on `d ⊆ A ∪ B` (with `A` and `B` disjoint)
corresponds to the constraint `|a| + |b| ≤ k` on `(a, b)`, since
`|a ∪ b| = |a| + |b|` when `Disjoint a b`. -/

/-- Truncated version: the sum over `d ⊆ P` with `|d| ≤ k` of `f d`
equals the sum over `(a, b) ∈ P_n.powerset × P_∁.powerset` with
`|a| + |b| ≤ k` of `f (a ∪ b)`.

Here `P_n := primesDvdN P n` and `P_∁ := primesNotDvdN P n`. -/
lemma sum_truncated_powerset_split {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (n k : ℕ) (f : Finset ℕ → R) :
    ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), f d
      = ∑ a ∈ (primesDvdN P n).powerset,
          ∑ b ∈ (primesNotDvdN P n).powerset.filter
                  (fun b => a.card + b.card ≤ k),
            f (a ∪ b) := by
  classical
  -- Rewrite `P = P_n ∪ P_∁` (disjoint).
  set A := primesDvdN P n with hA_def
  set B := primesNotDvdN P n with hB_def
  have hAB : Disjoint A B := disjoint_primesDvdN_primesNotDvdN P n
  have hUnion : A ∪ B = P := union_primesDvdN_primesNotDvdN P n
  -- Step 1: rewrite the LHS as a sum over (A ∪ B).powerset using hUnion.
  have hStep1 :
      ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), f d
        = ∑ d ∈ (A ∪ B).powerset.filter (fun d => d.card ≤ k), f d := by
    rw [hUnion]
  rw [hStep1]
  -- Step 2: rewrite the filtered powerset sum as `Finset.sum_filter`.
  rw [Finset.sum_filter]
  -- Step 3: apply the disjoint-union powerset bijection on the indicator.
  rw [sum_powerset_disjoint_union A B hAB
        (fun d => if d.card ≤ k then f d else 0)]
  -- Step 4: for each (a, b) with a ⊆ A, b ⊆ B (so a ∩ b = ∅), we have
  -- |a ∪ b| = a.card + b.card.  Hence the indicator becomes
  -- `if a.card + b.card ≤ k then f (a ∪ b) else 0`.
  refine Finset.sum_congr rfl ?_
  intro a ha
  have haA : a ⊆ A := Finset.mem_powerset.mp ha
  -- The inner `Finset.sum_filter` on b's filter.
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hbB : b ⊆ B := Finset.mem_powerset.mp hb
  -- a, b are disjoint (since A, B are disjoint and a ⊆ A, b ⊆ B).
  have hab : Disjoint a b := Finset.disjoint_of_subset_left haA
                              (Finset.disjoint_of_subset_right hbB hAB)
  -- Hence |a ∪ b| = a.card + b.card.
  have hcard : (a ∪ b).card = a.card + b.card := Finset.card_union_of_disjoint hab
  rw [hcard]

/-! ## Section 4 — Main theorem: paired sum split by gcd.

We apply the split to both `d₁` and `d₂` in the paired Bonferroni
double sum and obtain a quadruple sum over `(a₁, b₁, a₂, b₂)`. -/

/-- **Paired sum split by gcd.**

For a finset `P` of primes, a truncation depth `k`, and a target `n`,
the truncated paired Bonferroni double sum

```
∑_{d₁ ⊆ P, |d₁| ≤ k}  ∑_{d₂ ⊆ P, |d₂| ≤ k}
    μ(d₁.prod) · μ(d₂.prod) · #{m ∈ [1, n-1] : d₁.prod ∣ m ∧ d₂.prod ∣ (n-m)}
```

equals the quadruple sum over `(a₁, b₁, a₂, b₂)` with `aᵢ ⊆ P_n` and
`bᵢ ⊆ P_∁` (where `P_n := P.filter (· ∣ n)` and
`P_∁ := P.filter (¬ · ∣ n)`), subject to the truncation
`aᵢ.card + bᵢ.card ≤ k`, of

```
μ((a₁ ∪ b₁).prod) · μ((a₂ ∪ b₂).prod) ·
   #{m ∈ [1, n-1] : (a₁ ∪ b₁).prod ∣ m ∧ (a₂ ∪ b₂).prod ∣ (n-m)} .
```

This is the gcd-split rearrangement for HL §3.11.

The proof is **purely Finset combinatorics** — no number-theoretic fact
about the primes in `P` is used beyond the disjoint partition
`P = P_n ⊔ P_∁`.  In particular, the hypothesis `hP : ∀ p ∈ P, Nat.Prime p`
is *unused* in the rearrangement (we keep it in the signature to match
the upstream context). -/
theorem pairedSum_split_by_gcd
    (P : Finset ℕ) (n k : ℕ)
    (_hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
        (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
          (((Finset.Icc 1 (n - 1)).filter
            (fun m => (d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m))).card : ℝ))
      = ∑ a₁ ∈ (primesDvdN P n).powerset,
          ∑ b₁ ∈ (primesNotDvdN P n).powerset.filter
                  (fun b => a₁.card + b.card ≤ k),
            ∑ a₂ ∈ (primesDvdN P n).powerset,
              ∑ b₂ ∈ (primesNotDvdN P n).powerset.filter
                      (fun b => a₂.card + b.card ≤ k),
                (ArithmeticFunction.moebius ((a₁ ∪ b₁).prod id) : ℝ) *
                  (ArithmeticFunction.moebius ((a₂ ∪ b₂).prod id) : ℝ) *
                  (((Finset.Icc 1 (n - 1)).filter
                    (fun m => ((a₁ ∪ b₁).prod id) ∣ m ∧
                              ((a₂ ∪ b₂).prod id) ∣ (n - m))).card : ℝ) := by
  classical
  -- Apply `sum_truncated_powerset_split` to the outer d₁ sum.
  -- The inner sum (over d₂) is the "summand" indexed by d₁.
  rw [sum_truncated_powerset_split P n k
        (f := fun d₁ =>
          ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
            (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
              (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
              (((Finset.Icc 1 (n - 1)).filter
                (fun m => (d₁.prod id) ∣ m ∧
                          (d₂.prod id) ∣ (n - m))).card : ℝ))]
  -- Now apply the same split to the inner d₂ sum.
  refine Finset.sum_congr rfl ?_
  intro a₁ _ha₁
  refine Finset.sum_congr rfl ?_
  intro b₁ _hb₁
  exact sum_truncated_powerset_split P n k
    (f := fun d₂ =>
      (ArithmeticFunction.moebius ((a₁ ∪ b₁).prod id) : ℝ) *
        (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        (((Finset.Icc 1 (n - 1)).filter
          (fun m => ((a₁ ∪ b₁).prod id) ∣ m ∧
                    (d₂.prod id) ∣ (n - m))).card : ℝ))

end PathCPairedSumGCDSplit
end Gdbh

/-! ### Axiom audit -/

#print axioms Gdbh.PathCPairedSumGCDSplit.pairedSum_split_by_gcd
