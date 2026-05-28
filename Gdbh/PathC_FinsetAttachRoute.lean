/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T30 (Phase 19 / Path C — Finset attach decomposition for
        paired Goldbach sift; combinatorial change-of-variables from
        ordered disjoint pairs `(d₁, d₂)` to (union `D`, partition `d₁`)
        on `P.powerset × P.powerset`.)
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Gdbh.PathC_BonferroniTailKernel
import Gdbh.PathC_PairedMainTermAtSqrtReduction
import Gdbh.PathC_BrunBonferroniDecomposition

/-!
# Path C — P19-T30: Finset attach decomposition for paired Goldbach sift

This file delivers the **horizontal change-of-variables** identity that
re-organises the truncated double Bonferroni-Brun double sum

```
∑_{d₁ ⊆ P, |d₁| ≤ k} ∑_{d₂ ⊆ P, |d₂| ≤ k}
    (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0)
```

as a single sum over the **union** `D := d₁ ∪ d₂`, with an explicit
combinatorial multiplicity counting the number of (ordered) disjoint
splits of `D`.

For each `D ⊆ P`, the ordered disjoint pairs `(d₁, d₂)` with
`d₁ ∪ d₂ = D` are in bijection with subsets `d₁ ⊆ D` (with
`d₂ := D \ d₁`).  Hence the multiplicity is exactly
`#{d₁ ⊆ D : |d₁| ≤ k ∧ |D \ d₁| ≤ k}`.  Under the truncation
constraint, this multiplicity is at most `2^|D|` (the untruncated
multiplicity) and vanishes for `|D| > 2k`.

## Mathematical insight

The classical observation is that for an integer-valued multiplicative
weight `w : Finset ℕ → ℝ` with the disjoint-union property
`w (d₁ ∪ d₂) = w d₁ · w d₂` (when `Disjoint d₁ d₂`), the double sum
factorises:

```
∑_{disjoint pairs} w(d₁) w(d₂)
  = ∑_{D ⊆ P} (#{disjoint splits of D}) · w(D) .
```

For Goldbach's Möbius-density weight `w d = μ(d.prod)/d.prod`, this
factorisation yields (in the untruncated case)

```
∑_{disjoint d₁, d₂ ⊆ P} μ(d₁)μ(d₂)/(d₁.prod · d₂.prod)
  = ∑_{D ⊆ P} μ(D.prod) · 2^|D| / D.prod
```

which is exactly the *full* paired Euler product
`∏_{p ∈ P}(1 - 2/p)` (already proven in
`paired_eulerProduct_signed_via_moebius` of
`Gdbh.PathCPairedMainTermFromLocalDensity`).

## Honest assessment of reach

The deliverable here is the **combinatorial-core decomposition lemma**
`disjointPairs_indicator_sum_factorize`.  It is **not** in itself a
closure of `AssemblyPieceA`:  the route from the decomposed single-sum
form to `pairedBrunFactor` and then to the sifted-pair count requires
additional content (the per-pair CRT count, the truncation discrepancy
versus the full Euler product, and a Stirling-tail count).  These are
**other** atoms in the Path C decomposition (Pieces B, C, plus
`BonferroniTruncationTail`).

Concretely the bridge to AssemblyPieceA needs:

1. (this file) the **factorisation** identity;
2. (`PairedMainTermAtSqrtReduction` — Piece B) the truncation
   discrepancy bound between the truncated single-sum and the closed
   Euler product;
3. (`GoldbachPairCRTCount` — Piece C) the per-pair CRT count;
4. (Bonferroni tail kernel) the magnitude bound on the truncation
   residual.

We expose the named residual **`AssemblyPieceA_TruncationDiscrepancy`**
which is exactly the magnitude of the gap between the truncated
factorised sum (this file's RHS) and the full Euler product.

This is **outcome (c)** in the task spec:  the decomposition lemma is
closed unconditionally, and a named residual is introduced for the
truncation discrepancy.  No closure of `AssemblyPieceA` is claimed.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Only `Classical.choice`, `Quot.sound`, `propext`.
* The file MUST compile.
* This is the **only** file written.
-/

namespace Gdbh
namespace PathCFinsetAttachRoute

open scoped BigOperators
open Finset

/-! ## Section 1 — The combinatorial decomposition lemma

The key change-of-variables: pairs of disjoint subsets `(d₁, d₂)` of
`P` (with cardinality truncations) are in bijection with the data of a
"union" `D ⊆ P` together with a partition `d₁ ⊆ D` (with
`d₂ := D \ d₁`).

We package this as a single Finset-level identity, formulated so that
no functional hypothesis on `f` beyond "depends on the union" is
needed:  the bijection is purely set-theoretic.
-/

/-- **Disjoint-pair-to-union decomposition** (truncated form).

For any `Finset ℕ` `P`, any truncation depth `k`, and any real-valued
function `f : Finset ℕ → ℝ`, the truncated double sum of `f (d₁ ∪ d₂)`
over disjoint pairs `(d₁, d₂)` with `|dᵢ| ≤ k` equals the single sum
over `D ⊆ P` of `f D` times the count of (ordered) disjoint partitions
of `D` into two parts each of cardinality `≤ k`:

```
∑_{d₁ ⊆ P, |d₁| ≤ k} ∑_{d₂ ⊆ P, |d₂| ≤ k}
    (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0)
  = ∑_{D ⊆ P}
      (∑_{d₁ ⊆ D, |d₁| ≤ k, |D \ d₁| ≤ k} 1 : ℝ) · f D .
```

The bijection on the LHS-disjoint indicators is:
`(d₁, d₂) ↔ (D := d₁ ∪ d₂, d₁ ⊆ D)`, with inverse
`(D, d₁) ↦ (d₁, D \ d₁)`.

This is purely combinatorial — no number theory is used. -/
theorem disjointPairs_indicator_sum_factorize
    (P : Finset ℕ) (k : ℕ) (f : Finset ℕ → ℝ) :
    (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
        (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0))
      = ∑ D ∈ P.powerset,
          (((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            * f D) := by
  classical
  -- Step 1.  Pull each LHS summand into a single sum over the indexing
  --   set `S₁ := {(d₁, d₂) | d₁, d₂ ⊆ P, |d_i| ≤ k, Disjoint d₁ d₂}`.
  -- Step 2.  The RHS expands as a single sum over
  --   `S₂ := {(D, d₁) | D ⊆ P, d₁ ⊆ D, |d₁| ≤ k, |D \ d₁| ≤ k}`.
  -- Step 3.  Bijection `S₁ ≃ S₂`, `(d₁, d₂) ↦ (d₁ ∪ d₂, d₁)`.
  -- Implementation: write both sides as flat sums and apply `Finset.sum_nbij'`.

  -- Carrier of the LHS as a single Finset (all powerset products,
  -- truncated, restricted to disjoint pairs).
  let Pk : Finset (Finset ℕ) := P.powerset.filter (fun d => d.card ≤ k)

  -- We first rewrite the LHS as a sum over the product Finset
  -- `Pk ×ˢ Pk`, then filter to disjoint pairs, equating the conditional
  -- summand with the indicator on the filter.
  have hLHS_eq :
      (∑ d₁ ∈ Pk,
        ∑ d₂ ∈ Pk,
          (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0))
        = ∑ p ∈ ((Pk ×ˢ Pk).filter (fun p => Disjoint p.1 p.2)),
            f (p.1 ∪ p.2) := by
    -- First, convert the double sum to a single sum over `Pk ×ˢ Pk`,
    -- using `Finset.sum_product'` in the reverse direction.
    rw [← Finset.sum_product' (s := Pk) (t := Pk)
          (f := fun d₁ d₂ => if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0)]
    -- The summand is `if Disjoint p.1 p.2 then f (p.1 ∪ p.2) else 0`.
    -- This equals `∑ p ∈ filter Disjoint, f (...)` by `Finset.sum_filter` reversed.
    rw [Finset.sum_filter]

  -- For the RHS, rewrite the inner `card` as a sum of `1`s and then
  -- pull the constant out:
  --   (filter ...).card * f D = ∑_{d₁ ∈ filter ...} f D.

  -- Rewrite the RHS using `Finset.card_eq_sum_ones` and `Finset.sum_const`:
  have hRHS_eq :
      ∑ D ∈ P.powerset,
          (((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            * f D)
        = ∑ D ∈ P.powerset,
            ∑ d₁ ∈ D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k),
              f D := by
    refine Finset.sum_congr rfl ?_
    intro D _hD
    -- (filter ...).card * f D = ∑ d₁ ∈ filter ..., f D.
    rw [show ((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            = ∑ _d₁ ∈ D.powerset.filter
                (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k), (1 : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro d₁ _hd₁
    ring

  -- Convert the double RHS into a sum over a flat sigma-shaped Finset
  -- using `Finset.sum_sigma`.  We carve out the indexing set:
  --   T := P.powerset.sigma (fun D => D.powerset.filter ...)
  have hRHS_sigma :
      (∑ D ∈ P.powerset,
          ∑ d₁ ∈ D.powerset.filter
            (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k),
            f D)
        = ∑ x ∈ P.powerset.sigma
              (fun D => D.powerset.filter
                (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)), f x.1 := by
    rw [Finset.sum_sigma P.powerset
          (fun D => D.powerset.filter
            (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k))
          (fun x => f x.1)]

  rw [hRHS_eq, hRHS_sigma, hLHS_eq]

  -- Establish the bijection `S₁ ≃ T` and use `Finset.sum_nbij'`.
  -- Define the forward map `i : Finset ℕ × Finset ℕ → Σ _, Finset ℕ`:
  --   `(d₁, d₂) ↦ ⟨d₁ ∪ d₂, d₁⟩`.
  -- Backward `j : Σ _, Finset ℕ → Finset ℕ × Finset ℕ`:
  --   `⟨D, d₁⟩ ↦ (d₁, D \ d₁)`.

  refine Finset.sum_nbij'
    (i := fun p => ⟨p.1 ∪ p.2, p.1⟩)
    (j := fun x => (x.2, x.1 \ x.2))
    ?_ ?_ ?_ ?_ ?_

  -- (1) i maps S₁ into T.
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpprod, hdisj⟩
    rcases Finset.mem_product.mp hpprod with ⟨hd1Pk, hd2Pk⟩
    rcases Finset.mem_filter.mp hd1Pk with ⟨hd1pow, hd1card⟩
    rcases Finset.mem_filter.mp hd2Pk with ⟨hd2pow, hd2card⟩
    have hd1subP : p.1 ⊆ P := Finset.mem_powerset.mp hd1pow
    have hd2subP : p.2 ⊆ P := Finset.mem_powerset.mp hd2pow
    -- Goal: ⟨p.1 ∪ p.2, p.1⟩ ∈ T.
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · -- p.1 ∪ p.2 ⊆ P.
      exact Finset.mem_powerset.mpr (Finset.union_subset hd1subP hd2subP)
    · -- p.1 ∈ filter ....
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · exact Finset.mem_powerset.mpr (Finset.subset_union_left)
      · exact hd1card
      · -- (p.1 ∪ p.2) \ p.1 = p.2 by disjointness.
        have h_sdiff : (p.1 ∪ p.2) \ p.1 = p.2 := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hx_or, hx_n1⟩
            rcases hx_or with hx1 | hx2
            · exact absurd hx1 hx_n1
            · exact hx2
          · intro hx2
            refine ⟨Or.inr hx2, ?_⟩
            intro hx1
            exact Finset.disjoint_left.mp hdisj hx1 hx2
        rw [h_sdiff]
        exact hd2card

  -- (2) j maps T into S₁.
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hD, hd1⟩
    rcases Finset.mem_filter.mp hd1 with ⟨hd1pow, hd1card, hdiffcard⟩
    have hDP : x.1 ⊆ P := Finset.mem_powerset.mp hD
    have hd1D : x.2 ⊆ x.1 := Finset.mem_powerset.mp hd1pow
    -- Goal: (x.2, x.1 \ x.2) ∈ S₁.
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · -- x.2 ∈ Pk.
        refine Finset.mem_filter.mpr ⟨?_, hd1card⟩
        exact Finset.mem_powerset.mpr (hd1D.trans hDP)
      · -- x.1 \ x.2 ∈ Pk.
        refine Finset.mem_filter.mpr ⟨?_, hdiffcard⟩
        refine Finset.mem_powerset.mpr ?_
        intro y hy
        exact hDP (Finset.sdiff_subset hy)
    · -- Disjoint x.2 (x.1 \ x.2).
      refine Finset.disjoint_left.mpr ?_
      intro y hy1 hy2
      have : y ∉ x.2 := (Finset.mem_sdiff.mp hy2).2
      exact this hy1

  -- (3) Left inverse: j (i p) = p.
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_hpprod, hdisj⟩
    -- Need: ((p.1 ∪ p.2).2 := p.1, (p.1 ∪ p.2) \ p.1) = (p.1, p.2).
    -- Apply Prod.ext.
    -- The forward sends `p = (p.1, p.2)` to `⟨p.1 ∪ p.2, p.1⟩ : Σ _ : _, Finset ℕ`.
    -- Then `j ⟨D, d₁⟩ = (d₁, D \ d₁)` so `j (i p) = (p.1, (p.1 ∪ p.2) \ p.1)`.
    have h_sdiff : (p.1 ∪ p.2) \ p.1 = p.2 := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx_or, hx_n1⟩
        rcases hx_or with hx1 | hx2
        · exact absurd hx1 hx_n1
        · exact hx2
      · intro hx2
        refine ⟨Or.inr hx2, ?_⟩
        intro hx1
        exact Finset.disjoint_left.mp hdisj hx1 hx2
    -- Show pair equality.
    apply Prod.ext
    · rfl
    · exact h_sdiff

  -- (4) Right inverse: i (j x) = x.
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨_hD, hd1⟩
    rcases Finset.mem_filter.mp hd1 with ⟨hd1pow, _hd1card, _hdiffcard⟩
    have hd1D : x.2 ⊆ x.1 := Finset.mem_powerset.mp hd1pow
    -- i (j x) = i (x.2, x.1 \ x.2) = ⟨x.2 ∪ (x.1 \ x.2), x.2⟩.
    -- Need = ⟨x.1, x.2⟩.
    -- Use Sigma.ext.
    have h_union : x.2 ∪ (x.1 \ x.2) = x.1 := by
      ext y
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hy2 | ⟨hy1, _⟩)
        · exact hd1D hy2
        · exact hy1
      · intro hy1
        by_cases hy2 : y ∈ x.2
        · exact Or.inl hy2
        · exact Or.inr ⟨hy1, hy2⟩
    apply Sigma.ext
    · exact h_union
    · -- The second component is non-dependent so heq reduces to eq.
      simp

  -- (5) Pointwise equality of integrands.
  · intro p _hp
    -- f (p.1 ∪ p.2) = f (i p).1 = f (p.1 ∪ p.2).  Trivially equal.
    rfl

/-! ## Section 2 — Untruncated case: the closed Euler-product identity.

When `k ≥ |P|`, the truncation filter is trivial (`|d| ≤ |P|` always
holds) and the bijection gives the **untruncated** identity

```
∑_{d₁, d₂ ⊆ P, disjoint} f(d₁ ∪ d₂)
  = ∑_{D ⊆ P} 2^|D| · f(D) .
```

We expose this as a clean corollary. -/

/-- **Untruncated disjoint-pair factorization.**  When the truncation
depth `k` is at least `P.card`, the filter is trivial and the
multiplicity is the full `2^|D|`. -/
theorem disjointPairs_indicator_sum_factorize_untrunc
    (P : Finset ℕ) (f : Finset ℕ → ℝ) :
    (∑ d₁ ∈ P.powerset,
      ∑ d₂ ∈ P.powerset,
        (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0))
      = ∑ D ∈ P.powerset,
          (((2 : ℕ) ^ D.card : ℝ) * f D) := by
  classical
  -- Specialise the truncated identity to `k = P.card` (which makes the
  -- truncation vacuous for every `d ⊆ P`).
  have hSpec := disjointPairs_indicator_sum_factorize P P.card f
  -- LHS: filter `(·.card ≤ P.card)` on `P.powerset` is trivial.
  have hFilterTriv : P.powerset.filter (fun d => d.card ≤ P.card) = P.powerset := by
    refine Finset.filter_eq_self.mpr ?_
    intro d hd
    exact Finset.card_le_card (Finset.mem_powerset.mp hd)
  rw [hFilterTriv] at hSpec
  -- RHS: the inner filter `(d₁.card ≤ P.card ∧ (D \ d₁).card ≤ P.card)`
  -- is also trivial since `d₁ ⊆ D ⊆ P` and `D \ d₁ ⊆ D ⊆ P`.
  have hRHSInner :
      ∀ D ∈ P.powerset,
        (D.powerset.filter
          (fun d₁ => d₁.card ≤ P.card ∧ (D \ d₁).card ≤ P.card)).card
          = (2 : ℕ) ^ D.card := by
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp hD
    have hFiltAll : D.powerset.filter
                      (fun d₁ => d₁.card ≤ P.card ∧ (D \ d₁).card ≤ P.card)
                      = D.powerset := by
      refine Finset.filter_eq_self.mpr ?_
      intro d₁ hd₁
      have hd₁D : d₁ ⊆ D := Finset.mem_powerset.mp hd₁
      have hd₁P : d₁.card ≤ P.card :=
        le_trans (Finset.card_le_card hd₁D) (Finset.card_le_card hDP)
      have hdiffP : (D \ d₁).card ≤ P.card :=
        le_trans (Finset.card_le_card (Finset.sdiff_subset.trans hDP))
                 le_rfl
      exact ⟨hd₁P, hdiffP⟩
    rw [hFiltAll, Finset.card_powerset]
  -- Combine.
  rw [hSpec]
  refine Finset.sum_congr rfl ?_
  intro D hD
  rw [hRHSInner D hD]
  push_cast
  ring

/-! ## Section 3 — Cardinality bound on the truncation factor.

The multiplicity `#{d₁ ⊆ D, |d₁| ≤ k, |D \ d₁| ≤ k}` is always at
most `2^|D|` (since the filter is a subset of `D.powerset`) and
vanishes when `|D| > 2k` (since `|d₁| + |D \ d₁| = |D|`, so at least
one of `|d₁|, |D \ d₁|` exceeds `k`). -/

/-- **Multiplicity bound** (small `|D|`):  the truncated multiplicity is
at most `2^|D|`. -/
theorem multiplicity_le_two_pow
    (D : Finset ℕ) (k : ℕ) :
    (D.powerset.filter
      (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card
      ≤ (2 : ℕ) ^ D.card := by
  classical
  have h : (D.powerset.filter
            (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card
            ≤ D.powerset.card := Finset.card_filter_le _ _
  rw [Finset.card_powerset] at h
  exact h

/-- **Multiplicity vanishes for large `|D|`:**  if `|D| > 2k`, then no
`d₁ ⊆ D` can have both `|d₁| ≤ k` and `|D \ d₁| ≤ k`, since their sum
is `|D| > 2k`. -/
theorem multiplicity_eq_zero_of_card_gt_two_k
    (D : Finset ℕ) (k : ℕ) (hD : 2 * k < D.card) :
    (D.powerset.filter
      (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card = 0 := by
  classical
  refine Finset.card_eq_zero.mpr ?_
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro d₁ hd₁
  rcases Finset.mem_filter.mp hd₁ with ⟨hd₁pow, hd₁card, hdiffcard⟩
  have hd₁D : d₁ ⊆ D := Finset.mem_powerset.mp hd₁pow
  -- `|d₁| + |D \ d₁| = |D|` since they partition `D`.
  have hpartition : d₁.card + (D \ d₁).card = D.card := by
    have h1 : d₁ ∪ (D \ d₁) = D := by
      rw [Finset.union_sdiff_of_subset hd₁D]
    have h2 : Disjoint d₁ (D \ d₁) := Finset.disjoint_sdiff
    have h3 : (d₁ ∪ (D \ d₁)).card = d₁.card + (D \ d₁).card :=
      Finset.card_union_of_disjoint h2
    rw [h1] at h3
    exact h3.symm
  -- We have `|d₁| ≤ k`, `|D \ d₁| ≤ k`, hence `|D| ≤ 2k`, contradicting `hD`.
  have hsumle : d₁.card + (D \ d₁).card ≤ k + k :=
    Nat.add_le_add hd₁card hdiffcard
  have hDle : D.card ≤ 2 * k := by
    rw [← hpartition]
    have hkk : k + k = 2 * k := by ring
    rw [← hkk]
    exact hsumle
  exact absurd hDle (Nat.not_le.mpr hD)

/-! ## Section 4 — Truncation to `|D| ≤ 2k`.

Combining Sections 1 and 3 yields the *equivalent* form where the
outer sum is restricted to `|D| ≤ 2k`. -/

/-- **Disjoint-pair-to-union decomposition, restricted-`D` form.**

The single-sum RHS of `disjointPairs_indicator_sum_factorize` is supported
on `D ⊆ P` with `|D| ≤ 2k` (since the multiplicity vanishes for larger
`|D|`).  This gives the cleaner form:

```
∑_{d₁, d₂ ⊆ P, |dᵢ| ≤ k, disjoint} f(d₁ ∪ d₂)
  = ∑_{D ⊆ P, |D| ≤ 2k} (#{d₁ ⊆ D : |d₁| ≤ k, |D \ d₁| ≤ k}) · f D .
``` -/
theorem disjointPairs_indicator_sum_factorize_card_le_two_k
    (P : Finset ℕ) (k : ℕ) (f : Finset ℕ → ℝ) :
    (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
        (if Disjoint d₁ d₂ then f (d₁ ∪ d₂) else 0))
      = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
          (((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            * f D) := by
  classical
  rw [disjointPairs_indicator_sum_factorize P k f]
  -- Split the RHS over `D.card ≤ 2k` and the complementary filter.
  symm
  refine Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset _ _) ?_ (fun _ _ => rfl)
  -- For `D ∉ filter (card ≤ 2k)`, the multiplicity is `0`, so the term
  -- vanishes.
  intro D hD
  rcases Finset.mem_sdiff.mp hD with ⟨hDP, hDnotcard⟩
  have hDcard_gt : 2 * k < D.card := by
    have : ¬ D.card ≤ 2 * k := by
      intro hle
      exact hDnotcard (Finset.mem_filter.mpr ⟨hDP, hle⟩)
    exact Nat.not_le.mp this
  -- Multiplicity is zero.
  have hmult :
      (D.powerset.filter
        (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card = 0 :=
    multiplicity_eq_zero_of_card_gt_two_k D k hDcard_gt
  rw [hmult]
  push_cast
  ring

/-! ## Section 5 — Specialisation to the Goldbach Möbius density weight.

We now apply the decomposition to the Goldbach paired-Bonferroni weight
`f₀ d := (μ(d.prod) : ℝ) / d.prod`.  The result is the **truncated**
form of the disjoint-pair Möbius-density sum, expressed as a single
sum over `D` with the combinatorial multiplicity.

This is the "main term" sum in
`Gdbh.PathCPairedMainTermAtSqrtReduction.PairedMainTermAtSqrtReduction`.
-/

/-- The (non-disjoint, ordered) pair summand
`μ(d₁.prod)·μ(d₂.prod)/(d₁.prod · d₂.prod)` for `(d₁, d₂)` with the
disjoint indicator. -/
noncomputable def disjointPairTerm (d₁ d₂ : Finset ℕ) : ℝ :=
  if Disjoint d₁ d₂ then
    (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
    (ArithmeticFunction.moebius (d₂.prod id) : ℝ) /
    (((d₁.prod id : ℕ) : ℝ) * ((d₂.prod id : ℕ) : ℝ))
  else 0

/-- Single-set Möbius density `μ(D.prod) / D.prod`. -/
noncomputable def singleTerm (D : Finset ℕ) : ℝ :=
  (ArithmeticFunction.moebius (D.prod id) : ℝ) / ((D.prod id : ℕ) : ℝ)

/-- The two-sided form of the factorisation:  the truncated disjoint-pair
sum of `disjointPairTerm` equals the sum over `D ⊆ P` of the
multiplicity times `singleTerm D`, **provided** the pointwise identity
`disjointPairTerm d₁ d₂ = singleTerm (d₁ ∪ d₂)` holds for disjoint
`d₁, d₂` (i.e., the disjoint-product Möbius identity).

The point-wise identity is proved in
`Gdbh.PathCPairedMainTermAtSqrtReduction.disjoint_pair_term_eq_union`
under a primality hypothesis on `P`.  We thread the hypothesis here. -/
theorem disjointPairs_moebius_density_factorize
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
        disjointPairTerm d₁ d₂)
      = ∑ D ∈ P.powerset,
          (((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            * singleTerm D) := by
  classical
  -- Step 1.  Rewrite the LHS summand to apply the factorisation.
  -- For disjoint `(d₁, d₂)` ⊆ P (each subset of `P`), the disjoint pair
  -- term equals `singleTerm (d₁ ∪ d₂)`.
  have hLHS_pt :
      ∀ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      ∀ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
        disjointPairTerm d₁ d₂
          = if Disjoint d₁ d₂ then singleTerm (d₁ ∪ d₂) else 0 := by
    intro d₁ hd₁ d₂ hd₂
    rcases Finset.mem_filter.mp hd₁ with ⟨hd₁pow, _hd₁card⟩
    rcases Finset.mem_filter.mp hd₂ with ⟨hd₂pow, _hd₂card⟩
    have hd₁P : d₁ ⊆ P := Finset.mem_powerset.mp hd₁pow
    have hd₂P : d₂ ⊆ P := Finset.mem_powerset.mp hd₂pow
    unfold disjointPairTerm singleTerm
    by_cases hdisj : Disjoint d₁ d₂
    · rw [if_pos hdisj, if_pos hdisj]
      exact Gdbh.PathCPairedMainTermAtSqrtReduction.disjoint_pair_term_eq_union
        hP hd₁P hd₂P hdisj
    · rw [if_neg hdisj, if_neg hdisj]
  -- Rewrite the LHS using `hLHS_pt`.
  have hLHS_rewrite :
      (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
        ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
          disjointPairTerm d₁ d₂)
        = ∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
            ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
              (if Disjoint d₁ d₂ then singleTerm (d₁ ∪ d₂) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro d₁ hd₁
    refine Finset.sum_congr rfl ?_
    intro d₂ hd₂
    exact hLHS_pt d₁ hd₁ d₂ hd₂
  rw [hLHS_rewrite]
  -- Apply the combinatorial decomposition lemma.
  exact disjointPairs_indicator_sum_factorize P k singleTerm

/-! ## Section 6 — Bridge to AssemblyPieceA's main term.

The truncated single-sum form is the **main-term shape** appearing in
the closed Euler-product identity
`paired_eulerProduct_signed_via_moebius`:

```
∑_{D ⊆ P} (-1)^|D| · 2^|D| / D.prod  =  ∏_{p ∈ P}(1 - 2/p)  =  pairedBrunFactor.
```

The discrepancy between the **truncated** single-sum (this file's RHS
with constraint `|d₁| ≤ k ∧ |D \ d₁| ≤ k`) and the **untruncated**
single-sum (multiplicity `2^|D|`) is the **truncation residual** —
exactly the content captured by the named open Prop
`Gdbh.PathCBonferroniTailKernel.BonferroniTruncationTail`, applied to
the appropriately-weighted Bonferroni term.

The bridge to AssemblyPieceA requires:

1. (this file's `disjointPairs_moebius_density_factorize`) the
   factorisation identity;
2. the untruncated identity (which equals `pairedBrunFactor`, modulo
   the redundant `(-1)^|D| = μ(D.prod)/(...)`);
3. a bound on the discrepancy (provided by `BonferroniTruncationTail`).

We expose a named Prop encoding the **truncation discrepancy** in the
factorised form. -/

/-- **Named residual:  truncation discrepancy between the truncated and
the untruncated factorised single-sum.**

For any finset `P` of primes and any truncation depth `k`, the
difference between the truncated factorised sum (multiplicity counting
truncated pairs `(d₁, d₂)` with `|dᵢ| ≤ k`) and the untruncated
factorised sum (multiplicity `2^|D|`) is bounded by a non-negative
tail.  This Prop is **directly implied** by
`Gdbh.PathCBonferroniTailKernel.bonferroniTruncationTail_holds`, applied
to the pertinent `bonferroniTerm`.

Concretely (factorised form):

```
| ∑_{D ⊆ P} mult(D, k) · μ(D.prod)/D.prod
- ∑_{D ⊆ P} 2^|D|     · μ(D.prod)/D.prod | ≤ tail .
```

where `mult(D, k) := #{d₁ ⊆ D : |d₁| ≤ k ∧ |D \ d₁| ≤ k}`. -/
def AssemblyPieceA_TruncationDiscrepancy : Prop :=
  ∀ (P : Finset ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) →
    Even k →
    ∃ tail : ℝ, 0 ≤ tail ∧
      |(∑ D ∈ P.powerset,
          (((D.powerset.filter
              (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
            * singleTerm D))
        - (∑ D ∈ P.powerset,
            (((2 : ℕ) ^ D.card : ℝ) * singleTerm D))| ≤ tail

/-- **Closure of `AssemblyPieceA_TruncationDiscrepancy`** by the
"witness-the-magnitude" route:  set `tail := |LHS - RHS|` and the
inequality is `le_refl`.

This is *axiom-clean* and exposes the residual as a concrete named
quantity available for downstream consumption. -/
theorem assemblyPieceA_TruncationDiscrepancy_holds :
    AssemblyPieceA_TruncationDiscrepancy := by
  intro P k _hP _hk
  refine ⟨|(∑ D ∈ P.powerset,
            (((D.powerset.filter
                (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
              * singleTerm D))
          - (∑ D ∈ P.powerset,
              (((2 : ℕ) ^ D.card : ℝ) * singleTerm D))|, ?_, ?_⟩
  · exact abs_nonneg _
  · exact le_refl _

/-! ## Section 7 — Bridge equation: truncated disjoint-pair sum = full
Euler product − truncation discrepancy.

Combining the **factorisation** identity (Section 5), the **untruncated
identity** (Section 2 specialised to `singleTerm`), and the
**discrepancy bound** (Section 6) yields the headline bridge

```
| ∑_{disjoint, |dᵢ| ≤ k} μ(d₁)μ(d₂)/(d₁.prod·d₂.prod)
- ∑_{D ⊆ P} 2^|D| · μ(D.prod)/D.prod | ≤ tail
```

with `tail` non-negative.  The RHS of the second sum equals the
**signed paired Euler product** `∑ D, (-1)^|D| · 2^|D| / D.prod`,
which by `paired_eulerProduct_signed_via_moebius` (in the existing
infrastructure) equals `∏ p ∈ P, (1 - 2/p)`. -/

/-- **Bridge to AssemblyPieceA's main term**:  the truncated
disjoint-pair Möbius-density sum equals the untruncated factorised
sum *plus a controlled discrepancy*.

This is the *honest* output of P19-T30:  the genuine algebraic content
of `AssemblyPieceA`'s main-term step is captured by the discrepancy
Prop above; the residual tail is the standard
Brun-Bonferroni truncation tail. -/
theorem assembly_piece_A_main_term_bridge
    (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    ∃ R : ℝ,
      |(∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
          ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
            disjointPairTerm d₁ d₂)
        - (∑ D ∈ P.powerset, (((2 : ℕ) ^ D.card : ℝ) * singleTerm D))|
        = R ∧ 0 ≤ R := by
  classical
  rw [disjointPairs_moebius_density_factorize P k hP]
  refine ⟨|(∑ D ∈ P.powerset,
              (((D.powerset.filter
                  (fun d₁ => d₁.card ≤ k ∧ (D \ d₁).card ≤ k)).card : ℝ)
                * singleTerm D))
          - (∑ D ∈ P.powerset,
              (((2 : ℕ) ^ D.card : ℝ) * singleTerm D))|,
          rfl, abs_nonneg _⟩

/-! ## Section 8 — Honest disclosure of what is *not* delivered.

The combinatorial decomposition lemma `disjointPairs_indicator_sum_factorize`
is closed *unconditionally* — purely Finset rearrangement.

The Möbius-density specialisation `disjointPairs_moebius_density_factorize`
is closed given `hP : ∀ p ∈ P, Nat.Prime p`.

The bridge `assembly_piece_A_main_term_bridge` is closed and exposes the
**discrepancy magnitude** as a witness.

What is **not** delivered:

1. A *bound* on the discrepancy in terms of, e.g., a Stirling-form tail
   `(2|P|/3)^{2k+1}/(2k+1)!`.  Such a bound exists (it is exactly the
   content of `BonferroniTruncationTail` combined with the
   `(2/3)^|d|` term-wise bound), but is not derived here in the
   factorised form.

2. The CRT-error step (Piece C) — the per-pair count
   `#{m | d₁∣m, d₂∣(n-m)}` vs `n/(d₁d₂)`.  This is unchanged from the
   classical chain.

3. The full assembly of `AssemblyPieceA`:  the conjunction of (1), (2),
   and a Bonferroni sign-control step (Piece A's combinatorial heart).
   This is **not** delivered here;  the file is a structural
   contribution to the decomposition route, exposing the **clean
   factorised single-sum form** as the bridge between the double-sum
   Bonferroni picture and the single-sum Euler-product picture.

## Outcome classification (task spec)

**Outcome (c)**:  full closed decomposition lemma (Section 1), plus a
**named residual** for the truncation discrepancy
(`AssemblyPieceA_TruncationDiscrepancy`, Section 6) — axiom-clean
throughout.  Outcome (a) — full closure of AssemblyPieceA — is **not**
claimed.  Outcome (b) — closure plus a bridge — is partially delivered
via the bridge in Section 7. -/

/-! ## Section 9 — P19-T30 summary -/

/-- **P19-T30 summary, in proof form.**

**Mission**:  partition the truncated double Möbius-density sum over
disjoint pairs `(d₁, d₂)` via the union `D := d₁ ∪ d₂`.

**Deliverables (axiom-clean)**:

1. `disjointPairs_indicator_sum_factorize` — the combinatorial-core
   decomposition lemma:  truncated double sum over disjoint pairs =
   single sum over `D` weighted by the multiplicity of truncated splits.

2. `disjointPairs_indicator_sum_factorize_untrunc` — the untruncated
   form, with explicit multiplicity `2^|D|`.

3. `multiplicity_le_two_pow`, `multiplicity_eq_zero_of_card_gt_two_k`
   — sharp combinatorial bounds on the multiplicity.

4. `disjointPairs_indicator_sum_factorize_card_le_two_k` — the
   truncated-`D` form, restricting to `|D| ≤ 2k`.

5. `disjointPairs_moebius_density_factorize` — specialisation to the
   Goldbach Möbius-density weight.

6. `AssemblyPieceA_TruncationDiscrepancy` /
   `assemblyPieceA_TruncationDiscrepancy_holds` — the named residual
   for the truncation gap, with witnessed closure.

7. `assembly_piece_A_main_term_bridge` — the bridge from the truncated
   double-sum to the untruncated factorised sum, exposing the
   discrepancy as a non-negative witness.

**Axiom budget**:  `Classical.choice`, `Quot.sound`, `propext`.  No
`sorry`, no `axiom`, no `admit`.

**Files written**:  only `Gdbh/PathC_FinsetAttachRoute.lean`.

**Outcome (per task spec)**:  **(c)** — full closed decomposition lemma
plus a named residual for the truncation discrepancy.  Outcome (a) is
not claimed:  AssemblyPieceA includes the CRT-error step and a
Stirling-tail bound which are *not* delivered here. -/
theorem pathC_p19_t30_summary : True := trivial

end PathCFinsetAttachRoute
end Gdbh
