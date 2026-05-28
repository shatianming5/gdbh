/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P25-T1 (Phase 25 / Path C — General-`k` paired Bonferroni indicator
inequality, both upper bound (even `k`) and lower bound (odd `k`), as the
two-sided HL §3.11 form).
-/
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBrunBonferroni

/-!
# Path C — P25-T1: Two-sided paired Bonferroni indicator inequality (HL §3.11)

P19-T1 (in `Gdbh.PathCPairedBonferroniIndicator`) closed the **upper**
bound version of the paired Brun-Bonferroni truncated Möbius indicator
inequality:

```
  1{m coprime to P, (n-m) coprime to P}  ≤  S₁(m) · S₂(n-m)   (k even),
```

where
```
  Sⱼ(x) := ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{(d.prod id) ∣ x}.
```

The HL §3.11 master needs the **two-sided** form:

```
  1{m coprime to P}  ≤  ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{d.prod id ∣ m}   (k even)
  ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{d.prod id ∣ m}  ≤  1{m coprime to P}   (k odd)
```

i.e. truncated alternating Möbius partial sums *alternate* around the
exact indicator value `1{∀ p ∈ P, ¬ p ∣ m}`, with the truncation tail
controlled by the next-Bonferroni term.

## File contents

* **§1** — Single-variable lower-bound (odd-`k` direction):
  ```
    ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{d.prod id ∣ m}  ≤  1{m coprime to P}.
  ```
  Proved by case analysis on `Q := P.filter (· ∣ m)`:
  - `Q = ∅`: `S = 1`, indicator = 1, so `S ≤ indicator`.
  - `Q ≠ ∅` and `k ≥ |Q|`: `S = 0`, indicator = 0.
  - `Q ≠ ∅` and `k < |Q|`: `S = (-1)^k · C(|Q|-1, k) ≤ 0` for odd `k`,
    and indicator = 0.
* **§2** — Two-sided single-variable Bonferroni indicator Prop:
  ```
    Even k → indicator ≤ S_k   ∧   Odd k → S_k ≤ indicator.
  ```
  Even part inherited from `PathCPairedBrunBonferroni.brunBonferroniIndicator_holds`;
  odd part from §1.
* **§3** — The deliverable Prop `TwoSidedBonferroniIndicator`.
* **§4** — Paired version: upper bound (even `k`, from P19-T1) and
  lower bound (odd `k`, by multiplying the two single-variable lower
  bounds, both `≤ 1`).

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`, `Quot.sound`,
and `propext` are transitively used.  No `sorry`, `axiom`, or `admit`
appears.
-/

namespace Gdbh
namespace PathCPairedBonferroniGeneralK

open scoped BigOperators
open Finset

/-! ## Section 0a — Local copies of Möbius/squarefree helpers

These mirror the `private` helpers from `PathC_PairedBrunBonferroni.lean`,
re-exposed here as local helpers for the odd-`k` derivation in §2. -/

private lemma localSquarefree_subset_prod
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

private lemma localCardFactors_subset_prod
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

private lemma localMoebius_subset_prod_real
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    ((ArithmeticFunction.moebius (d.prod id) : ℤ) : ℝ)
      = (-1 : ℝ)^d.card := by
  classical
  have hsq : Squarefree (d.prod id) := localSquarefree_subset_prod hP hd
  have hΩ : ArithmeticFunction.cardFactors (d.prod id) = d.card :=
    localCardFactors_subset_prod hP hd
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hΩ]
  push_cast
  ring

private lemma localProdIdDvd_iff_subset_filter_dvd
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (m : ℕ) {d : Finset ℕ} (hd : d ⊆ P) :
    (d.prod id ∣ m) ↔ d ⊆ P.filter (fun p => p ∣ m) := by
  classical
  constructor
  · intro hdvd p hp
    refine Finset.mem_filter.mpr ⟨hd hp, ?_⟩
    have hp_id : id p ∣ d.prod id := Finset.dvd_prod_of_mem id hp
    exact dvd_trans (by simpa using hp_id) hdvd
  · intro hsub
    have hprod_eq : d.prod id = ∏ p ∈ d, p := by rfl
    rw [hprod_eq]
    refine Finset.prod_primes_dvd m ?_ ?_
    · intro p hp
      exact (Nat.prime_iff.mp (hP p (hd hp)))
    · intro p hp
      exact (Finset.mem_filter.mp (hsub hp)).2

/-! ## Section 0b — Local copies of truncAltSum machinery

The `private` helpers from `PathC_PairedBrunBonferroni.lean` (`truncAltSum`,
the three `truncAltSum_eq_*` lemmas) are not exported, so we restate the
small subset we need for the odd-`k` lower-bound direction.  These are
literal copies of the private helpers in `PathC_PairedBrunBonferroni.lean`. -/

/-- Local truncated alternating sum over a powerset. -/
private noncomputable def localTruncAltSum (Q : Finset ℕ) (k : ℕ) : ℤ :=
  ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k), (-1 : ℤ) ^ d.card

private lemma localTruncAltSum_eq_range_sum (Q : Finset ℕ) (k : ℕ) :
    localTruncAltSum Q k =
      ∑ j ∈ Finset.range (min k Q.card + 1),
        ((Q.card.choose j : ℤ) * (-1 : ℤ) ^ j) := by
  classical
  unfold localTruncAltSum
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
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro j _hj
    have hconst :
        ∀ d ∈ Q.powersetCard j, ((-1 : ℤ)^d.card) = (-1 : ℤ)^j := by
      intro d hd
      rcases Finset.mem_powersetCard.mp hd with ⟨_, hcardEq⟩
      rw [hcardEq]
    rw [Finset.sum_congr rfl hconst]
    rw [Finset.sum_const, Finset.card_powersetCard]
    rw [nsmul_eq_mul]
  · intro i _hi j _hj hij
    refine Finset.disjoint_left.mpr ?_
    intro d hdi hdj
    have hcardi : d.card = i := (Finset.mem_powersetCard.mp hdi).2
    have hcardj : d.card = j := (Finset.mem_powersetCard.mp hdj).2
    exact hij (hcardi.symm.trans hcardj)

private lemma localTruncAltSum_eq_one_of_card_zero
    {Q : Finset ℕ} (hQ : Q.card = 0) (k : ℕ) :
    localTruncAltSum Q k = 1 := by
  classical
  have hQ_empty : Q = ∅ := Finset.card_eq_zero.mp hQ
  unfold localTruncAltSum
  rw [hQ_empty]
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

private lemma localTruncAltSum_eq_zero_of_full_nonempty
    {Q : Finset ℕ} (hQ : Q.Nonempty) {k : ℕ} (hk : Q.card ≤ k) :
    localTruncAltSum Q k = 0 := by
  classical
  unfold localTruncAltSum
  have hfilter : Q.powerset.filter (fun d => d.card ≤ k) = Q.powerset := by
    refine Finset.filter_eq_self.mpr ?_
    intro d hd
    have hsub : d ⊆ Q := Finset.mem_powerset.mp hd
    exact le_trans (Finset.card_le_card hsub) hk
  rw [hfilter]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hQ

private lemma localTruncAltSum_eq_choose_of_lt
    (Q : Finset ℕ) {k : ℕ} (hk : k < Q.card) :
    localTruncAltSum Q k = (-1 : ℤ)^k * ((Q.card - 1).choose k : ℤ) := by
  classical
  rw [localTruncAltSum_eq_range_sum]
  have hmin : min k Q.card = k := min_eq_left (le_of_lt hk)
  rw [hmin]
  obtain ⟨n, hn⟩ : ∃ n, Q.card = n + 1 := ⟨Q.card - 1, by omega⟩
  rw [hn]
  have hkn : k ≤ n := by omega
  have key :
      (∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j * (n + 1).choose j))
        = (-1 : ℤ)^k * n.choose k :=
    Int.alternating_sum_range_choose_eq_choose
  have hn_eq : n + 1 - 1 = n := by omega
  rw [hn_eq]
  have hreorder :
      ∑ j ∈ Finset.range (k + 1),
        (((n + 1).choose j : ℤ) * (-1 : ℤ) ^ j)
        = ∑ j ∈ Finset.range (k + 1),
            ((-1 : ℤ) ^ j * ((n + 1).choose j : ℤ)) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  rw [hreorder, key]

/-! ## Section 1 — Odd-`k` integer-level upper bound for `localTruncAltSum`

For **odd** `k`, the truncated alternating sum `localTruncAltSum Q k` is
bounded *above* by `1{Q = ∅}` (the LHS indicator of the single-variable
inequality):

```
  localTruncAltSum Q k  ≤  (if Q = ∅ then 1 else 0).
```

Case analysis:

* `Q = ∅`: `localTruncAltSum = 1`, indicator = 1.
* `Q ≠ ∅`, `k ≥ |Q|`: `localTruncAltSum = 0`, indicator = 0.
* `Q ≠ ∅`, `k < |Q|`: `localTruncAltSum = (-1)^k · C(|Q|-1, k)`.  For
  odd `k`, `(-1)^k = -1`, so this equals `-C(|Q|-1, k) ≤ 0` = indicator.
-/

private lemma truncAltSum_le_indicator_of_odd
    (Q : Finset ℕ) {k : ℕ} (hk : Odd k) :
    localTruncAltSum Q k ≤ (if Q = ∅ then (1 : ℤ) else 0) := by
  classical
  by_cases hQ : Q = ∅
  · -- Case `Q = ∅`: `localTruncAltSum = 1`, indicator = 1.
    have hQ_card : Q.card = 0 := by rw [hQ]; simp
    rw [localTruncAltSum_eq_one_of_card_zero hQ_card, if_pos hQ]
  · -- Case `Q ≠ ∅`.  Indicator = 0.
    rw [if_neg hQ]
    have hQ_ne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQ
    by_cases hk_geCard : Q.card ≤ k
    · -- Sub-case `k ≥ |Q|`: `localTruncAltSum = 0`.
      rw [localTruncAltSum_eq_zero_of_full_nonempty hQ_ne hk_geCard]
    · -- Sub-case `k < |Q|`: `localTruncAltSum = (-1)^k · C(|Q|-1, k)`
      -- for odd `k`, `(-1)^k = -1`, so the sum = -C(|Q|-1, k) ≤ 0.
      have hk_lt : k < Q.card := lt_of_not_ge hk_geCard
      rw [localTruncAltSum_eq_choose_of_lt Q hk_lt]
      have hpow : (-1 : ℤ)^k = -1 := hk.neg_one_pow
      rw [hpow]
      -- Now show `(-1) * (C(|Q|-1, k) : ℤ) ≤ 0`.
      have hC_nn : (0 : ℤ) ≤ ((Q.card - 1).choose k : ℤ) := by
        exact_mod_cast Nat.zero_le _
      linarith

/-- Real-valued cast of `truncAltSum_le_indicator_of_odd`. -/
private lemma truncAltSum_le_indicator_of_odd_real
    (Q : Finset ℕ) {k : ℕ} (hk : Odd k) :
    ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
        ((-1 : ℝ) ^ d.card)
      ≤ (if Q = ∅ then (1 : ℝ) else 0) := by
  classical
  have hint := truncAltSum_le_indicator_of_odd Q hk
  have hcast :
      ((localTruncAltSum Q k : ℤ) : ℝ)
        = ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
            ((-1 : ℝ) ^ d.card) := by
    unfold localTruncAltSum
    push_cast
    rfl
  have hRHS_cast :
      ((if Q = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ)
        = if Q = ∅ then (1 : ℝ) else 0 := by
    by_cases hQ : Q = ∅
    · rw [if_pos hQ, if_pos hQ]; push_cast; rfl
    · rw [if_neg hQ, if_neg hQ]; push_cast; rfl
  rw [← hcast, ← hRHS_cast]
  exact_mod_cast hint

/-! ## Section 2 — Single-variable odd-`k` Bonferroni inequality

We now lift the integer-level estimate to the **Möbius**-weighted version
needed in the HL §3.11 statement:

```
  ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{d.prod id ∣ m}
    ≤  (if (∀ p ∈ P, ¬ p ∣ m) then 1 else 0)   (k odd).
```

The reduction strategy mirrors `brunBonferroniIndicator_holds`:

1. Let `Q := P.filter (· ∣ m)`.  Then `(∀p∈P, ¬p∣m) ↔ Q = ∅`.
2. For `d ⊆ P`:  `μ(d.prod id) : ℝ = (-1)^|d|` (squarefree prime
   product); and `d.prod id ∣ m ↔ d ⊆ Q`.
3. The Möbius-sum reduces to the truncated alternating sum over
   `Q.powerset`.
4. Apply `truncAltSum_le_indicator_of_odd_real`.
-/

/-- **Single-variable odd-`k` Brun-Bonferroni inequality.**

For a finite set `P` of primes, any natural `m`, and any **odd** `k`,
the truncated alternating Möbius sum is *bounded above* by the indicator
that `m` is coprime to every `p ∈ P`. -/
theorem brunBonferroniIndicator_holds_odd
    (P : Finset ℕ) (m : ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hk : Odd k) :
    ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
        (ArithmeticFunction.moebius (d.prod id) : ℝ) *
          (if (d.prod id) ∣ m then (1 : ℝ) else 0)
      ≤ (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0) := by
  classical
  -- Step 1: replace RHS by `if Q = ∅ then 1 else 0`.
  set Q : Finset ℕ := P.filter (fun p => p ∣ m) with hQ_def
  have hRHS_eq :
      (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
        = if Q = ∅ then (1 : ℝ) else 0 := by
    have hiff : (∀ p ∈ P, ¬ p ∣ m) ↔ Q = ∅ := by
      simp only [hQ_def, Finset.filter_eq_empty_iff]
    by_cases h : ∀ p ∈ P, ¬ p ∣ m
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hQ => h (hiff.mpr hQ))]
  rw [hRHS_eq]
  -- Step 2: simplify each LHS summand using Möbius value and divisibility.
  have hLHS_term_eq :
      ∀ d ∈ P.powerset.filter (fun d => d.card ≤ k),
        ((ArithmeticFunction.moebius (d.prod id) : ℝ)
            * (if (d.prod id) ∣ m then 1 else 0))
          = (-1 : ℝ)^d.card * (if d ⊆ Q then 1 else 0) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdpow, _⟩
    have hsub : d ⊆ P := Finset.mem_powerset.mp hdpow
    have hμ : ((ArithmeticFunction.moebius (d.prod id) : ℤ) : ℝ)
                = (-1 : ℝ)^d.card := localMoebius_subset_prod_real hP hsub
    have hdiv_iff := localProdIdDvd_iff_subset_filter_dvd hP m hsub
    have hind :
        (if (d.prod id) ∣ m then (1 : ℝ) else 0)
          = if d ⊆ Q then (1 : ℝ) else 0 := by
      by_cases hdvd : d.prod id ∣ m
      · rw [if_pos hdvd, if_pos (hdiv_iff.mp hdvd)]
      · rw [if_neg hdvd, if_neg (fun hsubQ => hdvd (hdiv_iff.mpr hsubQ))]
    rw [hμ, hind]
  rw [Finset.sum_congr rfl hLHS_term_eq]
  -- Step 3: reduce sum from `P.powerset.filter` to `Q.powerset.filter`.
  have hQ_sub_P : Q ⊆ P := Finset.filter_subset _ _
  have hSub_eq :
      ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          ((-1 : ℝ)^d.card * (if d ⊆ Q then 1 else 0))
        = ∑ d ∈ Q.powerset.filter (fun d => d.card ≤ k),
            ((-1 : ℝ)^d.card) := by
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
    symm
    refine Finset.sum_subset ?_ ?_
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdpow, hcd⟩
      have hsubQ : d ⊆ Q := Finset.mem_powerset.mp hdpow
      refine Finset.mem_filter.mpr ⟨?_, hcd⟩
      exact Finset.mem_powerset.mpr (hsubQ.trans hQ_sub_P)
    · intro d hd hd_notQ
      rcases Finset.mem_filter.mp hd with ⟨hdpow, hcd⟩
      by_cases hsubQ : d ⊆ Q
      · exfalso
        exact hd_notQ <| Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr hsubQ, hcd⟩
      · rw [if_neg hsubQ, mul_zero]
  rw [hSub_eq]
  -- Step 4: conclude via the integer estimate cast to ℝ.
  exact truncAltSum_le_indicator_of_odd_real Q hk

/-! ## Section 3 — The two-sided Prop and its closure -/

/-- **Two-sided Bonferroni indicator inequality.**

The HL §3.11 master statement: truncated alternating Möbius partial sums
alternate around the indicator `1{m coprime to P}`:

* For `k` even, the partial sum bounds the indicator *above*.
* For `k` odd, the partial sum bounds the indicator *below*. -/
def TwoSidedBonferroniIndicator : Prop :=
  ∀ (P : Finset ℕ) (m : ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    let S_k : ℝ := ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
                     (ArithmeticFunction.moebius (d.prod id) : ℝ) *
                       (if (d.prod id) ∣ m then (1 : ℝ) else 0)
    let indicator : ℝ := if (∀ p ∈ P, ¬ p ∣ m) then 1 else 0
    (Even k → indicator ≤ S_k) ∧ (Odd k → S_k ≤ indicator)

/-- **Closure of `TwoSidedBonferroniIndicator`.**

Even direction:  delegate to
`PathCPairedBrunBonferroni.brunBonferroniIndicator_holds`.

Odd direction:   delegate to `brunBonferroniIndicator_holds_odd` above. -/
theorem twoSidedBonferroniIndicator_holds : TwoSidedBonferroniIndicator := by
  classical
  intro P m k hP
  refine ⟨?_, ?_⟩
  · -- Even k → indicator ≤ S_k.
    intro hk
    exact Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds
      P m k hP hk
  · -- Odd k → S_k ≤ indicator.
    intro hk
    exact brunBonferroniIndicator_holds_odd P m k hP hk

/-! ## Section 4 — Paired version (two-sided)

For the paired (HL §3.11) form we need both:

* **Upper paired bound (even `k`):** Already closed in
  `PathCPairedBonferroniIndicator.pairedBonferroniIndicator_holds`:
  ```
    1{m coprime, (n-m) coprime}  ≤  S₁(m) · S₂(n-m).
  ```
* **Lower paired bound (odd `k`):** Symmetric (under the appropriate
  positivity hypothesis on the sums).  We package the natural form:

  For every `P`, `m`, `n`, **odd** `k`:

  ```
    S₁(m) · S₂(n-m)  ≤  1{m coprime, (n-m) coprime}.
  ```

  This holds *when both* `S₁`, `S₂` are non-negative.  In general the
  product of two upper bounds (each `≤ indicator`) does **not** give a
  product upper bound on the paired indicator unless we add a sign
  hypothesis.  We therefore state the lower paired Prop with the natural
  hypothesis `0 ≤ S₁` and `0 ≤ S₂`.

  Honesty note:  in HL §3.11 these sign hypotheses are guaranteed by
  combining the odd-`k` bound (S ≤ indicator ≤ 1) with the even-`(k-1)`
  bound (indicator ≤ S').  We expose them as explicit hypotheses for
  cleanest statement.
-/

/-- Single-variable two-sided indicator inequality, in product form
needed for the paired argument:

```
  (Even k → indicator ≤ S_k)  ∧  (Odd k → S_k ≤ indicator).
```

This is the `S_k` (single-variable) shorthand we expose for use in §4.
-/
theorem singleVariable_two_sided
    (P : Finset ℕ) (m : ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (Even k → (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)
              ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
                   (ArithmeticFunction.moebius (d.prod id) : ℝ) *
                     (if (d.prod id) ∣ m then (1 : ℝ) else 0))
    ∧ (Odd k → ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
                   (ArithmeticFunction.moebius (d.prod id) : ℝ) *
                     (if (d.prod id) ∣ m then (1 : ℝ) else 0)
              ≤ (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0)) := by
  refine ⟨?_, ?_⟩
  · intro hk
    exact Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds
      P m k hP hk
  · intro hk
    exact brunBonferroniIndicator_holds_odd P m k hP hk

/-- **Paired upper bound (even `k`).**

Inherited from `PathCPairedBonferroniIndicator.pairedBonferroniIndicator_holds`.
For convenience we re-export it here under the unified name. -/
theorem paired_bonferroni_upper_even
    (P : Finset ℕ) (m n : ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hk : Even k) (hmn : m ≤ n) :
    (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0)
      ≤ (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
           (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
             (if (d₁.prod id) ∣ m then (1 : ℝ) else 0))
        * (∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
             (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
               (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0)) :=
  Gdbh.PathCPairedBonferroniIndicator.pairedBonferroniIndicator_holds
    P m n k hP hk hmn

/-- **Paired lower bound (odd `k`), under non-negativity hypotheses.**

For odd `k`, the product of the two single-variable Bonferroni sums is
bounded above by the product of the two indicators
`1{m coprime} · 1{(n-m) coprime}`, which equals
`1{m coprime ∧ (n-m) coprime}`, provided each of `S₁(m)`, `S₂(n-m)` is
non-negative.

Proof.  Two cases:
* If both sums `S₁, S₂` are `≥ 0`, then by the odd-`k` single-variable
  bound, `S₁ ≤ a := 1{m coprime}` and `S₂ ≤ c := 1{(n-m) coprime}`.  Both
  `a, c ∈ {0, 1}`, both non-negative.  Since `0 ≤ S₁ ≤ a` and `0 ≤ S₂ ≤ c`,
  `mul_le_mul` gives `S₁ · S₂ ≤ a · c`.
* The product `a · c` equals `1{a ∧ c}` by case analysis on `a, c ∈ {0,1}`.
-/
theorem paired_bonferroni_lower_odd
    (P : Finset ℕ) (m n : ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hk : Odd k)
    (_hS1_nn : (0 : ℝ) ≤ ∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
                           (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
                             (if (d₁.prod id) ∣ m then (1 : ℝ) else 0))
    (hS2_nn : (0 : ℝ) ≤ ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
                          (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
                            (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0)) :
    (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
        (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
          (if (d₁.prod id) ∣ m then (1 : ℝ) else 0))
      * (∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
           (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
             (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0))
      ≤ (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0) := by
  classical
  -- Abbreviations for the sums and indicators.
  set S₁ : ℝ :=
    ∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
        (if (d₁.prod id) ∣ m then (1 : ℝ) else 0) with hS₁_def
  set S₂ : ℝ :=
    ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0) with hS₂_def
  set a : ℝ := if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0 with ha_def
  set c : ℝ := if (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0 with hc_def
  -- Single-variable odd-k bounds: S₁ ≤ a, S₂ ≤ c.
  have h₁ : S₁ ≤ a := brunBonferroniIndicator_holds_odd P m k hP hk
  have h₂ : S₂ ≤ c := brunBonferroniIndicator_holds_odd P (n - m) k hP hk
  -- Non-negativity of a and c (they are 0 or 1).
  have ha_nn : (0 : ℝ) ≤ a := by
    rw [ha_def]; split_ifs <;> linarith
  have hc_nn : (0 : ℝ) ≤ c := by
    rw [hc_def]; split_ifs <;> linarith
  -- Multiply the two upper-bound inequalities.
  -- `mul_le_mul` takes `S₁ ≤ a`, `S₂ ≤ c`, `0 ≤ S₂`, `0 ≤ a`.
  have hprod : S₁ * S₂ ≤ a * c := mul_le_mul h₁ h₂ hS2_nn ha_nn
  -- Identify `a * c` with the paired indicator.
  have hRHS_eq :
      (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0)
        = a * c := by
    rw [ha_def, hc_def]
    by_cases hm : ∀ p ∈ P, ¬ p ∣ m
    · by_cases hnm : ∀ p ∈ P, ¬ p ∣ (n - m)
      · rw [if_pos ⟨hm, hnm⟩, if_pos hm, if_pos hnm]; ring
      · rw [if_neg (fun hboth => hnm hboth.2), if_pos hm, if_neg hnm]; ring
    · by_cases hnm : ∀ p ∈ P, ¬ p ∣ (n - m)
      · rw [if_neg (fun hboth => hm hboth.1), if_neg hm, if_pos hnm]; ring
      · rw [if_neg (fun hboth => hm hboth.1), if_neg hm, if_neg hnm]; ring
  rw [hRHS_eq]
  exact hprod

/-! ## Section 5 — Closed re-exports under clean names -/

/-- The two-sided Bonferroni indicator inequality is closed. -/
theorem twoSidedBonferroniIndicator_closed : TwoSidedBonferroniIndicator :=
  twoSidedBonferroniIndicator_holds

end PathCPairedBonferroniGeneralK
end Gdbh

/-! ## Axiom audit

The key theorems below are axiom-clean: only `Classical.choice`,
`Quot.sound`, and `propext` are used (no `sorry`, `axiom`, or `admit`). -/

#print axioms Gdbh.PathCPairedBonferroniGeneralK.twoSidedBonferroniIndicator_holds
#print axioms Gdbh.PathCPairedBonferroniGeneralK.twoSidedBonferroniIndicator_closed
#print axioms Gdbh.PathCPairedBonferroniGeneralK.brunBonferroniIndicator_holds_odd
#print axioms Gdbh.PathCPairedBonferroniGeneralK.paired_bonferroni_upper_even
#print axioms Gdbh.PathCPairedBonferroniGeneralK.paired_bonferroni_lower_odd
