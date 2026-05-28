/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T1 (Phase 19 / Path C — Paired Brun-Bonferroni truncated Möbius
inequality at the indicator level, simultaneously for `m` and `n - m`).
-/
import Gdbh.PathC_PairedBrunBonferroni

/-!
# Path C — P19-T1: Paired Brun-Bonferroni indicator at general k

This file packages the *paired* form of the Brun-Bonferroni truncated
Möbius indicator inequality.  The single-variable version is closed in
`Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds`:

```
   1{∀ p ∈ P, ¬ p ∣ m}
     ≤ ∑_{d ⊆ P, |d| ≤ k} μ(d.prod id) · 1{d.prod id ∣ m}     (k even).
```

The *paired* version, which we close here, applies the single-variable
inequality to **both** `m` and `n - m` simultaneously and takes the
product:

```
   1{∀ p ∈ P, ¬ p ∣ m} · 1{∀ p ∈ P, ¬ p ∣ (n - m)}
     ≤ (∑_{d₁ ⊆ P, |d₁| ≤ k} μ(d₁.prod id) · 1{d₁.prod id ∣ m})
       · (∑_{d₂ ⊆ P, |d₂| ≤ k} μ(d₂.prod id) · 1{d₂.prod id ∣ (n - m)})  .
```

## Why this works (the non-trivial step)

Multiplying two non-negative inequalities `0 ≤ a ≤ b` and `0 ≤ c ≤ d`
gives `a·c ≤ b·d`.  Here:

* `a = 1{m coprime to P}`, `c = 1{(n - m) coprime to P}` — both are
  indicators (0 or 1), so non-negative.
* `b = S₁`, `d = S₂` — the truncated Möbius sums.

The *crucial* observation is that for **`k` even**, the truncated
Möbius sum `S₁` is itself **non-negative**:  this is implicit in the
case analysis of `Gdbh.PathCPairedBrunBonferroni.indicator_le_truncAltSum_of_even`,
which exhibits three sub-cases (`Q = ∅`, `Q ≠ ∅ ∧ k ≥ |Q|`,
`Q ≠ ∅ ∧ k < |Q|`) whose values are `1`, `0`, `C(|Q|-1, k)` respectively,
all `≥ 0`.

Hence the indicator bound on `m` chains transitively through `0` to give
`0 ≤ S₁`, and similarly `0 ≤ S₂`.  The pairwise product `0 ≤ a·c ≤ b·d`
then follows from `mul_le_mul`.

## Honesty note

The natural product-form paired Bonferroni Prop, as stated, **is true**
for `k` even.  No false-Prop catch is needed.  The earlier honesty
disclaimer in `PathC_PairedBrunBonferroni.lean` regarding
`BrunBonferroniIndicatorPaired` referred to the *2^|d|-weighted* version
(which has sign issues), not the unweighted product form treated here.

## Axiom budget

Every theorem below is axiom-clean:  only `Classical.choice`,
`Quot.sound`, and `propext` are transitively used.  No `sorry`, `axiom`,
or `admit` appears.
-/

namespace Gdbh
namespace PathCPairedBonferroniIndicator

open scoped BigOperators
open Finset

/-! ## Section 1 — Non-negativity of the single-variable truncated Möbius sum

We first establish that the RHS of the single-variable Bonferroni
inequality is itself `≥ 0` for `k` even.  This is needed in order to
multiply two single-variable inequalities into a paired one. -/

/-- For `k` even, the single-variable truncated Möbius sum
`∑_{d ⊆ P, |d|≤k} μ(d.prod id) · 1{d.prod id ∣ m}` is non-negative.

Proof.  By the single-variable Brun-Bonferroni inequality
(`brunBonferroniIndicator_holds`), this sum is bounded below by the
indicator `(if ∀p∈P, ¬p∣m then 1 else 0)`, which is itself ≥ 0.  Hence by
transitivity it is ≥ 0. -/
lemma single_variable_truncMoebiusSum_nonneg
    (P : Finset ℕ) (m : ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hk : Even k) :
    (0 : ℝ)
      ≤ ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          (ArithmeticFunction.moebius (d.prod id) : ℝ) *
            (if (d.prod id) ∣ m then 1 else 0) := by
  classical
  -- Step 1: get the single-variable Bonferroni bound.
  have hBon :=
    Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds P m k hP hk
  -- Step 2: LHS of Bonferroni is `≥ 0` (it's an indicator).
  have hInd_nonneg :
      (0 : ℝ) ≤ (if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0) := by
    split_ifs with h
    · linarith
    · linarith
  -- Step 3: chain.
  exact le_trans hInd_nonneg hBon

/-! ## Section 2 — The paired Prop

We package the paired indicator inequality. -/

/-- **Paired Brun-Bonferroni truncated Möbius indicator inequality.**

For any finset `P` of primes, any naturals `m ≤ n`, and any even
truncation depth `k`, the *paired* indicator that **both** `m` and
`n - m` are coprime to `P` is bounded above by the product of the two
single-variable truncated Möbius sums. -/
def PairedBonferroniIndicator : Prop :=
  ∀ (P : Finset ℕ) (m n : ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    Even k →
    m ≤ n →
    (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0)
      ≤ (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
           (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
             (if (d₁.prod id) ∣ m then (1 : ℝ) else 0))
        * (∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
             (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
               (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0))

/-! ## Section 3 — Closure of the paired Prop -/

/-- **Closure of `PairedBonferroniIndicator`.**

Strategy:
1. Apply `brunBonferroniIndicator_holds` to `m`, giving
   `1{m coprime} ≤ S₁`.
2. Apply it to `n - m`, giving `1{(n - m) coprime} ≤ S₂`.
3. Both indicators are non-negative (0 or 1); both `S₁` and `S₂` are
   non-negative for `k` even by `single_variable_truncMoebiusSum_nonneg`.
4. Multiply the two inequalities via `mul_le_mul` to get
   `1{m coprime} · 1{(n - m) coprime} ≤ S₁ · S₂`.
5. Identify `1{m coprime} · 1{(n - m) coprime}` with
   `if (m coprime ∧ (n - m) coprime) then 1 else 0`.
-/
theorem pairedBonferroniIndicator_holds : PairedBonferroniIndicator := by
  classical
  intro P m n k hP hk _hmn
  -- Abbreviations for the two single-variable RHS sums.
  set S₁ : ℝ :=
    ∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
        (if (d₁.prod id) ∣ m then (1 : ℝ) else 0) with hS₁_def
  set S₂ : ℝ :=
    ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0) with hS₂_def
  -- Indicator abbreviations.
  set a : ℝ := if (∀ p ∈ P, ¬ p ∣ m) then (1 : ℝ) else 0 with ha_def
  set c : ℝ := if (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0 with hc_def
  -- Step 1: single-variable Bonferroni for `m`.
  have h₁ : a ≤ S₁ :=
    Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds P m k hP hk
  -- Step 2: single-variable Bonferroni for `n - m`.
  have h₂ : c ≤ S₂ :=
    Gdbh.PathCPairedBrunBonferroni.brunBonferroniIndicator_holds P (n - m) k hP hk
  -- Step 3: non-negativity of all four quantities.
  have ha_nn : (0 : ℝ) ≤ a := by
    rw [ha_def]
    split_ifs with h
    · linarith
    · linarith
  have hc_nn : (0 : ℝ) ≤ c := by
    rw [hc_def]
    split_ifs with h
    · linarith
    · linarith
  have hS₁_nn : (0 : ℝ) ≤ S₁ :=
    single_variable_truncMoebiusSum_nonneg P m k hP hk
  have hS₂_nn : (0 : ℝ) ≤ S₂ :=
    single_variable_truncMoebiusSum_nonneg P (n - m) k hP hk
  -- Step 4: multiply the two single-variable inequalities.
  -- We need `a · c ≤ S₁ · S₂`.
  -- Use `mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a·c ≤ b·d`.
  have hprod : a * c ≤ S₁ * S₂ := by
    have hbound : a * c ≤ S₁ * S₂ := by
      have := mul_le_mul h₁ h₂ hc_nn hS₁_nn
      exact this
    exact hbound
  -- Step 5: identify `a · c` with the paired indicator.
  have hLHS_eq :
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
  rw [hLHS_eq]
  exact hprod

/-! ## Section 4 — Re-export under a clean name -/

/-- The paired Brun-Bonferroni indicator inequality is closed. -/
theorem pairedBonferroniIndicator_closed : PairedBonferroniIndicator :=
  pairedBonferroniIndicator_holds

end PathCPairedBonferroniIndicator
end Gdbh
