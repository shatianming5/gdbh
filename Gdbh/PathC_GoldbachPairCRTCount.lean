/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P17-T3 (Phase 17 / Path C — paired CRT counting kernel for
the Brun-Goldbach sieve).
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Path C — Goldbach pair CRT counting (P17-T3)

This file is the **P17-T3 deliverable** in Phase 17.  It supplies the
paired CRT counting kernel for the Brun-Goldbach sieve.

The named open `Prop` is `GoldbachPairCRTCount`:

```
∀ n d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → Nat.Coprime d₁ d₂ → d₁ * d₂ ≤ n →
  Int.natAbs (
    (((Finset.Icc 1 (n - 1)).filter
        (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
    - (n / (d₁ * d₂) : ℤ)
  ) ≤ 1
```

## Signature note

The task statement uses `card - n / (d₁ * d₂)` inside `Int.natAbs`.
Read literally, both operands are `ℕ`, so the subtraction would be
*natural-number truncation* (`Nat.sub`).  That is one-sided: it only
bounds `card - n/(d₁d₂)` when `card ≥ n/(d₁d₂)`, and silently returns
`0` in the opposite direction.

A faithful "O(1) error" statement bounds the **two-sided** discrepancy.
We therefore cast the right-hand side to `ℤ` before subtracting, so the
genuine signed difference is bounded above by `1` in absolute value.
This is the formulation actually needed in Brun-Goldbach: both directions
of the error contribute to the sieve estimate.

## Strategy

The condition `d₁ ∣ m ∧ d₂ ∣ (n - m)` on `m ∈ Icc 1 (n-1)` (so `m < n`,
where natural subtraction agrees with the genuine difference) is, via
`Nat.modEq_iff_dvd'` and `Nat.modEq_zero_iff_dvd`, equivalent to

```
m ≡ 0  [MOD d₁]   and   m ≡ n  [MOD d₂].
```

With `Nat.Coprime d₁ d₂`, this is in turn equivalent (by
`modEq_and_modEq_iff_modEq_mul` plus a CRT representative) to

```
m ≡ c  [MOD d₁ * d₂]
```

for `c = (Nat.chineseRemainder co 0 n).val`.  Counting `m ∈ Ico 0 n` in
this single residue class is exactly `Nat.count_modEq_card`:

```
n.count (· ≡ c [MOD d₁*d₂])
  = n / (d₁*d₂) + (if c % (d₁*d₂) < n % (d₁*d₂) then 1 else 0).
```

The original target is `m ∈ Icc 1 (n-1)`, which differs from `Ico 0 n`
only by the single element `m = 0`.  Element `0` satisfies the condition
iff `d₂ ∣ n` (since `d₁ ∣ 0` always).  So our target count equals

```
n / (d₁*d₂) + ε  −  [d₂ ∣ n],
```

with `ε ∈ {0, 1}` and `[d₂ ∣ n] ∈ {0, 1}`.  The signed discrepancy from
`n / (d₁*d₂)` is therefore in `{-1, 0, 1}`, so its `Int.natAbs` is `≤ 1`,
which is exactly the named `Prop`.

## Theorem names exported

* `Gdbh.PathCGoldbachPairCRTCount.GoldbachPairCRTCount` — the named open Prop.
* `Gdbh.PathCGoldbachPairCRTCount.singleDivisorCount` — the one-sided
  counting subroutine (`#{m ∈ Icc 1 n : d ∣ m} = n / d`, hence
  `Int.natAbs(… − n/d) = 0 ≤ 1`).
* `Gdbh.PathCGoldbachPairCRTCount.goldbachPairCRTCount_holds` — closure
  of `GoldbachPairCRTCount`.
-/

namespace Gdbh
namespace PathCGoldbachPairCRTCount

open Finset

/-- **Paired CRT counting Prop.**

For coprime positive `d₁, d₂` with `d₁ * d₂ ≤ n`, the count of `m ∈
[1, n-1]` with `d₁ ∣ m` and `d₂ ∣ (n - m)` differs from `n / (d₁ * d₂)`
by at most `1` (as a signed integer). -/
def GoldbachPairCRTCount : Prop :=
  ∀ n d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → Nat.Coprime d₁ d₂ → d₁ * d₂ ≤ n →
    Int.natAbs (
      (((Finset.Icc 1 (n - 1)).filter
          (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
      - ((n / (d₁ * d₂) : ℕ) : ℤ)
    ) ≤ 1

/-! ### Subroutine: single-divisor counting -/

/-- **Subroutine.** Exact count of multiples of `d` in `Icc 1 n`:

```
#{m ∈ Icc 1 n : d ∣ m} = n / d.
```

This is mathlib's `Nat.Ioc_filter_dvd_card_eq_div` rewritten through
`Icc 1 n = Ioc 0 n`.  The signed-distance form (zero error) is stronger
than the stated `≤ 1` bound. -/
theorem singleDivisorCount (n d : ℕ) (_hd : 0 < d) :
    Int.natAbs (
      (((Finset.Icc 1 n).filter (fun m => d ∣ m)).card : ℤ)
      - ((n / d : ℕ) : ℤ)
    ) ≤ 1 := by
  classical
  -- `Icc 1 n = Ioc 0 n` on `ℕ`.
  have hicc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.lt_iff_add_one_le]
  -- Apply mathlib's exact count: `#{x ∈ Ioc 0 n | d ∣ x} = n / d`.
  have hcard : (((Finset.Icc 1 n).filter (fun m => d ∣ m)).card : ℕ) = n / d := by
    rw [hicc]
    exact Nat.Ioc_filter_dvd_card_eq_div n d
  -- The signed difference is therefore exactly zero.
  have hZ : (((Finset.Icc 1 n).filter (fun m => d ∣ m)).card : ℤ) - ((n / d : ℕ) : ℤ) = 0 := by
    have hcast : (((Finset.Icc 1 n).filter (fun m => d ∣ m)).card : ℤ) = ((n / d : ℕ) : ℤ) := by
      exact_mod_cast hcard
    linarith
  rw [hZ]
  simp
  -- The unused hypothesis `hd : 0 < d` is not needed for this exact count.

/-! ### Paired CRT counting -/

/-- For `m ≤ n` and `d ≥ 1`, `d ∣ (n - m)` (with natural-number
subtraction) is equivalent to `m ≡ n [MOD d]`. -/
private lemma dvd_sub_iff_modEq {n m d : ℕ} (hmn : m ≤ n) :
    d ∣ (n - m) ↔ m ≡ n [MOD d] := by
  rw [Nat.modEq_iff_dvd' hmn]

/-- For any `m`, `d ∣ m` iff `m ≡ 0 [MOD d]`. -/
private lemma dvd_iff_modEq_zero {m d : ℕ} :
    d ∣ m ↔ m ≡ 0 [MOD d] :=
  Nat.modEq_zero_iff_dvd.symm

/-- Equivalence of the paired divisibility condition with a single residue
class modulo `d₁ * d₂`, for coprime `d₁, d₂`. -/
private lemma paired_dvd_iff_modEq
    (n m d₁ d₂ : ℕ) (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂)
    (co : Nat.Coprime d₁ d₂) (hmn : m ≤ n) :
    (d₁ ∣ m ∧ d₂ ∣ (n - m)) ↔
      m ≡ (Nat.chineseRemainder co 0 n).val [MOD d₁ * d₂] := by
  classical
  set c := (Nat.chineseRemainder co 0 n).val with hc_def
  have hcr := (Nat.chineseRemainder co 0 n).property
  -- hcr.1 : c ≡ 0 [MOD d₁];  hcr.2 : c ≡ n [MOD d₂]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hm1 : m ≡ 0 [MOD d₁] := dvd_iff_modEq_zero.mp h₁
    have hm2 : m ≡ n [MOD d₂] := (dvd_sub_iff_modEq hmn).mp h₂
    -- m ≡ c [MOD d₁*d₂] follows by CRT uniqueness from m ≡ 0 mod d₁, m ≡ n mod d₂.
    -- chineseRemainder_modEq_unique : z ≡ a [MOD n] → z ≡ b [MOD m] → z ≡ CR [MOD n*m]
    have := Nat.chineseRemainder_modEq_unique co (a := 0) (b := n) hm1 hm2
    exact this
  · intro hmc
    -- From m ≡ c [MOD d₁ * d₂]:
    --   m ≡ c [MOD d₁]  (because d₁ ∣ d₁ * d₂)
    --   m ≡ c [MOD d₂]
    -- Combine with c ≡ 0 [MOD d₁] and c ≡ n [MOD d₂].
    have hm_d₁d₂ : m ≡ c [MOD d₁] ∧ m ≡ c [MOD d₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul co).mpr hmc
    have hm1 : m ≡ 0 [MOD d₁] := hm_d₁d₂.1.trans hcr.1
    have hm2 : m ≡ n [MOD d₂] := hm_d₁d₂.2.trans hcr.2
    have h₁ : d₁ ∣ m := dvd_iff_modEq_zero.mpr hm1
    have h₂ : d₂ ∣ (n - m) := (dvd_sub_iff_modEq hmn).mpr hm2
    exact ⟨h₁, h₂⟩

/-- The "full" range `Ico 0 n` count: by the CRT equivalence and
`Nat.count_modEq_card`, the count of `m ∈ Ico 0 n` satisfying the paired
divisibility condition differs from `n / (d₁ * d₂)` by `0` or `1`. -/
private lemma fullRange_count_eq
    (n d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (co : Nat.Coprime d₁ d₂) :
    ((Finset.Ico 0 n).filter
      (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card =
      n / (d₁ * d₂) +
        (if (Nat.chineseRemainder co 0 n).val % (d₁ * d₂) < n % (d₁ * d₂)
          then 1 else 0) := by
  classical
  set c := (Nat.chineseRemainder co 0 n).val with hc_def
  have hd₁d₂ : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  -- Rewrite the filter via the CRT equivalence: on `Ico 0 n`, members have m < n hence m ≤ n.
  have hfilt :
      (Finset.Ico 0 n).filter (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m)) =
      (Finset.Ico 0 n).filter (fun m => m ≡ c [MOD d₁ * d₂]) := by
    apply Finset.filter_congr
    intro m hm
    have hmlt : m < n := (Finset.mem_Ico.mp hm).2
    have hmn : m ≤ n := hmlt.le
    exact paired_dvd_iff_modEq n m d₁ d₂ hd₁ hd₂ co hmn
  rw [hfilt]
  -- Now apply `Nat.count_modEq_card`, which gives the formula in terms of `range n`.
  -- `range n = Ico 0 n`, so the filter card equals `n.count (· ≡ c [MOD d₁*d₂])`.
  have hrange : Finset.Ico 0 n = Finset.range n := by
    ext x
    simp [Finset.mem_range]
  rw [hrange]
  -- `n.count p = #{x ∈ range n | p x}`.
  have hcount := Nat.count_eq_card_filter_range (p := fun m => m ≡ c [MOD d₁ * d₂]) n
  rw [← hcount]
  exact Nat.count_modEq_card n hd₁d₂ c

/-- Removing the `m = 0` case from the `range n` filter gives the
`Icc 1 (n-1)` filter, exactly when `n ≥ 1`. -/
private lemma icc_one_card_eq_range_card_sub
    (n d₁ d₂ : ℕ) (hn : 1 ≤ n) :
    (((Finset.Icc 1 (n - 1)).filter
        (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
      = (((Finset.Ico 0 n).filter
            (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
        - (if d₂ ∣ n then 1 else 0) := by
  classical
  -- `Icc 1 (n - 1)` equals `Ico 1 n` on ℕ when `1 ≤ n`.
  have hicc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      omega
  -- Decompose `Ico 0 n = {0} ∪ Ico 1 n` as a disjoint union.
  have hsplit : Finset.Ico 0 n = insert 0 (Finset.Ico 1 n) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    constructor
    · rintro ⟨_, hk⟩
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exact Or.inl hk0
      · exact Or.inr ⟨hk0, hk⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Nat.zero_le _, hn⟩
      · exact ⟨Nat.zero_le _, h2⟩
  have hzero_not_mem : 0 ∉ Finset.Ico 1 n := by
    intro h
    have := (Finset.mem_Ico.mp h).1
    exact absurd this (by omega)
  -- Filter then card; use `filter_insert` to split.
  set p : ℕ → Prop := fun m => d₁ ∣ m ∧ d₂ ∣ (n - m) with hp_def
  -- p 0 ↔ d₂ ∣ n (since `d₁ ∣ 0` and `n - 0 = n`).
  have hp0 : p 0 ↔ d₂ ∣ n := by
    simp [hp_def]
  have hfilt_split :
      (Finset.Ico 0 n).filter p =
        if p 0 then insert 0 ((Finset.Ico 1 n).filter p)
              else (Finset.Ico 1 n).filter p := by
    rw [hsplit]
    exact Finset.filter_insert p (0 : ℕ) (Finset.Ico 1 n)
  rw [hicc]
  by_cases h0 : p 0
  · -- `d₂ ∣ n` case
    have hdvdn : d₂ ∣ n := hp0.mp h0
    have h_card :
        ((Finset.Ico 0 n).filter p).card =
          ((Finset.Ico 1 n).filter p).card + 1 := by
      rw [hfilt_split, if_pos h0]
      have hzero_not_mem' : 0 ∉ (Finset.Ico 1 n).filter p := by
        intro hmem
        exact hzero_not_mem (Finset.mem_filter.mp hmem).1
      rw [Finset.card_insert_of_notMem hzero_not_mem']
    rw [if_pos hdvdn]
    have : (((Finset.Ico 1 n).filter p).card : ℤ) =
           (((Finset.Ico 0 n).filter p).card : ℤ) - 1 := by
      have := congrArg (fun k : ℕ => (k : ℤ)) h_card
      push_cast at this
      linarith
    linarith
  · -- `¬ (d₂ ∣ n)` case
    have hndvdn : ¬ d₂ ∣ n := fun h => h0 (hp0.mpr h)
    have h_card :
        ((Finset.Ico 0 n).filter p).card =
          ((Finset.Ico 1 n).filter p).card := by
      rw [hfilt_split, if_neg h0]
    rw [if_neg hndvdn]
    have : (((Finset.Ico 1 n).filter p).card : ℤ) =
           (((Finset.Ico 0 n).filter p).card : ℤ) := by
      have := congrArg (fun k : ℕ => (k : ℤ)) h_card
      push_cast at this
      linarith
    linarith

/-- **Closure** of `GoldbachPairCRTCount`. -/
theorem goldbachPairCRTCount_holds : GoldbachPairCRTCount := by
  classical
  intro n d₁ d₂ hd₁ hd₂ co hle
  -- Set up shorthand.
  set D : ℕ := d₁ * d₂ with hD_def
  have hD : 0 < D := Nat.mul_pos hd₁ hd₂
  have hn : 1 ≤ n := le_trans hD hle
  set c : ℕ := (Nat.chineseRemainder co 0 n).val with hc_def
  -- The count over the full range `Ico 0 n`:
  have hfull :
      ((Finset.Ico 0 n).filter
        (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card =
        n / D + (if c % D < n % D then 1 else 0) := by
    simpa [hD_def, hc_def] using fullRange_count_eq n d₁ d₂ hd₁ hd₂ co
  -- The relation between `Icc 1 (n-1)` and `Ico 0 n`:
  have hsub :
      (((Finset.Icc 1 (n - 1)).filter
          (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
        = (((Finset.Ico 0 n).filter
              (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
          - (if d₂ ∣ n then 1 else 0) :=
    icc_one_card_eq_range_card_sub n d₁ d₂ hn
  -- Cast `hfull` to ℤ.
  have hfullZ :
      (((Finset.Ico 0 n).filter
          (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
        = ((n / D : ℕ) : ℤ) + (if c % D < n % D then (1 : ℤ) else 0) := by
    by_cases hcase : c % D < n % D
    · have hfull' :
          ((Finset.Ico 0 n).filter
            (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card = n / D + 1 := by
        rw [hfull, if_pos hcase]
      rw [if_pos hcase]
      exact_mod_cast hfull'
    · have hfull' :
          ((Finset.Ico 0 n).filter
            (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card = n / D := by
        rw [hfull, if_neg hcase, Nat.add_zero]
      rw [if_neg hcase]
      simpa using (by exact_mod_cast hfull' :
        (((Finset.Ico 0 n).filter
            (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ) = ((n / D : ℕ) : ℤ))
  -- Combine: signed count − n/D = (if c%D < n%D then 1 else 0) − (if d₂ ∣ n then 1 else 0).
  -- The Prop's RHS is `((n / (d₁ * d₂) : ℕ) : ℤ)`, which with `D = d₁ * d₂` is `((n / D : ℕ) : ℤ)`.
  show Int.natAbs (
        (((Finset.Icc 1 (n - 1)).filter
            (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
        - ((n / (d₁ * d₂) : ℕ) : ℤ)
      ) ≤ 1
  have hdiff :
      (((Finset.Icc 1 (n - 1)).filter
          (fun m => d₁ ∣ m ∧ d₂ ∣ (n - m))).card : ℤ)
        - ((n / (d₁ * d₂) : ℕ) : ℤ)
      = (if c % D < n % D then (1 : ℤ) else 0)
        - (if d₂ ∣ n then (1 : ℤ) else 0) := by
    rw [hsub]
    rw [hfullZ]
    -- Now reduce to: (RHS_full - (if d₂ ∣ n) - (↑n/(d₁*d₂))) = .. ; D = d₁*d₂.
    have : ((n / (d₁ * d₂) : ℕ) : ℤ) = ((n / D : ℕ) : ℤ) := by
      simp [hD_def]
    rw [this]
    ring
  -- The right-hand side is in {-1, 0, 1}, so its natAbs is ≤ 1.
  rw [hdiff]
  by_cases h1 : c % D < n % D <;> by_cases h2 : d₂ ∣ n <;> simp [h1, h2]

end PathCGoldbachPairCRTCount
end Gdbh
