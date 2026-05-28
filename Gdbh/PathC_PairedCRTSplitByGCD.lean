/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P25-T2 (Phase 25 / Path C — paired CRT counting split by
the prime divisibility of `n`, for the Brun-Goldbach sieve).
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Path C — Paired CRT count, split by `gcd(d, n)` (P25-T2)

The previous paired-CRT kernel (`PathC_GoldbachPairCRTCount`) handles
**coprime** divisor pairs `(d₁, d₂)` and bounds the deviation by `1`.
The Hardy-Littlewood §3.11 master expansion requires a finer splitting:
for a single squarefree modulus `d`, the count

```
#{m ∈ [1, n-1] : d ∣ m ∧ d ∣ (n - m)}
```

must be split according to whether `d ∣ n`:

* **`d ∤ n`** — the conditions `d ∣ m` and `d ∣ (n - m)` are
  *incompatible*: from `d ∣ m` and `d ∣ (n - m)` with `m ≤ n` we deduce
  `d ∣ n`, contradicting `d ∤ n`.  So the count is **zero**.

* **`d ∣ n`** — given `d ∣ n`, `d ∣ m ↔ d ∣ (n - m)` (because
  `n - m + m = n` and `d ∣ n`), so the joint condition reduces to
  `d ∣ m`.  The count is then the number of multiples of `d` in
  `[1, n-1]`, which equals `(n - 1) / d`, and under `d ∣ n, 0 < d`
  this equals `n / d - 1` (`ℕ` subtraction).

The natural-number difference `count - (n / d - 1)` is therefore
identically zero on both branches, so `Int.natAbs ≤ 1` is trivial.

## Theorem names exported

* `Gdbh.PathCPairedCRTSplitByGCD.goldbachPairCount_split` — the
  definition.
* `Gdbh.PathCPairedCRTSplitByGCD.goldbachPairCount_split_zero_of_not_dvd`
  — the `¬ d ∣ n` branch.
* `Gdbh.PathCPairedCRTSplitByGCD.goldbachPairCount_split_eq_div_of_dvd`
  — the `d ∣ n` branch.
-/

namespace Gdbh
namespace PathCPairedCRTSplitByGCD

open Finset

/-- **Split paired CRT count.** Number of `m ∈ [1, n-1]` for which the
single squarefree modulus `d` divides **both** `m` and `n - m`. -/
def goldbachPairCount_split (n d : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).filter (fun m => d ∣ m ∧ d ∣ (n - m))).card

/-! ### Branch 1 : `d ∤ n` — the count is zero. -/

/-- The paired count is non-trivial only when `d ∣ n`.

If `d ∤ n` (and `d > 0`), then for every `m ∈ [1, n-1]` we have `m ≤ n`,
so the additivity `(n - m) + m = n` together with `d ∣ m` and
`d ∣ (n - m)` would force `d ∣ n`, contradiction. -/
theorem goldbachPairCount_split_zero_of_not_dvd
    (n d : ℕ) (hd : ¬ d ∣ n) (_hd_pos : 0 < d) :
    goldbachPairCount_split n d = 0 := by
  classical
  unfold goldbachPairCount_split
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro m hm hcond
  obtain ⟨hm1, hmn1⟩ := Finset.mem_Icc.mp hm
  have hmn : m ≤ n := by omega
  obtain ⟨hd_m, hd_nm⟩ := hcond
  have hsum : (n - m) + m = n := Nat.sub_add_cancel hmn
  have hd_n : d ∣ n := by
    have := Nat.dvd_add hd_nm hd_m
    rw [hsum] at this
    exact this
  exact hd hd_n

/-! ### Branch 2 : `d ∣ n` — the count equals `(n-1)/d = n/d - 1`. -/

/-- Helper: on `[1, n-1]`, the condition `d ∣ m ∧ d ∣ (n - m)` is
equivalent to `d ∣ m` whenever `d ∣ n`. -/
private lemma cond_iff_dvd_m
    {n d m : ℕ} (hd : d ∣ n) (_hmn : m ≤ n) :
    (d ∣ m ∧ d ∣ (n - m)) ↔ d ∣ m := by
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro hdm
    exact ⟨hdm, Nat.dvd_sub hd hdm⟩

/-- Helper: under `d ∣ n`, the filtered set
`{m ∈ Icc 1 (n-1) | d ∣ m ∧ d ∣ (n - m)}` equals
`{m ∈ Icc 1 (n-1) | d ∣ m}`. -/
private lemma filter_paired_eq_filter_dvd
    (n d : ℕ) (hd : d ∣ n) :
    (Finset.Icc 1 (n - 1)).filter (fun m => d ∣ m ∧ d ∣ (n - m))
      = (Finset.Icc 1 (n - 1)).filter (fun m => d ∣ m) := by
  classical
  apply Finset.filter_congr
  intro m hm
  have hmn1 := (Finset.mem_Icc.mp hm).2
  have hmn : m ≤ n := by omega
  exact cond_iff_dvd_m hd hmn

/-- Helper: `Icc 1 N = Ioc 0 N` on `ℕ`. -/
private lemma icc_one_eq_ioc_zero (N : ℕ) :
    Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext k
  simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.lt_iff_add_one_le]

/-- Helper: count of multiples of `d` in `[1, N]` equals `N/d`. -/
private lemma card_multiples_in_icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
  classical
  rw [icc_one_eq_ioc_zero]
  exact Nat.Ioc_filter_dvd_card_eq_div N d

/-- Helper: when `d ∣ n` and `0 < d`, we have `(n - 1)/d = n/d - 1`
(with natural-number subtraction). -/
private lemma sub_one_div_eq_div_sub_one
    {n d : ℕ} (hd : d ∣ n) (hd_pos : 0 < d) :
    (n - 1) / d = n / d - 1 := by
  obtain ⟨k, rfl⟩ := hd
  -- Goal: (d * k - 1) / d = d * k / d - 1
  rw [Nat.mul_div_cancel_left k hd_pos]
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · -- k = 0: both sides 0.
    subst hk0; simp
  · -- k ≥ 1.
    -- Rewrite `d * k - 1 = d * (k - 1) + (d - 1)`.
    have hd1 : 1 ≤ d := hd_pos
    have hk1 : 1 ≤ k := hk_pos
    have hdk_eq : d * k - 1 = d * (k - 1) + (d - 1) := by
      -- d * k = d * (k - 1) + d (since k ≥ 1).
      have h_split : d * k = d * (k - 1) + d := by
        have : d * k = d * ((k - 1) + 1) := by
          congr 1; omega
        rw [this, Nat.mul_add, Nat.mul_one]
      omega
    rw [hdk_eq]
    -- (d * (k - 1) + (d - 1)) / d = (k - 1) + (d - 1)/d = (k - 1) + 0.
    have h_div : (d * (k - 1) + (d - 1)) / d = (k - 1) + (d - 1) / d :=
      Nat.mul_add_div hd_pos (k - 1) (d - 1)
    rw [h_div]
    have hd1_lt : d - 1 < d := Nat.sub_lt hd_pos Nat.one_pos
    have h_small_div : (d - 1) / d = 0 := Nat.div_eq_of_lt hd1_lt
    rw [h_small_div, Nat.add_zero]

/-- For `d ∣ n`, the paired count equals `(n-1)/d`, which is `n/d - 1`
in `ℕ`-truncated arithmetic.  The signed (integer) discrepancy from
`n / d - 1` is therefore in `{0, 1}` (the `1` arising only when
`n = 0`, where `↑(n/d - 1) = 0` but `↑n/↑d - 1 = -1`).  In all cases
`Int.natAbs` of the signed discrepancy is `≤ 1`. -/
theorem goldbachPairCount_split_eq_div_of_dvd
    (n d : ℕ) (hd : d ∣ n) (hd_pos : 0 < d) :
    Int.natAbs (goldbachPairCount_split n d - (n / d - 1)) ≤ 1 := by
  classical
  -- Exact equality `count = n/d - 1` in `ℕ` (natural subtraction).
  have h_eq : goldbachPairCount_split n d = n / d - 1 := by
    unfold goldbachPairCount_split
    rw [filter_paired_eq_filter_dvd n d hd]
    rw [card_multiples_in_icc (n - 1) d]
    exact sub_one_div_eq_div_sub_one hd hd_pos
  rw [h_eq]
  -- The goal is in `ℤ`: `(↑(n/d - 1) - (↑n/↑d - 1)).natAbs ≤ 1`.
  -- Case on whether `n / d = 0` or `n / d ≥ 1`.
  rcases Nat.eq_zero_or_pos (n / d) with hnd0 | hnd_pos
  · -- `n / d = 0`.  Then `n / d - 1 = 0` in `ℕ`, so `↑(n/d - 1) = 0`.
    -- Also `↑n / ↑d = ↑(n/d) = 0`, so `↑n/↑d - 1 = -1`.
    -- Thus the inner expression is `0 - (-1) = 1`, `natAbs = 1 ≤ 1`.
    have h_int : (↑n : ℤ) / (↑d : ℤ) = ((n / d : ℕ) : ℤ) := by
      exact_mod_cast (Int.natCast_div n d).symm
    rw [hnd0]
    simp [h_int, hnd0]
  · -- `n / d ≥ 1`.  Then `n / d - 1` in `ℕ` equals `n/d - 1` (no truncation).
    -- `↑(n/d - 1) = ↑(n/d) - 1 = ↑n/↑d - 1`, so the difference is `0`.
    have h_int : (↑n : ℤ) / (↑d : ℤ) = ((n / d : ℕ) : ℤ) := by
      exact_mod_cast (Int.natCast_div n d).symm
    have h_cast : ((n / d - 1 : ℕ) : ℤ) = ((n / d : ℕ) : ℤ) - 1 := by
      have : n / d = (n / d - 1) + 1 := (Nat.sub_add_cancel hnd_pos).symm
      have := congrArg (fun k : ℕ => (k : ℤ)) this
      push_cast at this
      linarith
    rw [h_cast, h_int]
    simp

end PathCPairedCRTSplitByGCD
end Gdbh
