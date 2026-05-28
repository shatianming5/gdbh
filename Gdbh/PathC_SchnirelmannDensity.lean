import Mathlib

/-!
# Path C — Schnirelmann density: definitions and basic lemmas

This file is the foundation of Path C (Schnirelmann + additive combinatorics)
to binary Goldbach.  It is completely independent of Path A (von Mangoldt /
circle method) and only depends on mathlib.

## Main definitions

* `Gdbh.countingUpTo A n` — number of `k ∈ [1, n]` with `A k`.
* `Gdbh.schnirelmannDensity A` — Schnirelmann density of `A`, defined as
  `iInf` of `countingUpTo A n / n` over `n ≥ 1` (with a sentinel value `1`
  at `n = 0` so the `iInf` is over the same bounded set `[0,1]`).

## Main lemmas (all axiom-clean: `Classical.choice, Quot.sound, propext`)

* `schnirelmannDensity_nonneg` : `0 ≤ schnirelmannDensity A`.
* `schnirelmannDensity_le_one`  : `schnirelmannDensity A ≤ 1`.
* `schnirelmannDensity_eq_zero_of_one_not_mem` : `¬ A 1 →
  schnirelmannDensity A = 0`.
* `schnirelmannDensity_le_of_counting_le` : pointwise bound
  `countingUpTo A n ≤ C * n` (for all `n ≥ 1`) gives
  `schnirelmannDensity A ≤ C`.
* `schnirelmannDensity_ge_of_counting_ge` : pointwise bound
  `c * n ≤ countingUpTo A n` (for all `n ≥ 1`) gives
  `c ≤ schnirelmannDensity A`.
* `schnirelmannDensity_mono` : if `A ⊆ B` (i.e. `∀ k, A k → B k`),
  then `schnirelmannDensity A ≤ schnirelmannDensity B`.
-/

namespace Gdbh

open scoped BigOperators

/-- Counting function: number of `k ∈ [1, n]` with `A k`. -/
def countingUpTo (A : ℕ → Prop) [DecidablePred A] (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ A k)).card

/-- The summand of the Schnirelmann infimum: `countingUpTo A n / n` for
`n ≥ 1`, and the sentinel value `1` for `n = 0`. -/
noncomputable def schnirelmannTerm (A : ℕ → Prop) [DecidablePred A] (n : ℕ) : ℝ :=
  if 1 ≤ n then (countingUpTo A n : ℝ) / n else 1

/-- The Schnirelmann density of a set of naturals.

We define it as the infimum over all `n` of `countingUpTo A n / n` when `n ≥ 1`,
and `1` when `n = 0`.  The constant value at `n = 0` is harmless: all
`countingUpTo A n / n` for `n ≥ 1` lie in `[0, 1]`, so the infimum is the same
as the genuine `iInf` over `n ≥ 1` (and is automatically nonneg / ≤ 1). -/
noncomputable def schnirelmannDensity (A : ℕ → Prop) [DecidablePred A] : ℝ :=
  iInf (schnirelmannTerm A)

section Basic

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- Each term in the Schnirelmann infimum is nonneg. -/
lemma schnirelmannTerm_nonneg (n : ℕ) : 0 ≤ schnirelmannTerm A n := by
  unfold schnirelmannTerm
  by_cases h : 1 ≤ n
  · simp only [h, if_true]
    have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have hc : (0 : ℝ) ≤ (countingUpTo A n : ℝ) := by exact_mod_cast Nat.zero_le _
    exact div_nonneg hc hn
  · simp [h]

/-- `countingUpTo A n ≤ n` (every counted element is in `{1, …, n}`). -/
lemma countingUpTo_le (n : ℕ) : countingUpTo A n ≤ n := by
  classical
  have hsub : (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ A k) ⊆
      (Finset.range (n + 1)).erase 0 := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, hk1, _⟩
    refine Finset.mem_erase.mpr ⟨?_, hkr⟩
    exact Nat.one_le_iff_ne_zero.mp hk1
  have hcard_le :
      ((Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ A k)).card ≤
        ((Finset.range (n + 1)).erase 0).card :=
    Finset.card_le_card hsub
  have herase : ((Finset.range (n + 1)).erase 0).card = n := by
    have hmem : (0 : ℕ) ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    have := Finset.card_erase_of_mem hmem
    simp [this]
  simpa [countingUpTo, herase] using hcard_le

/-- Each term in the Schnirelmann infimum is `≤ 1`. -/
lemma schnirelmannTerm_le_one (n : ℕ) : schnirelmannTerm A n ≤ 1 := by
  unfold schnirelmannTerm
  by_cases h : 1 ≤ n
  · simp only [h, if_true]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast h
    have hcount_le_r : (countingUpTo A n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast countingUpTo_le A n
    rw [div_le_one hn_pos]
    exact hcount_le_r
  · simp [h]

/-- `schnirelmannTerm` has bounded-below range (by `0`). -/
lemma bddBelow_range_schnirelmannTerm :
    BddBelow (Set.range (schnirelmannTerm A)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact schnirelmannTerm_nonneg A n

/-- The Schnirelmann density is bounded below by `0`. -/
theorem schnirelmannDensity_nonneg :
    0 ≤ schnirelmannDensity A := by
  refine le_ciInf ?_
  intro n
  exact schnirelmannTerm_nonneg A n

/-- The Schnirelmann density is bounded above by `1`. -/
theorem schnirelmannDensity_le_one :
    schnirelmannDensity A ≤ 1 := by
  -- the `n = 0` branch evaluates to `1`.
  have hb := bddBelow_range_schnirelmannTerm A
  have hle : schnirelmannDensity A ≤ schnirelmannTerm A 0 :=
    ciInf_le hb 0
  have h0 : schnirelmannTerm A 0 = 1 := by
    unfold schnirelmannTerm
    simp
  exact hle.trans (le_of_eq h0)

/-- The `n = 1` term equals `countingUpTo A 1` (since dividing by `1`). -/
lemma schnirelmannTerm_one : schnirelmannTerm A 1 = (countingUpTo A 1 : ℝ) := by
  unfold schnirelmannTerm
  simp

/-- If `1 ∉ A`, then `countingUpTo A 1 = 0`. -/
lemma countingUpTo_one_eq_zero_of_one_not_mem (h : ¬ A 1) :
    countingUpTo A 1 = 0 := by
  classical
  have : (Finset.range (1 + 1)).filter (fun k => 1 ≤ k ∧ A k) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, hk1, hkA⟩
    have hkle : k ≤ 1 := by
      have := Finset.mem_range.mp hkr
      omega
    interval_cases k
    · exact h hkA
  simp [countingUpTo, this]

/-- If `1 ∉ A`, the Schnirelmann density is `0`. -/
theorem schnirelmannDensity_eq_zero_of_one_not_mem (h : ¬ A 1) :
    schnirelmannDensity A = 0 := by
  refine le_antisymm ?_ (schnirelmannDensity_nonneg A)
  have hb := bddBelow_range_schnirelmannTerm A
  have hle : schnirelmannDensity A ≤ schnirelmannTerm A 1 :=
    ciInf_le hb 1
  have hcount1 : countingUpTo A 1 = 0 :=
    countingUpTo_one_eq_zero_of_one_not_mem A h
  have h1 : schnirelmannTerm A 1 = 0 := by
    rw [schnirelmannTerm_one]
    exact_mod_cast hcount1
  exact hle.trans (le_of_eq h1)

/-- `countingUpTo A 1 ≤ 1` (only `1` itself can be in the count). -/
lemma countingUpTo_one_le : countingUpTo A 1 ≤ 1 := by
  have := countingUpTo_le A 1
  exact this

/-- Upper bound: if `countingUpTo A n ≤ C * n` for all `n ≥ 1`,
then `schnirelmannDensity A ≤ C`. -/
theorem schnirelmannDensity_le_of_counting_le {C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (countingUpTo A n : ℝ) ≤ C * n) :
    schnirelmannDensity A ≤ C := by
  -- pick the `n = 1` term and bound it by `C`.
  have hb := bddBelow_range_schnirelmannTerm A
  have hle : schnirelmannDensity A ≤ schnirelmannTerm A 1 :=
    ciInf_le hb 1
  have h1 := h 1 (le_refl 1)
  have h1' : (countingUpTo A 1 : ℝ) ≤ C := by simpa using h1
  have hterm : schnirelmannTerm A 1 = (countingUpTo A 1 : ℝ) :=
    schnirelmannTerm_one A
  exact hle.trans (hterm.le.trans h1')

/-- Lower bound: if `c * n ≤ countingUpTo A n` for all `n ≥ 1`,
then `c ≤ schnirelmannDensity A`. -/
theorem schnirelmannDensity_ge_of_counting_ge {c : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → c * n ≤ (countingUpTo A n : ℝ)) :
    c ≤ schnirelmannDensity A := by
  refine le_ciInf ?_
  intro n
  unfold schnirelmannTerm
  by_cases hn : 1 ≤ n
  · simp only [hn, if_true]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn_pos]
    exact h n hn
  · simp only [hn, if_false]
    -- `n = 0`; deduce `c ≤ 1` via the `n = 1` bound.
    have h1 := h 1 (le_refl 1)
    have hc_le_count1 : c ≤ (countingUpTo A 1 : ℝ) := by simpa using h1
    have hcount1 : (countingUpTo A 1 : ℝ) ≤ 1 := by
      exact_mod_cast countingUpTo_one_le A
    linarith

/-- Monotonicity of `countingUpTo` in the underlying predicate. -/
lemma countingUpTo_mono (h : ∀ k, A k → B k) (n : ℕ) :
    countingUpTo A n ≤ countingUpTo B n := by
  classical
  unfold countingUpTo
  apply Finset.card_le_card
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkr, hk1, hkA⟩
  exact Finset.mem_filter.mpr ⟨hkr, hk1, h k hkA⟩

/-- Monotonicity of `schnirelmannTerm` in the underlying predicate. -/
lemma schnirelmannTerm_mono (h : ∀ k, A k → B k) (n : ℕ) :
    schnirelmannTerm A n ≤ schnirelmannTerm B n := by
  unfold schnirelmannTerm
  by_cases hn : 1 ≤ n
  · simp only [hn, if_true]
    have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have hcount_le_r : (countingUpTo A n : ℝ) ≤ (countingUpTo B n : ℝ) := by
      exact_mod_cast countingUpTo_mono A B h n
    exact div_le_div_of_nonneg_right hcount_le_r hn_nonneg
  · simp [hn]

/-- Monotonicity of Schnirelmann density in the underlying set. -/
theorem schnirelmannDensity_mono (h : ∀ k, A k → B k) :
    schnirelmannDensity A ≤ schnirelmannDensity B := by
  have hb := bddBelow_range_schnirelmannTerm A
  exact ciInf_mono hb (schnirelmannTerm_mono A B h)

end Basic

end Gdbh
