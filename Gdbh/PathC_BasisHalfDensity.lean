/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P7-T1 (Phase 7 / Path C — Schnirelmann basis half-density theorem)
-/
import Gdbh.PathC_SchnirelmannDensity
import Gdbh.PathC_AdditionTheorem
import Gdbh.PathC_KGoldbach

/-!
# Path C — Schnirelmann's basis half-density theorem (Phase 7 closure)

This file proves **unconditionally** the named open `Prop`
`Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity` introduced in
`Gdbh/PathC_KGoldbach.lean`.  The result is the classical "second-step"
half-density Schnirelmann basis theorem:

```
  σA ≥ 1/2  ∧  A 0  ∧  A 1  ⇒  ∀ n ≥ 1,  n ∈ A + A.
```

The proof is the standard pigeonhole argument:

* `S  := {a ∈ A : a ≤ n} ⊆ [0, n]` has `|S| ≥ countingUpTo A n + 1`
  (since `0 ∈ A`).
* `S' := { n - a : a ∈ S } ⊆ [0, n]` has `|S'| = |S|` (the map
  `a ↦ n - a` is injective on `[0, n]`).
* `σA ≥ 1/2` gives `countingUpTo A n ≥ n/2`, so
  `|S| + |S'| ≥ 2 · countingUpTo A n + 2 ≥ n + 2 > n + 1 = |[0, n]|`.
* Pigeonhole: `S ∩ S' ≠ ∅`, witnessing `a ∈ A, b ∈ A` with `a + b = n`.

The deliverable is the unconditional theorem
`schnirelmannBasisHalfDensity_holds : SchnirelmannBasisHalfDensity`.
-/

namespace Gdbh
namespace PathCBasisHalfDensity

open scoped BigOperators

/-! ## Half-density implies near-balanced counting. -/

/-- From `σA ≥ 1/2`, the count of `A ∩ [1, n]` is at least `n / 2`
(as real numbers). -/
lemma countingUpTo_ge_half_of_density_half
    (A : ℕ → Prop) [DecidablePred A]
    (hσ : (1 : ℝ) / 2 ≤ schnirelmannDensity A) :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * (countingUpTo A n : ℝ) := by
  intro n hn
  -- σA ≤ schnirelmannTerm A n = countingUpTo A n / n (for n ≥ 1).
  have hb := bddBelow_range_schnirelmannTerm A
  have h_le_term : schnirelmannDensity A ≤ schnirelmannTerm A n := ciInf_le hb n
  have h_term_eq : schnirelmannTerm A n = (countingUpTo A n : ℝ) / n := by
    unfold schnirelmannTerm; simp [hn]
  rw [h_term_eq] at h_le_term
  have hσ_le : (1 : ℝ) / 2 ≤ (countingUpTo A n : ℝ) / n := le_trans hσ h_le_term
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Multiply both sides by 2 * n > 0.
  have h_mul : (1 : ℝ) / 2 * n ≤ (countingUpTo A n : ℝ) / n * n := by
    exact mul_le_mul_of_nonneg_right hσ_le (le_of_lt hn_pos)
  rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)] at h_mul
  linarith

/-- As a `ℕ` inequality: `n ≤ 2 * countingUpTo A n`. -/
lemma countingUpTo_two_mul_ge_of_density_half
    (A : ℕ → Prop) [DecidablePred A]
    (hσ : (1 : ℝ) / 2 ≤ schnirelmannDensity A)
    (n : ℕ) (hn : 1 ≤ n) :
    n ≤ 2 * countingUpTo A n := by
  have h := countingUpTo_ge_half_of_density_half A hσ n hn
  have h' : (n : ℝ) ≤ ((2 * countingUpTo A n : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast h'

/-! ## The pigeonhole step. -/

/-- The Finset of `a ∈ A` with `a ≤ n`. -/
private def AfinSet (A : ℕ → Prop) [DecidablePred A] (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter A

/-- When `A 0`, the `AfinSet` cardinality is at least `countingUpTo A n + 1`. -/
private lemma AfinSet_card_ge (A : ℕ → Prop) [DecidablePred A]
    (hA0 : A 0) (n : ℕ) :
    countingUpTo A n + 1 ≤ (AfinSet A n).card := by
  classical
  -- AfinSet A n = (range (n+1)).filter A
  -- countingUpTo A n = ((range (n+1)).filter (fun k => 1 ≤ k ∧ A k)).card
  -- The first set is the disjoint union of {0} and the second.
  unfold AfinSet countingUpTo
  -- Let S1 = (range (n+1)).filter A, S2 = (range (n+1)).filter (fun k => 1 ≤ k ∧ A k)
  -- We have S1 = {0} ∪ S2 (disjoint), so |S1| = 1 + |S2|.
  set S1 := (Finset.range (n + 1)).filter A
  set S2 := (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ A k)
  have h_zero_mem : (0 : ℕ) ∈ S1 := by
    refine Finset.mem_filter.mpr ⟨?_, hA0⟩
    exact Finset.mem_range.mpr (Nat.succ_pos _)
  have h_zero_not_S2 : (0 : ℕ) ∉ S2 := by
    intro h
    rcases Finset.mem_filter.mp h with ⟨_, h1, _⟩
    exact absurd h1 (by norm_num)
  have h_S2_sub_S1 : S2 ⊆ S1 := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, _, hkA⟩
    exact Finset.mem_filter.mpr ⟨hkr, hkA⟩
  -- S1 = insert 0 S2 (since {0} ⊆ S1 and S1 ⊆ {0} ∪ S2).
  have h_S1_eq : S1 = insert 0 S2 := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkr, hkA⟩
      rw [Finset.mem_range] at hkr
      by_cases hk0 : k = 0
      · rw [hk0]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkr, ?_, hkA⟩
        exact Nat.one_le_iff_ne_zero.mpr hk0
    · intro hk
      rcases Finset.mem_insert.mp hk with hk0 | hkS2
      · rw [hk0]; exact h_zero_mem
      · rcases Finset.mem_filter.mp hkS2 with ⟨hkr, _, hkA⟩
        exact Finset.mem_filter.mpr ⟨hkr, hkA⟩
  rw [h_S1_eq, Finset.card_insert_of_notMem h_zero_not_S2]

/-- All elements of `AfinSet A n` are at most `n`. -/
private lemma AfinSet_subset_range (A : ℕ → Prop) [DecidablePred A] (n : ℕ) :
    AfinSet A n ⊆ Finset.range (n + 1) :=
  Finset.filter_subset _ _

/-- The "reflection" of `AfinSet A n` through `n`: the set `{n - a : a ∈ AfinSet A n}`. -/
private def AfinSetRefl (A : ℕ → Prop) [DecidablePred A] (n : ℕ) : Finset ℕ :=
  (AfinSet A n).image (fun a => n - a)

/-- The reflected set has the same cardinality as the original, by injectivity. -/
private lemma AfinSetRefl_card (A : ℕ → Prop) [DecidablePred A] (n : ℕ) :
    (AfinSetRefl A n).card = (AfinSet A n).card := by
  unfold AfinSetRefl
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  simp only at hab
  -- a, b ∈ AfinSet A n means a, b ∈ Finset.range (n + 1), so a ≤ n and b ≤ n.
  rcases Finset.mem_filter.mp ha with ⟨har, _⟩
  rcases Finset.mem_filter.mp hb with ⟨hbr, _⟩
  rw [Finset.mem_range] at har hbr
  have ha_le : a ≤ n := by omega
  have hb_le : b ≤ n := by omega
  -- n - a = n - b with a, b ≤ n implies a = b.
  omega

/-- The reflected set is a subset of `[0, n]`. -/
private lemma AfinSetRefl_subset_range (A : ℕ → Prop) [DecidablePred A] (n : ℕ) :
    AfinSetRefl A n ⊆ Finset.range (n + 1) := by
  intro x hx
  unfold AfinSetRefl at hx
  rcases Finset.mem_image.mp hx with ⟨a, _, hax⟩
  rw [Finset.mem_range]
  omega

/-- **Pigeonhole step**: under `σA ≥ 1/2` and `A 0`, the sets
`AfinSet A n` and `AfinSetRefl A n` have nonempty intersection for
every `n ≥ 1`. -/
private lemma AfinSet_inter_AfinSetRefl_nonempty
    (A : ℕ → Prop) [DecidablePred A]
    (hA0 : A 0)
    (hσ : (1 : ℝ) / 2 ≤ schnirelmannDensity A)
    (n : ℕ) (hn : 1 ≤ n) :
    (AfinSet A n ∩ AfinSetRefl A n).Nonempty := by
  classical
  set S := AfinSet A n with hS_def
  set S' := AfinSetRefl A n with hS'_def
  -- |S| ≥ countingUpTo A n + 1
  have h_card_S : countingUpTo A n + 1 ≤ S.card := AfinSet_card_ge A hA0 n
  -- |S'| = |S|
  have h_card_S' : S'.card = S.card := AfinSetRefl_card A n
  -- n ≤ 2 * countingUpTo A n
  have h_count : n ≤ 2 * countingUpTo A n :=
    countingUpTo_two_mul_ge_of_density_half A hσ n hn
  -- So |S| + |S'| = 2|S| ≥ 2 (countingUpTo A n + 1) = 2 * countingUpTo A n + 2 ≥ n + 2.
  have h_sum_ge : n + 2 ≤ S.card + S'.card := by
    rw [h_card_S']
    omega
  -- |S ∪ S'| ≤ n + 1 (both subsets of range (n+1)).
  have h_union_sub : S ∪ S' ⊆ Finset.range (n + 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact AfinSet_subset_range A n h
    · exact AfinSetRefl_subset_range A n h
  have h_union_card : (S ∪ S').card ≤ n + 1 := by
    have := Finset.card_le_card h_union_sub
    simpa [Finset.card_range] using this
  -- |S ∩ S'| = |S| + |S'| - |S ∪ S'| ≥ (n + 2) - (n + 1) = 1 > 0.
  have h_union_inter := Finset.card_union_add_card_inter S S'
  have h_inter_pos : 0 < (S ∩ S').card := by omega
  exact Finset.card_pos.mp h_inter_pos

/-! ## Main theorem. -/

/-- **Schnirelmann's basis half-density theorem** (unconditional closure of
`Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity`).

If `A ⊆ ℕ` contains `0` and `1` and has Schnirelmann density at least
`1/2`, then `A + A` contains every positive integer. -/
theorem schnirelmannBasisHalfDensity_holds :
    Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity := by
  intro A _ hA0 _hA1 hσ n hn
  -- Pigeonhole: find x ∈ AfinSet A n ∩ AfinSetRefl A n.
  obtain ⟨x, hx⟩ := AfinSet_inter_AfinSetRefl_nonempty A hA0 hσ n hn
  rw [Finset.mem_inter] at hx
  rcases hx with ⟨hxS, hxS'⟩
  -- x ∈ AfinSet A n ⇒ A x and x ≤ n.
  rcases Finset.mem_filter.mp hxS with ⟨hxr, hxA⟩
  rw [Finset.mem_range] at hxr
  have hx_le : x ≤ n := by omega
  -- x ∈ AfinSetRefl A n ⇒ ∃ b ∈ AfinSet A n, n - b = x.
  unfold AfinSetRefl at hxS'
  rcases Finset.mem_image.mp hxS' with ⟨b, hbS, hbx⟩
  rcases Finset.mem_filter.mp hbS with ⟨hbr, hbA⟩
  rw [Finset.mem_range] at hbr
  have hb_le : b ≤ n := by omega
  -- Now x = n - b, with A x and A b.  Show x + b = n.
  have h_sum : x + b = n := by omega
  -- Conclude n ∈ sumset A A.
  rw [sumset_iff]
  exact ⟨x, b, hxA, hbA, h_sum⟩

end PathCBasisHalfDensity
end Gdbh
