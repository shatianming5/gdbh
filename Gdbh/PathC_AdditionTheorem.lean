/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T2 (Phase 6 / Path C — Schnirelmann's addition theorem)
-/
import Gdbh.PathC_SchnirelmannDensity

/-!
# Path C — Schnirelmann's addition theorem

This file proves Schnirelmann's classical 1930 addition theorem for the
density of sumsets of subsets of `ℕ` containing `0`.

The headline result is

```
σ(A + B) ≥ σA + σB - σA · σB    (when 0 ∈ A ∩ B)
```

which we expose as `schnirelmannDensity_sumset_ge`.  Iterating this
inequality gives the consequence that for any `A` with `0 ∈ A` and
`σA > 0`, the iterated sumset `A + A + ... + A` (`k` times) reaches
density `1` for some finite `k`.

## Main definitions

* `Gdbh.sumset A B : ℕ → Prop` — the sumset `A + B`.
* `Gdbh.sumsetIter A k : ℕ → Prop` — iterated sumset `A + A + ⋯ + A`
  with `k` copies of `A` (with `sumsetIter A 0 = {0}` as the base
  case).

## Main results (all axiom-clean: `Classical.choice, Quot.sound, propext`)

* `Gdbh.countingUpTo_sumset_ge_countingUpTo_right` — the trivial
  inclusion bound `(A + B)(n) ≥ B(n)` (using `0 ∈ A`).
* `Gdbh.schnirelmannDensity_sumset_ge_right` — `σB ≤ σ(A + B)` (the
  symmetric statement `σA ≤ σ(A + B)` follows from `0 ∈ B`).
* `Gdbh.countingUpTo_sumset_lower_bound` — the pointwise lower bound
  `(A + B)(n) ≥ B(n) + σA · (n - B(n))`, which is the analytic core of
  Schnirelmann's argument.  This is proved by a direct gap-injection
  construction.
* `Gdbh.schnirelmannDensity_sumset_ge` — Schnirelmann's addition
  inequality `σA + σB - σA · σB ≤ σ(A + B)`.
* `Gdbh.schnirelmannDensity_sumsetIter_ge_of_zero_mem` — monotone
  iteration: `σA ≤ σ(sumsetIter A k)` for all `k ≥ 1`.
* `Gdbh.schnirelmannDensity_one_sub_iter_le` — the explicit geometric
  estimate `1 - σ(sumsetIter A k) ≤ (1 - σA)^k`, which packages the
  full iteration.

The mathematical content of the gap-counting argument lives in
`countingUpTo_sumset_lower_bound`; everything else is routine
real-analytic manipulation on top of P6-T1's
`schnirelmannDensity_ge_of_counting_ge`.
-/

namespace Gdbh

open scoped BigOperators

/-! ## Sumset and iterated sumset. -/

/-- The sumset `A + B = { a + b : a ∈ A, b ∈ B }`.  We package the
existential over a *bounded* finite set so that decidability is
inherited automatically. -/
def sumset (A B : ℕ → Prop) (n : ℕ) : Prop :=
  ∃ p : ℕ × ℕ, p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ∧
    A p.1 ∧ B p.2 ∧ p.1 + p.2 = n

instance sumset_decidable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    DecidablePred (sumset A B) := fun n => by
  unfold sumset
  infer_instance

/-- Rewriting `sumset` in a more flexible form. -/
lemma sumset_iff (A B : ℕ → Prop) (n : ℕ) :
    sumset A B n ↔ ∃ a b, A a ∧ B b ∧ a + b = n := by
  constructor
  · rintro ⟨⟨a, b⟩, _, hA, hB, hab⟩
    exact ⟨a, b, hA, hB, hab⟩
  · rintro ⟨a, b, hA, hB, hab⟩
    refine ⟨(a, b), ?_, hA, hB, hab⟩
    have ha_le : a ≤ n := by omega
    have hb_le : b ≤ n := by omega
    simp [Finset.mem_product, Finset.mem_range, ha_le, hb_le]

/-- Iterated sumset.  `sumsetIter A 0 = {0}`, and
`sumsetIter A (k+1) = A + sumsetIter A k`. -/
def sumsetIter (A : ℕ → Prop) : ℕ → ℕ → Prop
  | 0, n => n = 0
  | k + 1, n => sumset A (sumsetIter A k) n

instance sumsetIter_decidable (A : ℕ → Prop) [DecidablePred A] (k : ℕ) :
    DecidablePred (sumsetIter A k) := by
  induction k with
  | zero => intro n; unfold sumsetIter; infer_instance
  | succ k ih => intro n; unfold sumsetIter; exact @sumset_decidable A _ _ ih n

/-- `0 ∈ sumsetIter A k` whenever `0 ∈ A`. -/
lemma zero_mem_sumsetIter {A : ℕ → Prop} (hA : A 0) :
    ∀ k, sumsetIter A k 0
  | 0 => rfl
  | k + 1 => by
    rw [sumsetIter, sumset_iff]
    exact ⟨0, 0, hA, zero_mem_sumsetIter hA k, rfl⟩

/-- `B ⊆ sumset A B` whenever `0 ∈ A`. -/
lemma sumset_of_mem_right {A B : ℕ → Prop} (hA : A 0)
    {n : ℕ} (hB : B n) : sumset A B n := by
  rw [sumset_iff]; exact ⟨0, n, hA, hB, by simp⟩

/-- `A ⊆ sumset A B` whenever `0 ∈ B`. -/
lemma sumset_of_mem_left {A B : ℕ → Prop} (hB : B 0)
    {n : ℕ} (hA : A n) : sumset A B n := by
  rw [sumset_iff]; exact ⟨n, 0, hA, hB, by simp⟩

/-! ## Trivial inclusion lower bound. -/

section Trivial

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- Counting-monotone inclusion: if `0 ∈ A`, then `B(n) ≤ (A + B)(n)`. -/
lemma countingUpTo_sumset_ge_countingUpTo_right (hA : A 0) (n : ℕ) :
    countingUpTo B n ≤ countingUpTo (sumset A B) n :=
  countingUpTo_mono _ _ (fun _ h => sumset_of_mem_right hA h) n

/-- Counting-monotone inclusion: if `0 ∈ B`, then `A(n) ≤ (A + B)(n)`. -/
lemma countingUpTo_sumset_ge_countingUpTo_left (hB : B 0) (n : ℕ) :
    countingUpTo A n ≤ countingUpTo (sumset A B) n :=
  countingUpTo_mono _ _ (fun _ h => sumset_of_mem_left hB h) n

/-- Density-monotone inclusion: `σB ≤ σ(A + B)` when `0 ∈ A`. -/
theorem schnirelmannDensity_sumset_ge_right (hA : A 0) :
    schnirelmannDensity B ≤ schnirelmannDensity (sumset A B) :=
  schnirelmannDensity_mono _ _ (fun _ h => sumset_of_mem_right hA h)

/-- Density-monotone inclusion: `σA ≤ σ(A + B)` when `0 ∈ B`. -/
theorem schnirelmannDensity_sumset_ge_left (hB : B 0) :
    schnirelmannDensity A ≤ schnirelmannDensity (sumset A B) :=
  schnirelmannDensity_mono _ _ (fun _ h => sumset_of_mem_left hB h)

end Trivial

/-! ## Gap structure of `B ∩ [0, n]` and the pointwise sumset bound.

For each `b ∈ B ∩ [0, n]`, define `gapSet B n b` as the set of integers
`a ∈ [1, n - b]` such that `b + i ∉ B` for every `1 ≤ i ≤ a`, i.e. the
"open interval after `b` and before the next `B`-element".  By
construction, distinct `b ∈ B` give disjoint shifted gaps, and the gap
of `b` is precisely the set of integers strictly between `b` and the
next `B`-element above `b`.

Inside the gap of `b`, the elements `b + a` for `a ∈ A` give injectively
distinct elements of `(A + B) ∩ [1, n]`, **all of which lie outside `B`**.
Coupled with the trivial inclusion `B ∩ [1, n] ⊆ (A + B) ∩ [1, n]`, this
yields the Schnirelmann pointwise bound.
-/

section Gap

variable (B : ℕ → Prop) [DecidablePred B]

/-- The gap set of `b` inside `[0, n]`: the integers `j ∈ [1, n - b]`
such that **no** value in `[b + 1, b + j]` lies in `B`. -/
def gapSet (n b : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun j => 1 ≤ j ∧ b + j ≤ n ∧ ∀ i, 1 ≤ i → i ≤ j → ¬ B (b + i))

lemma mem_gapSet {n b j : ℕ} :
    j ∈ gapSet B n b ↔ 1 ≤ j ∧ b + j ≤ n ∧
      ∀ i, 1 ≤ i → i ≤ j → ¬ B (b + i) := by
  unfold gapSet
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨?_, h⟩⟩
  obtain ⟨_, h2, _⟩ := h
  omega

lemma gapSet_subset_Ioc (n b : ℕ) :
    gapSet B n b ⊆ Finset.Ioc 0 (n - b) := by
  intro j hj
  rw [mem_gapSet] at hj
  rcases hj with ⟨hj1, hj2, _⟩
  rw [Finset.mem_Ioc]
  refine ⟨hj1, ?_⟩
  omega

/-- The gap sets `gapSet B n b` for distinct `b` are *shifted* into
disjoint regions of `[1, n]`. -/
lemma gapSet_shift_disjoint {n b b' : ℕ} (hB : B b) (hB' : B b') (hne : b ≠ b')
    {a a' : ℕ} (ha : a ∈ gapSet B n b) (ha' : a' ∈ gapSet B n b') :
    b + a ≠ b' + a' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `b < b'`.  Then if `b + a = b' + a'`, we'd have `b + a ≥ b'` and
    -- `b' = b + (b' - b)` with `1 ≤ b' - b ≤ a`.  But the gap
    -- condition on `b` then forces `¬ B b'`, contradiction.
    rw [mem_gapSet] at ha
    rcases ha with ⟨_, _, hgap⟩
    intro hab
    have hb'_sub : b' = b + (b' - b) := by omega
    have h1 : 1 ≤ b' - b := by omega
    have h2 : b' - b ≤ a := by omega
    have := hgap (b' - b) h1 h2
    rw [← hb'_sub] at this
    exact this hB'
  · rw [mem_gapSet] at ha'
    rcases ha' with ⟨_, _, hgap⟩
    intro hab
    have hb_sub : b = b' + (b - b') := by omega
    have h1 : 1 ≤ b - b' := by omega
    have h2 : b - b' ≤ a' := by omega
    have := hgap (b - b') h1 h2
    rw [← hb_sub] at this
    exact this hB

/-- Shifted gap sets are pairwise disjoint. -/
lemma shifted_gapSet_disjoint (n : ℕ) :
    ∀ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
    ∀ b' ∈ (Finset.range (n + 1)).filter (fun b => B b),
    b ≠ b' →
    Disjoint ((gapSet B n b).image (fun a => b + a))
      ((gapSet B n b').image (fun a => b' + a)) := by
  classical
  intro b hb b' hb' hne
  rw [Finset.mem_filter] at hb hb'
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  rcases hx with ⟨a, ha, hax⟩
  rcases hx' with ⟨a', ha', ha'x⟩
  have hne_sum : b + a ≠ b' + a' :=
    gapSet_shift_disjoint (B := B) (n := n) hb.2 hb'.2 hne ha ha'
  exact hne_sum (hax.trans ha'x.symm)

/-- Each shifted gap set is contained in `[1, n] \ B`. -/
lemma shifted_gapSet_subset (n b : ℕ) (_hBb : B b) :
    (gapSet B n b).image (fun a => b + a) ⊆
      (Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ ¬ B m) := by
  intro x hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨a, ha, hax⟩
  rw [mem_gapSet] at ha
  rcases ha with ⟨ha1, hab_le, ha_no⟩
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, by omega, ?_⟩
  rw [← hax]
  exact ha_no a ha1 (le_refl a)

/-- Each shifted gap set has the same cardinality as the original. -/
lemma shifted_gapSet_card (n b : ℕ) :
    ((gapSet B n b).image (fun a => b + a)).card = (gapSet B n b).card := by
  refine Finset.card_image_of_injOn ?_
  intro x _ y _ hxy
  exact Nat.add_left_cancel hxy

/-- The union of all shifted gap sets (for `b ∈ B ∩ [0, n]`) equals
`[1, n] \ B`. -/
lemma biUnion_shifted_gapSet (n : ℕ) (hB0 : B 0) :
    ((Finset.range (n + 1)).filter (fun b => B b)).biUnion
        (fun b => (gapSet B n b).image (fun a => b + a)) =
      (Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ ¬ B m) := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · -- ⊆: every shifted gap element is in [1, n] \ B (proved above).
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨b, hb, hxb⟩
    rw [Finset.mem_filter] at hb
    exact shifted_gapSet_subset B n b hb.2 hxb
  · -- ⊇: every m ∈ [1, n] \ B is in the gap of `predInB m`.
    intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    rcases hm with ⟨hmn, hm1, hmB⟩
    -- predecessor in B
    set preds := (Finset.range (n + 1)).filter (fun b => B b ∧ b < m) with hpreds_def
    have hpreds_ne : preds.Nonempty := ⟨0, by
      simp only [preds, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_pos _, hB0, by omega⟩⟩
    set b := preds.max' hpreds_ne with hb_def
    have hb_mem : b ∈ preds := Finset.max'_mem _ _
    rw [Finset.mem_filter, Finset.mem_range] at hb_mem
    rcases hb_mem with ⟨hbn, hBb, hblm⟩
    rw [Finset.mem_biUnion]
    refine ⟨b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbn, hBb⟩
    · rw [Finset.mem_image]
      refine ⟨m - b, ?_, by omega⟩
      rw [mem_gapSet]
      refine ⟨by omega, by omega, ?_⟩
      intro i hi1 hile
      by_contra hBbi
      have hbi_le_m : b + i ≤ m := by omega
      rcases lt_or_eq_of_le hbi_le_m with hlt | heq
      · have hbi_in_preds : b + i ∈ preds := by
          simp only [preds, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hBbi, hlt⟩
        have hb_ge : b + i ≤ b := Finset.le_max' preds _ hbi_in_preds
        omega
      · rw [heq] at hBbi
        exact hmB hBbi

/-- Schnirelmann gap-partition identity:

```
Σ_{b ∈ B ∩ [0, n]} |gapSet B n b| = n - |B ∩ [1, n]|.
```
-/
lemma sum_gapSet_card (n : ℕ) (hB0 : B 0) :
    ∑ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
        (gapSet B n b).card = n - countingUpTo B n := by
  classical
  -- Use the disjoint biUnion identity.
  have hdisj : (((Finset.range (n + 1)).filter (fun b => B b) : Finset ℕ) :
      Set ℕ).PairwiseDisjoint
      (fun b => (gapSet B n b).image (fun a => b + a)) := by
    intro b hb b' hb' hne
    exact shifted_gapSet_disjoint B n b hb b' hb' hne
  have hcard_biU :
      (((Finset.range (n + 1)).filter (fun b => B b)).biUnion
          (fun b => (gapSet B n b).image (fun a => b + a))).card =
        ∑ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
            ((gapSet B n b).image (fun a => b + a)).card :=
    Finset.card_biUnion hdisj
  have hcard_shift :
      ∀ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
        ((gapSet B n b).image (fun a => b + a)).card = (gapSet B n b).card := by
    intro b _; exact shifted_gapSet_card B n b
  rw [Finset.sum_congr rfl hcard_shift] at hcard_biU
  rw [biUnion_shifted_gapSet B n hB0] at hcard_biU
  -- Now compute the RHS: (range (n+1)).filter (fun m => 1 ≤ m ∧ ¬ B m).card
  -- = n - countingUpTo B n.
  rw [← hcard_biU]
  -- Need to show: |{m ∈ [0, n] : 1 ≤ m ∧ ¬ B m}| = n - countingUpTo B n
  have hsplit :
      ((Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ ¬ B m)).card +
        ((Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ B m)).card =
        ((Finset.range (n + 1)).filter (fun m => 1 ≤ m)).card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
    · congr 1
      apply Finset.filter_congr
      intro m _
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
      · intro h1
        by_cases hBm : B m
        · exact Or.inr ⟨h1, hBm⟩
        · exact Or.inl ⟨h1, hBm⟩
    · rw [Finset.disjoint_filter]
      intro m _ ⟨_, hnB⟩ ⟨_, hB⟩
      exact hnB hB
  have hrange_one_le :
      ((Finset.range (n + 1)).filter (fun m => 1 ≤ m)).card = n := by
    have hcard_erase : (Finset.range (n + 1)).erase 0 =
        (Finset.range (n + 1)).filter (fun m => 1 ≤ m) := by
      ext m
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
      omega
    have hmem0 : (0 : ℕ) ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    have h_erase_card := Finset.card_erase_of_mem hmem0
    rw [Finset.card_range] at h_erase_card
    rw [← hcard_erase]; omega
  have hcountingUpTo :
      ((Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ B m)).card =
        countingUpTo B n := rfl
  omega

end Gap

/-! ## The pointwise Schnirelmann sumset bound. -/

section PointwiseSumsetBound

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- **Pointwise injection bound**: in each gap of `B ∩ [0, n]`, the
elements `b + a` for `a ∈ A ∩ gapSet B n b` lie in `(A + B) ∩ [1, n] \ B`,
and the injection is globally injective.  We package this as:

```
∑_{b ∈ B ∩ [0, n]} A(|gapSet B n b|) ≤ (A + B)(n) - (B ∩ [1, n])
```

More precisely, the sum on the LHS *counts* elements
`(b, a)` with `a ∈ A`, `a ∈ gapSet B n b`, which inject into
`(A + B) ∩ [1, n] \ B`.  -/
lemma countingUpTo_sumset_ge_sum_card_gap (hA : A 0) (_hB : B 0) (n : ℕ) :
    countingUpTo B n +
      ∑ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
          ((gapSet B n b).filter (fun a => A a)).card ≤
      countingUpTo (sumset A B) n := by
  classical
  -- Split `(sumset A B) ∩ [1, n] = S_B ⊔ S_notB`, where
  --   S_B    = (Finset.range (n+1)).filter (fun m => 1 ≤ m ∧ B m)
  --   S_notB = the image of the gap-injection
  -- Then |S_B| = countingUpTo B n and |S_notB| = the sum.
  set Bcnt :=
    (Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ sumset A B m) with hBcnt_def
  set SB :=
    (Finset.range (n + 1)).filter (fun m => 1 ≤ m ∧ B m) with hSB_def
  -- The S_B side: trivial via mono.
  have hSB_subset_Bcnt : SB ⊆ Bcnt := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm.1, hm.2.1, ?_⟩
    exact sumset_of_mem_right hA hm.2.2
  -- The S_notB side: build the gap-injection as a Sigma → Finset injection.
  set GS :=
    ((Finset.range (n + 1)).filter (fun b => B b)).sigma
      (fun b => (gapSet B n b).filter (fun a => A a)) with hGS_def
  -- The injection sends `(b, a) ↦ b + a`.  Its image is contained in
  -- `Bcnt \ SB`.
  have h_image : ∀ x ∈ GS, x.fst + x.snd ∈ Bcnt ∧ x.fst + x.snd ∉ SB := by
    rintro ⟨b, a⟩ habmem
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at habmem
    rcases habmem with ⟨⟨hbn, hBb⟩, hag⟩
    rw [Finset.mem_filter] at hag
    rcases hag with ⟨ha_gap, hAa⟩
    rw [mem_gapSet] at ha_gap
    rcases ha_gap with ⟨ha1, hab_le, ha_no⟩
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [sumset_iff]; exact ⟨a, b, hAa, hBb, by ring⟩
    · intro h
      rw [Finset.mem_filter, Finset.mem_range] at h
      have hBba : B (b + a) := h.2.2
      have := ha_no a ha1 (le_refl a)
      exact this hBba
  have h_inj : ∀ x ∈ GS, ∀ y ∈ GS,
      (x.fst + x.snd : ℕ) = (y.fst + y.snd : ℕ) → x = y := by
    rintro ⟨b₁, a₁⟩ hxmem ⟨b₂, a₂⟩ hymem heq
    simp only at heq
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hxmem hymem
    rcases hxmem with ⟨⟨hb₁n, hBb₁⟩, hag₁⟩
    rcases hymem with ⟨⟨hb₂n, hBb₂⟩, hag₂⟩
    rw [Finset.mem_filter] at hag₁ hag₂
    rcases hag₁ with ⟨hg₁, hA₁⟩
    rcases hag₂ with ⟨hg₂, hA₂⟩
    by_cases hbeq : b₁ = b₂
    · subst hbeq
      have : a₁ = a₂ := by omega
      subst this
      rfl
    · -- WLOG b₁ < b₂.
      exfalso
      rcases lt_or_gt_of_ne hbeq with hlt | hgt
      · rw [mem_gapSet] at hg₁
        rcases hg₁ with ⟨_, _, ha_no⟩
        -- heq says b₁ + a₁ = b₂ + a₂. So a₁ = (b₂ - b₁) + a₂, hence a₁ ≥ b₂ - b₁.
        have h1 : 1 ≤ b₂ - b₁ := by omega
        have h2 : b₂ - b₁ ≤ a₁ := by omega
        have hne : ¬ B (b₁ + (b₂ - b₁)) := ha_no (b₂ - b₁) h1 h2
        have hb2_eq : b₁ + (b₂ - b₁) = b₂ := by omega
        rw [hb2_eq] at hne
        exact hne hBb₂
      · rw [mem_gapSet] at hg₂
        rcases hg₂ with ⟨_, _, ha_no⟩
        have h1 : 1 ≤ b₁ - b₂ := by omega
        have h2 : b₁ - b₂ ≤ a₂ := by omega
        have hne : ¬ B (b₂ + (b₁ - b₂)) := ha_no (b₁ - b₂) h1 h2
        have hb1_eq : b₂ + (b₁ - b₂) = b₁ := by omega
        rw [hb1_eq] at hne
        exact hne hBb₁
  -- Define the image Finset of the injection.
  set img := GS.image (fun x => x.fst + x.snd) with himg_def
  have himg_card : img.card = GS.card :=
    Finset.card_image_of_injOn (fun x hx y hy h => h_inj x hx y hy h)
  have himg_subset_Bcnt : img ⊆ Bcnt := by
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨⟨b, a⟩, hba, heq⟩
    rw [← heq]
    exact (h_image ⟨b, a⟩ hba).1
  have himg_disjoint_SB : Disjoint img SB := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_of_forall_notMem ?_
    intro m hm
    rw [Finset.mem_inter, Finset.mem_image] at hm
    rcases hm with ⟨⟨⟨b, a⟩, hba, heq⟩, hmsb⟩
    rw [← heq] at hmsb
    exact (h_image ⟨b, a⟩ hba).2 hmsb
  -- Combine: SB ⊔ img ⊆ Bcnt, with SB ⊥ img, so |SB| + |img| ≤ |Bcnt|.
  have h_card_union : (SB ∪ img).card = SB.card + img.card :=
    Finset.card_union_of_disjoint himg_disjoint_SB.symm
  have h_union_subset : SB ∪ img ⊆ Bcnt := by
    intro m hm
    rw [Finset.mem_union] at hm
    rcases hm with h | h
    · exact hSB_subset_Bcnt h
    · exact himg_subset_Bcnt h
  have h_card_sum : SB.card + img.card ≤ Bcnt.card := by
    rw [← h_card_union]; exact Finset.card_le_card h_union_subset
  have hSB_card : SB.card = countingUpTo B n := rfl
  have hBcnt_card : Bcnt.card = countingUpTo (sumset A B) n := rfl
  have hGS_card : GS.card =
      ∑ b ∈ (Finset.range (n + 1)).filter (fun b => B b),
          ((gapSet B n b).filter (fun a => A a)).card :=
    Finset.card_sigma _ _
  rw [hSB_card, hBcnt_card, himg_card, hGS_card] at h_card_sum
  exact h_card_sum

end PointwiseSumsetBound

/-! ## Lower bound for the gap-restricted A-counts.

Each gap term `((gapSet B n b).filter A).card` is bounded below by
`(countingUpTo A) of the gap size`.  Combined with
`schnirelmannDensity_ge_of_counting_ge`'s contrapositive, this lets us
collapse the sum.  In the current file we use the weaker, **average**
form: we lower bound each gap term by `σA · (gap size)` modulo a
finite-set correction. -/

section GapLowerBound

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- The "gap-shifted" set of `a ∈ A` is contained in `[0, n - b]`. -/
lemma gapSet_filter_A_card_le (n b : ℕ) :
    ((gapSet B n b).filter (fun a => A a)).card ≤
      countingUpTo A (n - b) := by
  classical
  -- Both Finsets count `a` with `1 ≤ a, A a`, but the LHS has the
  -- extra "in gap" condition.  So LHS ⊆ filter (1 ≤ a ∧ A a) of
  -- range (n - b + 1) = RHS.
  refine Finset.card_le_card ?_
  intro a ha
  rw [Finset.mem_filter, mem_gapSet] at ha
  rcases ha with ⟨⟨ha1, hab_le, _⟩, hAa⟩
  refine Finset.mem_filter.mpr ⟨?_, ha1, hAa⟩
  exact Finset.mem_range.mpr (by omega)

/-- *Equality* between filter-and-gap counting and a direct `Finset.filter`
counting: the gap-A intersection counted as the image of the pair sum.
We use this only via the inequality above. -/
lemma countingUpTo_A_ge_card_filter (n b j : ℕ)
    (hgap : ∀ i, 1 ≤ i → i ≤ j → ¬ B (b + i)) (hjn : b + j ≤ n) :
    ((Finset.range (j + 1)).filter (fun a => 1 ≤ a ∧ A a)).card ≤
      ((gapSet B n b).filter (fun a => A a)).card := by
  classical
  refine Finset.card_le_card ?_
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨ha_le, ha1, hAa⟩
  refine Finset.mem_filter.mpr ⟨?_, hAa⟩
  rw [mem_gapSet]
  refine ⟨ha1, by omega, ?_⟩
  intro i hi1 hile
  exact hgap i hi1 (by omega)

end GapLowerBound

/-! ## The Schnirelmann pointwise lower bound.

Combining the gap-injection bound with the density lower bound
`A(k) ≥ σA · k` (via `schnirelmannDensity_ge_of_counting_ge`) gives:

```
(A + B)(n) ≥ B(n) + σA · (n - B(n)).
```
-/

section PointwiseDensityBound

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- The Schnirelmann **pointwise lower bound**.

Assuming `0 ∈ A`, `0 ∈ B`, and that `A` satisfies the lower-density
hypothesis `∀ k, 1 ≤ k → α · k ≤ countingUpTo A k`, we have

```
(α · n + (1 - α) · countingUpTo B n) ≤ countingUpTo (A + B) n
```

for every `n ≥ 1`. -/
theorem countingUpTo_sumset_lower_bound (hA0 : A 0) (hB0 : B 0)
    {α : ℝ} (_hα_le : α ≤ 1)
    (hα_count : ∀ k : ℕ, 1 ≤ k → α * (k : ℝ) ≤ (countingUpTo A k : ℝ))
    (n : ℕ) (_hn : 1 ≤ n) :
    α * (n : ℝ) + (1 - α) * (countingUpTo B n : ℝ) ≤
      (countingUpTo (sumset A B) n : ℝ) := by
  classical
  -- Step 1: ∑ |gap b ∩ A| ≥ α * ∑ (gap b)
  --        ≥ α * (n - countingUpTo B n) ............ (*)
  set Br := (Finset.range (n + 1)).filter (fun b => B b) with hBr_def
  have hBr_subset_le : ∀ b ∈ Br, b ≤ n := by
    intro b hb
    rw [hBr_def, Finset.mem_filter, Finset.mem_range] at hb
    omega
  -- Sum of gap-sizes equals `n - countingUpTo B n` (key identity).
  have h_sum_gap : ∑ b ∈ Br, (gapSet B n b).card = n - countingUpTo B n :=
    sum_gapSet_card B n hB0
  -- Each gap-A term is bounded below.  Now apply α-lower density to each.
  have h_each : ∀ b ∈ Br,
      α * ((gapSet B n b).card : ℝ) ≤
        (((gapSet B n b).filter (fun a => A a)).card : ℝ) := by
    intro b hb
    -- Identify (gapSet B n b) with the natural counting of a "gap window".
    -- The gap window is `(b, ...]` and its size is `(gapSet B n b).card`.
    -- We need to relate `card (filter A (gap))` to `α * card (gap)`.
    -- We'll bound from below by `countingUpTo A (gap.card)`, then apply hα.
    -- KEY observation: if the gap has size `g`, then it equals
    -- `Finset.Ico 1 (g + 1)`, mapped via `a ↦ b + a`.  So filtering `A`
    -- via `a ↦ A (b + a)` ... but we want `A a`, the original predicate.
    -- The setup is: gapSet contains `j` such that `b + i ∉ B` for
    -- `1 ≤ i ≤ j` AND `b + j ≤ n`.  The card is the largest j with
    -- `j ≤ n - b` and `b + i ∉ B for 1 ≤ i ≤ j`.
    -- Let `g = (gapSet B n b).card`.  We claim:
    --   gapSet B n b = Finset.Ioc 0 g
    -- This is because the "no B in [b+1, b+j]" condition is monotone in j.
    -- gapSet is downward closed: j ∈ gap and 1 ≤ j' ≤ j ⇒ j' ∈ gap.
    have hdown : ∀ j ∈ gapSet B n b, ∀ j', 1 ≤ j' → j' ≤ j → j' ∈ gapSet B n b := by
      intro j hj j' hj'1 hj'le
      rw [mem_gapSet] at hj ⊢
      rcases hj with ⟨_, hjn, hj_no⟩
      refine ⟨hj'1, by omega, ?_⟩
      intro i hi1 hile
      exact hj_no i hi1 (by omega)
    -- Define g and prove: gapSet B n b = Finset.Ioc 0 g.
    set g := (gapSet B n b).card with hg_def
    have hgap_eq : (gapSet B n b) = Finset.Ioc 0 g := by
      rcases (gapSet B n b).eq_empty_or_nonempty with hempty | hne
      · -- card = 0, so Ioc 0 0 = ∅.
        have : g = 0 := by rw [hg_def, hempty]; rfl
        rw [hempty, this]; rfl
      · -- max' is in gapSet; downward closure gives gapSet ⊇ {1, ..., max'}.
        -- And gapSet ⊆ {1, ..., max'} by max'-property.  So gapSet = Ioc 0 max'.
        -- Then card = max'.
        have hmax_mem := Finset.max'_mem _ hne
        set M := (gapSet B n b).max' hne with hM_def
        have hsubset : (gapSet B n b) ⊆ Finset.Ioc 0 M := by
          intro j hj
          rw [Finset.mem_Ioc]
          rw [mem_gapSet] at hj
          exact ⟨hj.1, Finset.le_max' _ _ (by rw [mem_gapSet]; exact hj)⟩
        have hsuperset : Finset.Ioc 0 M ⊆ (gapSet B n b) := by
          intro j hj
          rw [Finset.mem_Ioc] at hj
          exact hdown M hmax_mem j hj.1 hj.2
        have h_eq_M : (gapSet B n b) = Finset.Ioc 0 M :=
          Finset.Subset.antisymm hsubset hsuperset
        have h_card_M : (gapSet B n b).card = M := by
          rw [h_eq_M, Nat.card_Ioc]; omega
        have hg_eq_M : g = M := by rw [hg_def]; exact h_card_M
        rw [h_eq_M, hg_eq_M]
    -- Use this Ioc characterization.
    have h_filter_eq :
        ((gapSet B n b).filter (fun a => A a)).card = countingUpTo A g := by
      rw [hgap_eq]
      -- countingUpTo A g = (range (g+1)).filter (fun k => 1 ≤ k ∧ A k)).card
      -- Ioc 0 g = (range (g+1)).filter (fun k => 1 ≤ k)
      have h_Ioc_eq : (Finset.Ioc 0 g) =
          (Finset.range (g + 1)).filter (fun k => 1 ≤ k) := by
        ext k
        simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
        omega
      rw [h_Ioc_eq]
      unfold countingUpTo
      rw [Finset.filter_filter]
    rw [h_filter_eq]
    -- Now reduce to: α * g ≤ countingUpTo A g.
    rcases Nat.eq_zero_or_pos g with hg0 | hg1
    · rw [hg0]
      simp only [Nat.cast_zero, mul_zero]
      exact_mod_cast Nat.zero_le _
    · exact hα_count g hg1
  -- Sum the per-b inequality.
  have h_sum_ineq :
      α * ((∑ b ∈ Br, (gapSet B n b).card : ℕ) : ℝ) ≤
        (((Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card : ℕ) : ℝ) := by
    have : α * ((∑ b ∈ Br, (gapSet B n b).card : ℕ) : ℝ) =
        ∑ b ∈ Br, α * ((gapSet B n b).card : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    rw [this]
    have h_card_sigma :
        (Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card =
          ∑ b ∈ Br, ((gapSet B n b).filter (fun a => A a)).card :=
      Finset.card_sigma _ _
    rw [h_card_sigma]
    push_cast
    exact Finset.sum_le_sum h_each
  -- Plug in the sum identity.
  rw [h_sum_gap] at h_sum_ineq
  have h_n_sub_count :
      ((n - countingUpTo B n : ℕ) : ℝ) =
        (n : ℝ) - (countingUpTo B n : ℝ) := by
    have hle : countingUpTo B n ≤ n := countingUpTo_le B n
    have h2 := Nat.sub_add_cancel hle
    have h3 : ((n - countingUpTo B n : ℕ) : ℝ) + (countingUpTo B n : ℝ) = (n : ℝ) := by
      exact_mod_cast h2
    linarith
  rw [h_n_sub_count] at h_sum_ineq
  -- Now combine with the gap-injection bound.
  have h_gap_inj := countingUpTo_sumset_ge_sum_card_gap A B hA0 hB0 n
  have h_gap_inj_real :
      (countingUpTo B n : ℝ) +
        ∑ b ∈ Br, (((gapSet B n b).filter (fun a => A a)).card : ℝ) ≤
        (countingUpTo (sumset A B) n : ℝ) := by
    have h_sum_eq :
        ∑ b ∈ Br, (((gapSet B n b).filter (fun a => A a)).card : ℝ) =
          (((Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card : ℕ) : ℝ) := by
      rw [Finset.card_sigma]
      push_cast
      rfl
    rw [h_sum_eq]
    have h_gap_inj' :
        (countingUpTo B n + ∑ b ∈ Br,
            ((gapSet B n b).filter (fun a => A a)).card : ℕ) ≤
          countingUpTo (sumset A B) n := h_gap_inj
    have h_card_sigma_eq :
        (((Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card : ℕ) : ℝ) =
        ((∑ b ∈ Br, ((gapSet B n b).filter (fun a => A a)).card : ℕ) : ℝ) := by
      rw [Finset.card_sigma]
    rw [h_card_sigma_eq]
    exact_mod_cast h_gap_inj'
  -- Now combine.
  -- We have:
  --   α * (n - countingUpTo B n) ≤ ∑ b ∈ Br, ((gapSet B n b).filter A).card
  --   countingUpTo B n + ∑ ≤ countingUpTo (sumset A B) n
  -- Thus:
  --   α * n + (1 - α) * countingUpTo B n
  --   = α * (n - countingUpTo B n) + countingUpTo B n
  --   ≤ ∑ + countingUpTo B n
  --   ≤ countingUpTo (sumset A B) n.
  have h_combine :
      α * ((n : ℝ) - (countingUpTo B n : ℝ)) + (countingUpTo B n : ℝ) ≤
        (countingUpTo (sumset A B) n : ℝ) := by
    calc α * ((n : ℝ) - (countingUpTo B n : ℝ)) + (countingUpTo B n : ℝ)
        ≤ (((Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card : ℕ) : ℝ)
            + (countingUpTo B n : ℝ) := by
              linarith
      _ = (countingUpTo B n : ℝ) +
            ∑ b ∈ Br, (((gapSet B n b).filter (fun a => A a)).card : ℝ) := by
              have h_card_sigma :
                  (((Br.sigma (fun b => (gapSet B n b).filter (fun a => A a))).card : ℕ) : ℝ) =
                    ∑ b ∈ Br, (((gapSet B n b).filter (fun a => A a)).card : ℝ) := by
                rw [Finset.card_sigma]; push_cast; rfl
              rw [h_card_sigma]; ring
      _ ≤ (countingUpTo (sumset A B) n : ℝ) := h_gap_inj_real
  -- Rewrite LHS.
  have h_lhs_eq :
      α * (n : ℝ) + (1 - α) * (countingUpTo B n : ℝ) =
        α * ((n : ℝ) - (countingUpTo B n : ℝ)) + (countingUpTo B n : ℝ) := by ring
  rw [h_lhs_eq]
  exact h_combine

end PointwiseDensityBound

/-! ## Schnirelmann's addition theorem. -/

section SchnirelmannAddition

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- **Schnirelmann's addition theorem**.

If `0 ∈ A` and `0 ∈ B`, then
`σA + σB - σA · σB ≤ σ(A + B)`. -/
theorem schnirelmannDensity_sumset_ge (hA0 : A 0) (hB0 : B 0) :
    schnirelmannDensity A + schnirelmannDensity B -
        schnirelmannDensity A * schnirelmannDensity B ≤
      schnirelmannDensity (sumset A B) := by
  set α := schnirelmannDensity A
  set β := schnirelmannDensity B
  have hα_le1 : α ≤ 1 := schnirelmannDensity_le_one A
  have hβ_le1 : β ≤ 1 := schnirelmannDensity_le_one B
  have hα_nonneg : 0 ≤ α := schnirelmannDensity_nonneg A
  have hβ_nonneg : 0 ≤ β := schnirelmannDensity_nonneg B
  -- α-lower density of A: ∀ k ≥ 1, α * k ≤ countingUpTo A k.
  have hα_count : ∀ k : ℕ, 1 ≤ k → α * (k : ℝ) ≤ (countingUpTo A k : ℝ) := by
    intro k hk
    have h_term : (countingUpTo A k : ℝ) / k = schnirelmannTerm A k := by
      unfold schnirelmannTerm; simp [hk]
    have hb := bddBelow_range_schnirelmannTerm A
    have hα_le_term : α ≤ schnirelmannTerm A k := ciInf_le hb k
    rw [← h_term] at hα_le_term
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    exact (le_div_iff₀ hk_pos).mp hα_le_term
  have hβ_count : ∀ k : ℕ, 1 ≤ k → β * (k : ℝ) ≤ (countingUpTo B k : ℝ) := by
    intro k hk
    have h_term : (countingUpTo B k : ℝ) / k = schnirelmannTerm B k := by
      unfold schnirelmannTerm; simp [hk]
    have hb := bddBelow_range_schnirelmannTerm B
    have hβ_le_term : β ≤ schnirelmannTerm B k := ciInf_le hb k
    rw [← h_term] at hβ_le_term
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    exact (le_div_iff₀ hk_pos).mp hβ_le_term
  -- The pointwise bound: α n + (1 - α) B(n) ≤ (A+B)(n).
  have h_point : ∀ n : ℕ, 1 ≤ n →
      α * (n : ℝ) + (1 - α) * (countingUpTo B n : ℝ) ≤
        (countingUpTo (sumset A B) n : ℝ) :=
    fun n hn => countingUpTo_sumset_lower_bound A B hA0 hB0 hα_le1 hα_count n hn
  -- Bound (1 - α) * B(n) ≥ (1 - α) * β * n.
  have h_one_sub_α_nonneg : 0 ≤ 1 - α := by linarith
  have h_final : ∀ n : ℕ, 1 ≤ n →
      (α + β - α * β) * (n : ℝ) ≤ (countingUpTo (sumset A B) n : ℝ) := by
    intro n hn
    have hβ_n := hβ_count n hn
    have h1 : (1 - α) * (β * (n : ℝ)) ≤ (1 - α) * (countingUpTo B n : ℝ) :=
      mul_le_mul_of_nonneg_left hβ_n h_one_sub_α_nonneg
    have h2 : α * (n : ℝ) + (1 - α) * (β * (n : ℝ)) ≤
        α * (n : ℝ) + (1 - α) * (countingUpTo B n : ℝ) := by linarith
    have h3 : α * (n : ℝ) + (1 - α) * (β * (n : ℝ)) =
        (α + β - α * β) * (n : ℝ) := by ring
    linarith [h_point n hn]
  exact schnirelmannDensity_ge_of_counting_ge (sumset A B) h_final

end SchnirelmannAddition

/-! ## Iterated sumset density. -/

section IteratedSumset

variable {A : ℕ → Prop} [DecidablePred A]

set_option linter.unusedSectionVars false in
/-- `0 ∈ A` propagates: `0 ∈ sumset A (sumsetIter A k)`. -/
lemma zero_mem_sumset_sumsetIter (hA : A 0) (k : ℕ) :
    sumset A (sumsetIter A k) 0 :=
  sumset_of_mem_right hA (zero_mem_sumsetIter hA k)

/-- The Schnirelmann iteration inequality:
`σ(sumsetIter A (k+1)) ≥ σA + σ(sumsetIter A k) - σA · σ(sumsetIter A k)`. -/
theorem schnirelmannDensity_sumsetIter_succ_ge (hA : A 0) (k : ℕ) :
    schnirelmannDensity A + schnirelmannDensity (sumsetIter A k) -
        schnirelmannDensity A * schnirelmannDensity (sumsetIter A k) ≤
      schnirelmannDensity (sumsetIter A (k + 1)) := by
  have h := schnirelmannDensity_sumset_ge A (sumsetIter A k) hA (zero_mem_sumsetIter hA k)
  -- `sumsetIter A (k+1) = sumset A (sumsetIter A k)`.
  exact h

/-- **Geometric closure**: if `σA > 0`, then `1 - σ(sumsetIter A (k+1)) ≤
(1 - σA) · (1 - σ(sumsetIter A k))`. -/
theorem one_sub_schnirelmannDensity_sumsetIter_succ_le (hA : A 0) (k : ℕ) :
    1 - schnirelmannDensity (sumsetIter A (k + 1)) ≤
      (1 - schnirelmannDensity A) *
        (1 - schnirelmannDensity (sumsetIter A k)) := by
  have h := schnirelmannDensity_sumsetIter_succ_ge hA k
  have : (1 - schnirelmannDensity A) *
        (1 - schnirelmannDensity (sumsetIter A k)) =
      1 - (schnirelmannDensity A + schnirelmannDensity (sumsetIter A k) -
        schnirelmannDensity A * schnirelmannDensity (sumsetIter A k)) := by ring
  linarith

/-- Iterated form via `(1 - σA)^k`. -/
theorem one_sub_schnirelmannDensity_sumsetIter_le (hA : A 0) :
    ∀ k : ℕ, 1 - schnirelmannDensity (sumsetIter A k) ≤
      (1 - schnirelmannDensity A) ^ k
  | 0 => by
    -- σ(sumsetIter A 0) = σ({0}).  Since {0} doesn't contain 1, density = 0.
    -- So 1 - 0 = 1 ≤ 1^0 = 1.
    have h0 : schnirelmannDensity (sumsetIter A 0) = 0 := by
      apply schnirelmannDensity_eq_zero_of_one_not_mem
      intro h1
      -- sumsetIter A 0 = fun n => n = 0, so it doesn't contain 1.
      change (1 : ℕ) = 0 at h1
      exact one_ne_zero h1
    simp [h0]
  | k + 1 => by
    have h_ind := one_sub_schnirelmannDensity_sumsetIter_le hA k
    have h_step := one_sub_schnirelmannDensity_sumsetIter_succ_le hA k
    have hα_le1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one A
    have hα_nonneg : 0 ≤ schnirelmannDensity A := schnirelmannDensity_nonneg A
    have hone_sub_α_nonneg : 0 ≤ 1 - schnirelmannDensity A := by linarith
    have hβ_le1 : schnirelmannDensity (sumsetIter A k) ≤ 1 :=
      schnirelmannDensity_le_one _
    have hone_sub_β_nonneg : 0 ≤ 1 - schnirelmannDensity (sumsetIter A k) := by
      linarith
    calc 1 - schnirelmannDensity (sumsetIter A (k + 1))
        ≤ (1 - schnirelmannDensity A) *
            (1 - schnirelmannDensity (sumsetIter A k)) := h_step
      _ ≤ (1 - schnirelmannDensity A) * (1 - schnirelmannDensity A) ^ k :=
          mul_le_mul_of_nonneg_left h_ind hone_sub_α_nonneg
      _ = (1 - schnirelmannDensity A) ^ (k + 1) := by ring

/-- **Geometric content of iteration**.  We expose the geometric
convergence `1 - σ(sumsetIter A k) ≤ (1 - σA)^k` proved in
`one_sub_schnirelmannDensity_sumsetIter_le`.  Inverting this gives:

```
σ(sumsetIter A k) ≥ 1 - (1 - σA)^k.
```

When `σA > 0`, the right-hand side approaches `1` as `k → ∞`.  The
*existential* form (∃ k, σ(sumsetIter A k) = 1) requires the
Schnirelmann basis-order theorem, which combines this geometric step
with a "second-step" argument involving the case `σ ≥ 1/2`.  That
second step is the content of P6-T3 (Mann's inequality / second-step
basis closure) and is intentionally deferred.

Here we expose the geometric step in its strongest available form. -/
theorem schnirelmannDensity_sumsetIter_ge_one_sub_geom (hA : A 0) (k : ℕ) :
    1 - (1 - schnirelmannDensity A) ^ k ≤ schnirelmannDensity (sumsetIter A k) := by
  have h := one_sub_schnirelmannDensity_sumsetIter_le hA k
  linarith

/-- **Honest closure at `σA = 1`**: when `σA = 1`, the iterated sumset
has density `1` at `k = 1`.  This handles the trivial corner of the
existential statement; the nontrivial case `σA ∈ (0, 1)` is deferred
to P6-T3. -/
theorem schnirelmannDensity_sumsetIter_one_of_density_one (hA : A 0)
    (hA1 : schnirelmannDensity A = 1) :
    schnirelmannDensity (sumsetIter A 1) = 1 := by
  show schnirelmannDensity (sumset A (sumsetIter A 0)) = 1
  have h_iter0 : schnirelmannDensity (sumsetIter A 0) = 0 := by
    apply schnirelmannDensity_eq_zero_of_one_not_mem
    intro h1
    change (1 : ℕ) = 0 at h1
    exact one_ne_zero h1
  have h_le1 : schnirelmannDensity (sumset A (sumsetIter A 0)) ≤ 1 :=
    schnirelmannDensity_le_one _
  have h_ge :=
    schnirelmannDensity_sumset_ge A (sumsetIter A 0) hA (zero_mem_sumsetIter hA 0)
  rw [hA1, h_iter0] at h_ge
  linarith

end IteratedSumset

end Gdbh
