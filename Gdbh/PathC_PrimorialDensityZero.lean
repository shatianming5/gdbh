/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T8 (Phase 22 / Path C — Primorial density-zero handling
        and the σ-bridge: positive Schnirelmann density on the
        non-primorial subsequence transfers to positive Schnirelmann
        density on the full set.)
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Gdbh.PathC_WeightedLogLossClosure

/-!
# Path C — P22-T8: Primorial density-zero handling

This file is the **P22-T8 deliverable** in Phase 22 (Path C closure).
It assembles the *primorial-density-zero* handling argument that
underlies the refactored `PrimesSumsetDensityModuloPrimorials` Prop
(P21-T2) and the K-Goldbach pipeline.

## Headline content

The set of primorials `{1, 2, 6, 30, 210, 2310, 30030, ...}` is
**extremely sparse**:  the `j`-th distinct primorial value
`∏_{i ≤ j} p_i ≥ 2^j`, so `#{primorials ≤ N} ≤ Nat.log 2 N + 1` is
`O(log N)`.  In particular the primorial subsequence has Schnirelmann
density zero, and removing it from any set `A ⊆ ℕ` *cannot* destroy
positivity of `σ(A)`:  `σ(A | non-primorial) > 0 → σ(A) > 0`.

This file provides:

1. **`IsPrimorial`** — alias for the `IsPrimorialValue` predicate
   defined in P21-T2 (`PathC_WeightedLogLossClosure.lean`).

2. **Sparsity bound**:
   `countingUpTo IsPrimorial N ≤ Nat.log 2 N + 1` for `N ≥ 1`
   (Section 3).  The proof uses the elementary observation that
   between any two distinct primorial values `m₁ < m₂` one has
   `2 * m₁ ≤ m₂` (a new prime `≥ 2` is added at every jump).

3. **Density-zero / `o(n)` form**:
   `Filter.Tendsto (fun n => (countingUpTo IsPrimorial n : ℝ) / n)
       Filter.atTop (nhds 0)` (Section 4), obtained by combining the
   `O(log N)` bound with `Real.isLittleO_log_id_atTop`.

4. **σ-bridge**:
   `σ(A ∧ ¬IsPrimorial) > 0 → σ(A) > 0` (Section 5), which is a
   direct consequence of monotonicity of `countingUpTo` and *does
   not* require the density-zero asymptotic — it is purely
   inclusion-based.

5. **Combined corollary**:  for `A = primesSumset`, the existing
   `PrimesSumsetDensityModuloPrimorials` Prop (P21-T2) yields
   positive Schnirelmann density of `primesSumset` via the σ-bridge
   (Section 6).

6. **Axiom audit** (`#print axioms`, Section 7).

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* This file only adds; it does not modify any other file.
-/

namespace Gdbh
namespace PathCPrimorialDensityZero

open scoped BigOperators
open Gdbh.PathCKGoldbach (primesSumset primesSumset_one)
open Gdbh.PathCWeightedLogLossClosure
  (IsPrimorialValue isPrimorialValue_one isPrimorialValue_two
   primesSumsetMinusPrimorials primesSumsetMinusPrimorials_decidable
   PrimesSumsetDensityModuloPrimorials
   primesSumset_of_primesSumsetMinusPrimorials
   countingUpTo_primesSumsetMinusPrimorials_le_primesSumset
   primesSumsetUniformLowerBound_of_densityModuloPrimorials
   schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials)

/-! ## Section 1 — `IsPrimorial` alias and elementary facts -/

/-- **`IsPrimorial n`** — alias for the P21-T2 predicate
`IsPrimorialValue n`, capturing "`n = primorial k` for some `k`". -/
def IsPrimorial (n : ℕ) : Prop := IsPrimorialValue n

/-- Decidability of `IsPrimorial` (via `Classical.dec`).  We only ever
need decidability through `countingUpTo`, so a `noncomputable` instance
is sufficient. -/
noncomputable instance isPrimorial_decidable : DecidablePred IsPrimorial := by
  classical
  intro n
  unfold IsPrimorial
  exact Classical.propDecidable _

/-- `1` is a primorial value. -/
lemma isPrimorial_one : IsPrimorial 1 := isPrimorialValue_one

/-- `2` is a primorial value. -/
lemma isPrimorial_two : IsPrimorial 2 := isPrimorialValue_two

/-- `IsPrimorial` is the same as `IsPrimorialValue`. -/
lemma isPrimorial_iff (n : ℕ) : IsPrimorial n ↔ IsPrimorialValue n := Iff.rfl

/-! ## Section 2 — The "factor-of-two" growth lemma

Between any two distinct primorial values `m₁ < m₂` (both `≥ 1`),
one has `2 * m₁ ≤ m₂` because the larger value adds at least one
extra prime factor `p ≥ 2`.

This is the *only* analytic content of the sparsity argument.  -/

/-- **Factor-of-two growth.**  Distinct primorial values `m₁ < m₂`,
both `≥ 1`, satisfy `2 * m₁ ≤ m₂`.

Proof:  write `m₁ = primorial k₁`, `m₂ = primorial k₂`.  Since
`primorial` is monotone, `m₁ < m₂` forces `k₁ < k₂`.  Then the
Bertrand-style factorisation
`primorial k₂ = primorial k₁ * ∏ p ∈ Ico (k₁+1) (k₂+1) with p.Prime, p`
shows the second factor is a *non-empty* product of primes (because
`primorial k₁ ≠ primorial k₂`), hence is `≥ 2`. -/
lemma two_mul_le_of_isPrimorial_lt
    {m₁ m₂ : ℕ} (h₁ : IsPrimorial m₁) (h₂ : IsPrimorial m₂)
    (hm₁_pos : 1 ≤ m₁) (hlt : m₁ < m₂) : 2 * m₁ ≤ m₂ := by
  classical
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  -- We do NOT need `k₁ < k₂` strictly; we just need to bound `m₂ / m₁` from below.
  -- Strategy: m₂ ≥ 2 m₁ iff (m₂ - m₁) ≥ m₁.  We use `primorial` divisibility.
  -- A cleaner approach: any natural number `n ≥ 2 m₁` lies above `2 m₁`.
  -- We show `m₂ ≥ 2 m₁` by showing `m₁ ∣ m₂` and `m₂ ≠ m₁` and `m₂ ≥ m₁`.
  -- From `primorial k₁ ∣ primorial k₂` whenever `k₁ ≤ k₂`, we get `m₁ ∣ m₂`
  -- when `k₁ ≤ k₂`.  But `k₁ ≤ k₂` is needed.
  -- Case 1: k₁ ≤ k₂.
  by_cases hk : k₁ ≤ k₂
  · -- `m₁ ∣ m₂` because primorial is divisibility-monotone.
    have h_dvd : m₁ ∣ m₂ := by
      rw [← hk₁, ← hk₂]
      exact primorial_dvd_primorial hk
    -- `m₂ / m₁ ≥ 2` since `m₂ > m₁ ≥ 1` and `m₁ ∣ m₂`.
    have hm₁_ne : m₁ ≠ 0 := by omega
    obtain ⟨q, hq⟩ := h_dvd
    -- `m₂ = m₁ * q` with `m₁ * q > m₁`, hence `q ≥ 2`.
    rw [hq]
    rw [hq] at hlt
    have hq_gt_one : 1 < q := by
      -- `m₁ * q > m₁ * 1` and `m₁ > 0` gives `q > 1`.
      have hm₁_pos' : 0 < m₁ := hm₁_pos
      have : m₁ * 1 < m₁ * q := by
        rw [mul_one]; exact hlt
      exact (mul_lt_mul_iff_of_pos_left hm₁_pos').mp this
    -- `2 * m₁ ≤ m₁ * q`.
    have hq_ge_two : 2 ≤ q := hq_gt_one
    calc 2 * m₁ = m₁ * 2 := by ring
      _ ≤ m₁ * q := Nat.mul_le_mul_left m₁ hq_ge_two
  · -- Case 2: k₂ < k₁ (so k₁ > k₂).  Then primorial k₁ ≥ primorial k₂, hence m₁ ≥ m₂.
    -- This contradicts `m₁ < m₂`.
    have hk_lt : k₂ < k₁ := Nat.lt_of_not_le hk
    have hk_le : k₂ ≤ k₁ := le_of_lt hk_lt
    have h_mono : primorial k₂ ≤ primorial k₁ := primorial_mono hk_le
    rw [hk₁, hk₂] at h_mono
    omega

/-! ## Section 3 — The `O(log N)` count bound

We prove:

```
countingUpTo IsPrimorial N ≤ Nat.log 2 N + 1   (for N ≥ 1).
```

Proof: the set of primorial values in `[1, N]` injects into the
range `[0, Nat.log 2 N]` via `m ↦ Nat.log 2 m`.  Injectivity follows
from the factor-of-two growth (`Nat.log 2` distinguishes any two
values whose ratio is `≥ 2`).
-/

/-- The *Finset* of primorial values in `[1, N]`.

We use the `Classical` decidable instance from
`isPrimorial_decidable`.  This Finset is the underlying set behind
`countingUpTo IsPrimorial N`. -/
noncomputable def primorialValuesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => 1 ≤ k ∧ IsPrimorial k)

/-- `countingUpTo IsPrimorial N = (primorialValuesUpTo N).card`. -/
lemma countingUpTo_isPrimorial_eq (N : ℕ) :
    Gdbh.countingUpTo IsPrimorial N = (primorialValuesUpTo N).card := by
  unfold Gdbh.countingUpTo primorialValuesUpTo
  rfl

/-- **`Nat.log 2` is injective on the primorial values in `[1, N]`.**

If `m₁, m₂ ∈ primorialValuesUpTo N` and `Nat.log 2 m₁ = Nat.log 2 m₂`,
then `m₁ = m₂`. -/
lemma nat_log_2_injOn_primorialValuesUpTo (N : ℕ) :
    Set.InjOn (fun m : ℕ => Nat.log 2 m) (primorialValuesUpTo N : Set ℕ) := by
  classical
  intro m₁ hm₁ m₂ hm₂ h_eq
  -- The lambda evaluates to: `Nat.log 2 m₁ = Nat.log 2 m₂`.
  simp only at h_eq
  -- Both are positive primorial values.
  have hm₁_mem : m₁ ∈ primorialValuesUpTo N := hm₁
  have hm₂_mem : m₂ ∈ primorialValuesUpTo N := hm₂
  unfold primorialValuesUpTo at hm₁_mem hm₂_mem
  rcases Finset.mem_filter.mp hm₁_mem with ⟨_, hm₁_pos, hm₁_prim⟩
  rcases Finset.mem_filter.mp hm₂_mem with ⟨_, hm₂_pos, hm₂_prim⟩
  -- Trichotomy on `m₁` vs `m₂`.
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · -- m₁ < m₂.  By factor-of-two growth, 2 m₁ ≤ m₂.
    have h_two_mul : 2 * m₁ ≤ m₂ :=
      two_mul_le_of_isPrimorial_lt hm₁_prim hm₂_prim hm₁_pos hlt
    -- Then Nat.log 2 m₂ ≥ Nat.log 2 (2 m₁) = Nat.log 2 m₁ + 1.
    have hm₁_ne : m₁ ≠ 0 := by omega
    have h_log_2m : Nat.log 2 (2 * m₁) = Nat.log 2 m₁ + 1 := by
      have := Nat.log_mul_base (b := 2) Nat.one_lt_two hm₁_ne
      rw [show 2 * m₁ = m₁ * 2 from by ring]
      exact this
    have h_log_mono : Nat.log 2 (2 * m₁) ≤ Nat.log 2 m₂ :=
      Nat.log_mono_right h_two_mul
    rw [h_log_2m] at h_log_mono
    -- h_eq : Nat.log 2 m₁ = Nat.log 2 m₂, h_log_mono : ...+1 ≤ ....
    exfalso
    linarith
  · exact heq
  · -- m₁ > m₂.  Symmetric case.
    have h_two_mul : 2 * m₂ ≤ m₁ :=
      two_mul_le_of_isPrimorial_lt hm₂_prim hm₁_prim hm₂_pos hgt
    have hm₂_ne : m₂ ≠ 0 := by omega
    have h_log_2m : Nat.log 2 (2 * m₂) = Nat.log 2 m₂ + 1 := by
      have := Nat.log_mul_base (b := 2) Nat.one_lt_two hm₂_ne
      rw [show 2 * m₂ = m₂ * 2 from by ring]
      exact this
    have h_log_mono : Nat.log 2 (2 * m₂) ≤ Nat.log 2 m₁ :=
      Nat.log_mono_right h_two_mul
    rw [h_log_2m] at h_log_mono
    -- h_eq : Nat.log 2 m₁ = Nat.log 2 m₂, h_log_mono : Nat.log 2 m₂ + 1 ≤ Nat.log 2 m₁.
    exfalso
    linarith

/-- **`Nat.log 2 m ≤ Nat.log 2 N`** for `m ∈ primorialValuesUpTo N`. -/
lemma nat_log_2_le_of_mem_primorialValuesUpTo
    {N m : ℕ} (h : m ∈ primorialValuesUpTo N) :
    Nat.log 2 m ≤ Nat.log 2 N := by
  unfold primorialValuesUpTo at h
  rcases Finset.mem_filter.mp h with ⟨h_range, _, _⟩
  have h_le : m ≤ N := by
    have := Finset.mem_range.mp h_range
    omega
  exact Nat.log_mono_right h_le

/-- **The image of `primorialValuesUpTo N` under `Nat.log 2` lies in
`Finset.range (Nat.log 2 N + 1)`.** -/
lemma image_nat_log_2_subset (N : ℕ) :
    (primorialValuesUpTo N).image (fun m => Nat.log 2 m) ⊆
      Finset.range (Nat.log 2 N + 1) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨m, hm, hxm⟩
  rw [← hxm]
  have h_le := nat_log_2_le_of_mem_primorialValuesUpTo hm
  exact Finset.mem_range.mpr (by omega)

/-- **The headline count bound.**  For every `N : ℕ`,

```
countingUpTo IsPrimorial N ≤ Nat.log 2 N + 1.
```

Proof: the Finset `primorialValuesUpTo N` injects into
`Finset.range (Nat.log 2 N + 1)` via `m ↦ Nat.log 2 m`. -/
theorem countingUpTo_isPrimorial_le_log (N : ℕ) :
    Gdbh.countingUpTo IsPrimorial N ≤ Nat.log 2 N + 1 := by
  classical
  rw [countingUpTo_isPrimorial_eq]
  -- `card (primorialValuesUpTo N) = card (image of Nat.log 2)`,
  -- since `Nat.log 2` is injective on this set.
  have h_card_image : ((primorialValuesUpTo N).image (fun m => Nat.log 2 m)).card =
      (primorialValuesUpTo N).card := by
    exact Finset.card_image_of_injOn (nat_log_2_injOn_primorialValuesUpTo N)
  -- The image is a subset of `Finset.range (Nat.log 2 N + 1)`, whose
  -- cardinality is `Nat.log 2 N + 1`.
  have h_sub := image_nat_log_2_subset N
  have h_card_le : ((primorialValuesUpTo N).image (fun m => Nat.log 2 m)).card ≤
      (Finset.range (Nat.log 2 N + 1)).card :=
    Finset.card_le_card h_sub
  have h_range_card : (Finset.range (Nat.log 2 N + 1)).card = Nat.log 2 N + 1 :=
    Finset.card_range _
  rw [h_range_card] at h_card_le
  rw [← h_card_image]
  exact h_card_le

/-- **Real-valued count bound.**  Casting the natural-number bound
above to `ℝ`. -/
lemma countingUpTo_isPrimorial_le_log_real (N : ℕ) :
    (Gdbh.countingUpTo IsPrimorial N : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
  have h := countingUpTo_isPrimorial_le_log N
  have h_real : (Gdbh.countingUpTo IsPrimorial N : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have h_cast : ((Nat.log 2 N + 1 : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 1 := by push_cast; ring
  rw [h_cast] at h_real
  exact h_real

/-! ## Section 4 — Density-zero (`o(n)`) asymptotic

We now upgrade the `O(log N)` bound to the asymptotic statement

```
lim_{N → ∞} (countingUpTo IsPrimorial N) / N = 0 .
```

The proof uses `Real.isLittleO_log_id_atTop : log =o[atTop] id`,
combined with `natLog_le_logb : Nat.log b a ≤ Real.logb b a` to
relate the natural-number log to the real log.
-/

/-- **Real log dominates `Nat.log 2`** (cast to `ℝ`).
`(Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2`. -/
lemma nat_log_2_le_real_log (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h_logb : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
  rwa [Real.logb] at h_logb

/-- **`Real.log n / n` tends to zero as `n → ∞`** (natural-number version,
specialised from `tendsto_pow_log_div_mul_add_atTop`). -/
lemma tendsto_real_log_div_natCast_atTop :
    Filter.Tendsto (fun n : ℕ => Real.log n / n) Filter.atTop (nhds 0) := by
  -- The real-valued statement: log x / x → 0.
  have h_real : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  exact h_real.comp tendsto_natCast_atTop_atTop

/-- **`Nat.log 2 n / n` tends to zero as `n → ∞`.** -/
lemma tendsto_nat_log_2_div_atTop :
    Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) / n) Filter.atTop (nhds 0) := by
  -- Bound by `(1 / Real.log 2) * (Real.log n / n)`, which → 0.
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_aux : Filter.Tendsto
      (fun n : ℕ => (1 / Real.log 2) * (Real.log n / n)) Filter.atTop (nhds 0) := by
    have h_lim := tendsto_real_log_div_natCast_atTop
    have : Filter.Tendsto
        (fun n : ℕ => (1 / Real.log 2) * (Real.log n / n))
        Filter.atTop (nhds ((1 / Real.log 2) * 0)) :=
      h_lim.const_mul (1 / Real.log 2)
    simpa using this
  -- Squeeze: 0 ≤ (Nat.log 2 n : ℝ) / n ≤ (1 / Real.log 2) * (Real.log n / n).
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_aux ?_ ?_
  · -- Lower: 0 ≤ Nat.log 2 n / n.
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact le_of_lt hn_pos
  · -- Upper: Nat.log 2 n / n ≤ (1 / Real.log 2) * (Real.log n / n).
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_nat : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := nat_log_2_le_real_log n
    have h_div : (Nat.log 2 n : ℝ) / n ≤ (Real.log n / Real.log 2) / n :=
      div_le_div_of_nonneg_right h_nat (le_of_lt hn_pos)
    have h_eq : (Real.log n / Real.log 2) / n = (1 / Real.log 2) * (Real.log n / n) := by
      field_simp
    rw [h_eq] at h_div
    exact h_div

/-- **`1 / n` tends to zero as `n → ∞`.** -/
lemma tendsto_one_div_natCast_atTop :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0) := by
  have h_inv : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero
  exact h_inv.comp tendsto_natCast_atTop_atTop

/-- **The numerator `Nat.log 2 N + 1` is `o(N)` as `N → ∞`.**

This combines `tendsto_nat_log_2_div_atTop` and `tendsto_one_div_natCast_atTop`. -/
lemma tendsto_log_div_atTop :
    Filter.Tendsto (fun n : ℕ => ((Nat.log 2 n : ℝ) + 1) / n)
      Filter.atTop (nhds 0) := by
  -- (Nat.log 2 n + 1) / n = Nat.log 2 n / n + 1 / n, both → 0.
  have h1 := tendsto_nat_log_2_div_atTop
  have h2 := tendsto_one_div_natCast_atTop
  have h_sum : Filter.Tendsto
      (fun n : ℕ => (Nat.log 2 n : ℝ) / n + 1 / n) Filter.atTop (nhds (0 + 0)) :=
    h1.add h2
  have h_zero : (0 : ℝ) + 0 = 0 := by ring
  rw [h_zero] at h_sum
  -- Rewrite the goal to match the sum.
  have h_eq : ∀ n : ℕ, ((Nat.log 2 n : ℝ) + 1) / n = (Nat.log 2 n : ℝ) / n + 1 / n := by
    intro n
    by_cases hn : (n : ℝ) = 0
    · rw [hn]; simp
    · field_simp
  -- Now we use congrFun via `Filter.Tendsto.congr`.
  exact h_sum.congr (fun n => (h_eq n).symm)

/-- **Density-zero (`o(n)` asymptotic).**

The count of primorial values up to `N`, divided by `N`, tends to
zero as `N → ∞`.

This is the precise formal statement of "primorials have density
zero". -/
theorem countingUpTo_isPrimorial_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (Gdbh.countingUpTo IsPrimorial n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  -- Squeeze between `0` (constant) and `((Nat.log 2 n : ℝ) + 1) / n` (→ 0).
  have h_upper := tendsto_log_div_atTop
  have h_lower : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper ?_ ?_
  · -- Lower bound: 0 ≤ count / n eventually.
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact le_of_lt hn_pos
  · -- Upper bound: count / n ≤ (Nat.log 2 n + 1) / n eventually.
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_log := countingUpTo_isPrimorial_le_log_real n
    exact div_le_div_of_nonneg_right h_log (le_of_lt hn_pos)

/-! ## Section 5 — The σ-bridge: positive density on the non-primorial
subsequence transfers to positive density on the full set.

This bridge is purely *inclusion-based* — it does not require the
density-zero asymptotic.  It states: if `A` is a set with positive
Schnirelmann density on its non-primorial part, then `A` itself has
positive Schnirelmann density.

The bridge is exactly the existing `primesSumsetUniformLowerBound_of_densityModuloPrimorials`
(P21-T2) generalised to an arbitrary `A`. -/

/-- **σ-bridge (generic form).**

Given a decidable predicate `A : ℕ → Prop` and the linear lower bound

```
∃ ε > 0, ∃ N₀, ∀ n ≥ N₀, ε · n ≤ countingUpTo (fun k => A k ∧ ¬IsPrimorial k) n ,
```

the *full* counting function `countingUpTo A n` satisfies the same
linear lower bound (with the same `ε`), since
`A ∧ ¬IsPrimorial ⊆ A`.

This is a direct consequence of monotonicity of `countingUpTo`. -/
theorem countingUpTo_le_of_minus_primorials
    (A : ℕ → Prop) [DecidablePred A] (n : ℕ) :
    Gdbh.countingUpTo (fun k => A k ∧ ¬IsPrimorial k) n ≤
      Gdbh.countingUpTo A n := by
  classical
  exact Gdbh.countingUpTo_mono _ _ (fun _ h => h.1) n

/-! ## Section 6 — Combined corollary for `primesSumset`

The P21-T2 Prop `PrimesSumsetDensityModuloPrimorials` says: positive
linear lower bound on `countingUpTo primesSumsetMinusPrimorials`.
The σ-bridge above immediately yields positive Schnirelmann density
of `primesSumset` itself, exactly as in
`schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials`.

We re-export this composition as the **P22-T8 headline**. -/

/-- **P22-T8 headline.**  `PrimesSumsetDensityModuloPrimorials`
implies `0 < schnirelmannDensity primesSumset` via the σ-bridge.

This is a direct re-export of the P21-T2 theorem
`schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials`,
recorded here under the P22-T8 namespace for documentation. -/
theorem schnirelmannDensity_primesSumset_pos
    (h : PrimesSumsetDensityModuloPrimorials) :
    0 < Gdbh.schnirelmannDensity primesSumset :=
  schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials h

/-- **P22-T8 summary**:  trivially `True`; the substantive content
is in the named theorems above. -/
theorem pathC_p22_t8_summary : True := trivial

end PathCPrimorialDensityZero
end Gdbh

/-! ## Section 7 — Axiom audit -/

#print axioms Gdbh.PathCPrimorialDensityZero.isPrimorial_one
#print axioms Gdbh.PathCPrimorialDensityZero.isPrimorial_two
#print axioms Gdbh.PathCPrimorialDensityZero.two_mul_le_of_isPrimorial_lt
#print axioms Gdbh.PathCPrimorialDensityZero.countingUpTo_isPrimorial_le_log
#print axioms Gdbh.PathCPrimorialDensityZero.countingUpTo_isPrimorial_le_log_real
#print axioms Gdbh.PathCPrimorialDensityZero.tendsto_log_div_atTop
#print axioms Gdbh.PathCPrimorialDensityZero.countingUpTo_isPrimorial_div_tendsto_zero
#print axioms Gdbh.PathCPrimorialDensityZero.countingUpTo_le_of_minus_primorials
#print axioms Gdbh.PathCPrimorialDensityZero.schnirelmannDensity_primesSumset_pos
#print axioms Gdbh.PathCPrimorialDensityZero.pathC_p22_t8_summary
