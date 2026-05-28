/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T3 (Phase 6 / Path C — Mann's 1942 addition theorem, structural
decomposition).
-/
import Gdbh.PathC_SchnirelmannDensity

/-!
# Path C — Mann's 1942 addition theorem (structural decomposition)

This file lays the structural infrastructure for Mann's celebrated 1942
strengthening of Schnirelmann's addition theorem:

```
σ(A + B) ≥ min(1, σA + σB)              (Mann's inequality)
```

This is strictly stronger than Schnirelmann's
`σ(A + B) ≥ σA + σB - σA · σB` (proved in `PathC_AdditionTheorem`) — in
particular, Mann's bound reaches `1` already once `σA + σB ≥ 1`,
which is the key ingredient of the "α + β ≥ 1 implies A + B = ℕ_{≥ 1}"
half of the Schnirelmann basis closure.

## Strategy: the `e`-function decomposition

The standard proof of Mann's theorem (going back to Mann's original
paper and refined by Artin–Scherk and Dyson) introduces the
**e-function**

```
e(α, A, B, n) := max(0, A(n) + B(n) - α · n)
```

viewed as a function of the real parameter `α ∈ [0, 1]`.  The key
analytic content is:

* `eFunction` is monotone non-increasing in `α`.
* There is a unique critical value `α* ∈ [0, 1]` where `eFunction`
  changes from "eventually positive at some `n`" to "uniformly zero
  in `n`".
* At the critical `α*`, the uniform bound
  `A(n) + B(n) ≤ α* · n` for all `n ≥ 1` is precisely
  `σ(A) + σ(B) ≤ α*`, **but** the geometric injection of `A + B`
  inside `[1, n]` simultaneously gives `(A + B)(n) ≥ α* · n` — i.e.
  `σ(A + B) ≥ α* ≥ σA + σB` (when `α* ≤ 1`).
* If `α* > 1`, then the trivial bound `σ(A + B) ≤ 1` already implies
  the Mann bound, since `min(1, σA + σB) = 1`.

The actual analytic core is the "e-zero implies bound" step, which
requires Mann's clever induction on the elements of `B`.

## What this file does

This file gives a **structural decomposition** of Mann's theorem into
three named open Props plus a *fully proved* mechanical assembly
theorem, plus partial closures for the corner cases.

We deliberately keep this file independent of `PathC_AdditionTheorem`
(P6-T2) by redefining the sumset locally as `mannSumset`.  This
parallel naming is intentional: when T2's API stabilizes, a future
task can identify `mannSumset` with T2's `sumset` via a one-line
`Iff`.

We expose:

1. `mannSumset A B n` — local sumset definition.
2. `MannEFunction A B α n` — the e-function in real form.
3. `MannEFunctionMonotoneInAlpha A B` — the monotonicity Prop.
4. `MannCriticalAlphaExists A B` — existence of a critical value.
5. `MannEZeroImpliesBound A B` — at the critical value, the
   counting inequality.
6. `mannTheorem_of_components` — given all three sub-Props,
   `σ(A + B) ≥ min(1, σA + σB)`.
7. `mannTheorem_density_one_left/right` — closed corner cases.

## Constraints

All theorems are axiom-clean (only `Classical.choice, Quot.sound,
propext` from the foundation, inherited via mathlib).  No `sorry`,
`axiom`, or `admit`.  The "actual analytic content" of Mann's theorem
is exposed exactly through the three open Props — there are no hidden
admits.
-/

namespace Gdbh

open scoped BigOperators

/-! ## Local sumset (independent of T2). -/

/-- **Local sumset** for the Mann file: `mannSumset A B n` iff there
exist `a ∈ A` and `b ∈ B` with `a + b = n`.  We package the existential
over a *bounded* finite set so that decidability is inherited
automatically.  This is intentionally a parallel definition to T2's
`sumset` and can be identified with it via a one-line lemma once T2
lands. -/
def mannSumset (A B : ℕ → Prop) (n : ℕ) : Prop :=
  ∃ p : ℕ × ℕ, p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ∧
    A p.1 ∧ B p.2 ∧ p.1 + p.2 = n

instance mannSumset_decidable (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] :
    DecidablePred (mannSumset A B) := fun n => by
  unfold mannSumset
  infer_instance

/-- Rewriting `mannSumset` in a more flexible form. -/
lemma mannSumset_iff (A B : ℕ → Prop) (n : ℕ) :
    mannSumset A B n ↔ ∃ a b, A a ∧ B b ∧ a + b = n := by
  constructor
  · rintro ⟨⟨a, b⟩, _, hA, hB, hab⟩
    exact ⟨a, b, hA, hB, hab⟩
  · rintro ⟨a, b, hA, hB, hab⟩
    refine ⟨(a, b), ?_, hA, hB, hab⟩
    have ha_le : a ≤ n := by omega
    have hb_le : b ≤ n := by omega
    simp [Finset.mem_product, Finset.mem_range, ha_le, hb_le]

/-- `B ⊆ mannSumset A B` whenever `0 ∈ A`. -/
lemma mannSumset_of_mem_right {A B : ℕ → Prop} (hA : A 0)
    {n : ℕ} (hB : B n) : mannSumset A B n := by
  rw [mannSumset_iff]; exact ⟨0, n, hA, hB, by simp⟩

/-- `A ⊆ mannSumset A B` whenever `0 ∈ B`. -/
lemma mannSumset_of_mem_left {A B : ℕ → Prop} (hB : B 0)
    {n : ℕ} (hA : A n) : mannSumset A B n := by
  rw [mannSumset_iff]; exact ⟨n, 0, hA, hB, by simp⟩

/-- Schnirelmann monotonicity for `mannSumset`: `σB ≤ σ(mannSumset A B)`
whenever `0 ∈ A`. -/
theorem schnirelmannDensity_mannSumset_ge_right
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] (hA : A 0) :
    schnirelmannDensity B ≤ schnirelmannDensity (mannSumset A B) :=
  schnirelmannDensity_mono _ _ (fun _ h => mannSumset_of_mem_right hA h)

/-- Schnirelmann monotonicity for `mannSumset`: `σA ≤ σ(mannSumset A B)`
whenever `0 ∈ B`. -/
theorem schnirelmannDensity_mannSumset_ge_left
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] (hB : B 0) :
    schnirelmannDensity A ≤ schnirelmannDensity (mannSumset A B) :=
  schnirelmannDensity_mono _ _ (fun _ h => mannSumset_of_mem_left hB h)

/-! ## The Mann `e`-function. -/

/-- The Mann `e`-function: at parameter `α`, this is the deviation of
the counting function `A(n) + B(n)` from the linear lower bound
`α · n`, truncated below by `0`.

When `α = σ(A + B)`, the e-function vanishes identically — this is
the analytic content of Mann's theorem. -/
noncomputable def MannEFunction (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (α : ℝ) (n : ℕ) : ℝ :=
  max 0 ((countingUpTo A n : ℝ) + (countingUpTo B n : ℝ) - α * (n : ℝ))

/-- Basic positivity: `MannEFunction A B α n ≥ 0`. -/
lemma mannEFunction_nonneg (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (α : ℝ) (n : ℕ) : 0 ≤ MannEFunction A B α n := by
  unfold MannEFunction; exact le_max_left _ _

/-- The e-function is monotone non-increasing in `α`. -/
lemma mannEFunction_antitone_in_alpha (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] (n : ℕ)
    {α β : ℝ} (h : α ≤ β) :
    MannEFunction A B β n ≤ MannEFunction A B α n := by
  unfold MannEFunction
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h_mul : α * (n : ℝ) ≤ β * (n : ℝ) :=
    mul_le_mul_of_nonneg_right h hn_nonneg
  -- max 0 (X - β n) ≤ max 0 (X - α n)
  apply max_le_max le_rfl
  linarith

/-- At `α = 0`, the e-function equals the unweighted count
`A(n) + B(n)` (which is ≥ 0). -/
lemma mannEFunction_at_zero (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] (n : ℕ) :
    MannEFunction A B 0 n = (countingUpTo A n : ℝ) + (countingUpTo B n : ℝ) := by
  unfold MannEFunction
  have hcA : (0 : ℝ) ≤ (countingUpTo A n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hcB : (0 : ℝ) ≤ (countingUpTo B n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_nn : (0 : ℝ) ≤ (countingUpTo A n : ℝ) + (countingUpTo B n : ℝ) - 0 * (n : ℝ) := by
    have : (0 : ℝ) * (n : ℝ) = 0 := by ring
    linarith
  rw [max_eq_right h_nn]
  ring

/-! ## The three sub-Props underlying Mann's theorem.

Each one is the named analytic content of a step in the standard
proof.  We state them as `Prop`s so they can be referenced as
hypotheses for the assembly theorem without committing to a proof. -/

/-- **Sub-Prop 1**: the e-function `MannEFunction A B α n` is
non-increasing in `α` uniformly in `n`.  This is the trivial
direction (proved above as `mannEFunction_antitone_in_alpha`); we
expose it as a Prop for the assembly's signature. -/
def MannEFunctionMonotoneInAlpha (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] : Prop :=
  ∀ (n : ℕ) ⦃α β : ℝ⦄, α ≤ β →
    MannEFunction A B β n ≤ MannEFunction A B α n

/-- **Sub-Prop 2**: there exists a critical `α*` ∈ `[0, 1]` such that
the e-function is uniformly zero in `n` for `α = α*`, and `α*` is at
least `min(1, σA + σB)`.

Geometrically, `α*` is the *Schnirelmann density of the sumset*, and
Mann's theorem says `α* ≥ min(1, σA + σB)`. -/
def MannCriticalAlphaExists (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
    (∀ n : ℕ, MannEFunction A B α n = 0) ∧
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ α

/-- **Sub-Prop 3**: at the critical `α*`, the uniform vanishing of
the e-function implies the corresponding counting bound on the
sumset; i.e., `A(n) + B(n) ≤ α* · n` together with the gap injection
gives `(mannSumset A B)(n) ≥ α* · n` for `n ≥ 1`.

This is the analytic core of Mann's proof — the induction on the
elements of `B`. -/
def MannEZeroImpliesBound (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] : Prop :=
  ∀ α : ℝ, (∀ n : ℕ, MannEFunction A B α n = 0) →
    ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ≤ (countingUpTo (mannSumset A B) n : ℝ)

/-! ## Trivially closable variants.

Sub-Prop 1 is the easy direction and we provide a closure form
of it.  The genuine open content lives in Sub-Props 2 and 3. -/

/-- The monotone-in-α sub-Prop holds unconditionally. -/
theorem mannEFunctionMonotoneInAlpha_holds (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B] :
    MannEFunctionMonotoneInAlpha A B :=
  fun n _ _ h => mannEFunction_antitone_in_alpha A B n h

/-! ## The mechanical assembly theorem.

This is the fully-proved closure: given the three sub-Props, we
derive Mann's inequality.  The mathematical content is concentrated
in `MannEZeroImpliesBound`. -/

section Assembly

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- **Mann's theorem from sub-Props**.  Given:

* `MannEFunctionMonotoneInAlpha A B`,
* `MannCriticalAlphaExists A B`,
* `MannEZeroImpliesBound A B`,

we conclude `σ(mannSumset A B) ≥ min(1, σA + σB)`. -/
theorem mannTheorem_of_components
    (_hMono : MannEFunctionMonotoneInAlpha A B)
    (hCrit : MannCriticalAlphaExists A B)
    (hEzero : MannEZeroImpliesBound A B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
      schnirelmannDensity (mannSumset A B) := by
  -- Unpack the critical α.
  rcases hCrit with ⟨α, _hα_nn, _hα_le1, hα_zero, hα_ge⟩
  -- Use hEzero at α: ∀ n ≥ 1, α n ≤ (mannSumset A B)(n).
  have h_count : ∀ n : ℕ, 1 ≤ n →
      α * (n : ℝ) ≤ (countingUpTo (mannSumset A B) n : ℝ) := hEzero α hα_zero
  -- This is exactly the lower-density hypothesis for σ(A + B).
  have h_sum_ge_α : α ≤ schnirelmannDensity (mannSumset A B) :=
    schnirelmannDensity_ge_of_counting_ge (mannSumset A B) h_count
  exact le_trans hα_ge h_sum_ge_α

end Assembly

/-! ## Honest partial closures.

These are corner cases we can close *without* the genuine analytic
content of Sub-Props 2 and 3.  They serve to make the structure
honest: we cover the trivial cases here, leaving the non-trivial
inequality exposed exactly as the conjunction of the open Props. -/

section Corners

variable (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]

/-- **Trivial Mann bound when σA + σB ≤ 0**: in this case both
densities are zero, and `min(1, σA + σB) = 0 ≤ σ(mannSumset A B)`. -/
theorem mannTheorem_when_sum_nonpos
    (h : schnirelmannDensity A + schnirelmannDensity B ≤ 0) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
      schnirelmannDensity (mannSumset A B) := by
  have h_nn := schnirelmannDensity_nonneg (mannSumset A B)
  have h_min_nonpos : min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ 0 :=
    (min_le_right _ _).trans h
  linarith

/-- If `σA = 1` and `0 ∈ B`, then `σ(mannSumset A B) = 1`. -/
theorem mannTheorem_when_density_one_left (hB : B 0)
    (hA1 : schnirelmannDensity A = 1) :
    1 ≤ schnirelmannDensity (mannSumset A B) := by
  have h_le : schnirelmannDensity A ≤ schnirelmannDensity (mannSumset A B) :=
    schnirelmannDensity_mannSumset_ge_left A B hB
  linarith

/-- Symmetric version: if `σB = 1` and `0 ∈ A`, then
`σ(mannSumset A B) = 1`. -/
theorem mannTheorem_when_density_one_right (hA : A 0)
    (hB1 : schnirelmannDensity B = 1) :
    1 ≤ schnirelmannDensity (mannSumset A B) := by
  have h_le : schnirelmannDensity B ≤ schnirelmannDensity (mannSumset A B) :=
    schnirelmannDensity_mannSumset_ge_right A B hA
  linarith

/-- **Mann's theorem in the `σA = 1` corner**: regardless of `B` (with
`0 ∈ B`), `σ(mannSumset A B) ≥ min(1, σA + σB) = 1`, hence equals `1`. -/
theorem mannTheorem_density_one_left (hB : B 0)
    (hA1 : schnirelmannDensity A = 1) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
      schnirelmannDensity (mannSumset A B) := by
  have h1 : 1 ≤ schnirelmannDensity (mannSumset A B) :=
    mannTheorem_when_density_one_left A B hB hA1
  have h_min_le_one : min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ 1 :=
    min_le_left _ _
  linarith

/-- Symmetric: in the `σB = 1` corner, Mann's bound is `1` and is
closed by the monotone inclusion. -/
theorem mannTheorem_density_one_right (hA : A 0)
    (hB1 : schnirelmannDensity B = 1) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
      schnirelmannDensity (mannSumset A B) := by
  have h1 : 1 ≤ schnirelmannDensity (mannSumset A B) :=
    mannTheorem_when_density_one_right A B hA hB1
  have h_min_le_one : min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ 1 :=
    min_le_left _ _
  linarith

end Corners

/-! ## The `min(1, σA + σB)` bound, written as an open conjecture.

We expose Mann's theorem in its final form as a *named Prop*.  In
the present file this Prop is **not** unconditionally closed; it is
shown to follow from the three sub-Props via
`mannTheorem_of_components`, and partial closures are provided for
the corners.

The full closure is deferred to a future Phase 7 task on the actual
analytic content of Mann's induction. -/

/-- **Mann's theorem (statement)**: `σ(mannSumset A B) ≥ min(1, σA + σB)`
whenever `0 ∈ A ∩ B`. -/
def MannInequality (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] : Prop :=
  A 0 → B 0 → min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
    schnirelmannDensity (mannSumset A B)

/-- **Skeleton closure of Mann's inequality from the three sub-Props**.

This is the abstract form of `mannTheorem_of_components`, packaged
as a closure of `MannInequality`.  It is fully proved (modulo the
named open Props). -/
theorem mannInequality_of_components (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B]
    (hMono : MannEFunctionMonotoneInAlpha A B)
    (hCrit : MannCriticalAlphaExists A B)
    (hEzero : MannEZeroImpliesBound A B) :
    MannInequality A B := by
  intro _ _
  exact mannTheorem_of_components A B hMono hCrit hEzero

/-- **Sharp comparison with Schnirelmann's bound**.  Mann's bound
`min(1, σA + σB)` is at least Schnirelmann's
`σA + σB - σA · σB` whenever both densities are in `[0, 1]`.

This makes Mann's strengthening explicit at the level of bounds. -/
theorem mann_bound_ge_schnirelmann_bound
    (α β : ℝ) (hα_nn : 0 ≤ α) (hα_le : α ≤ 1) (hβ_nn : 0 ≤ β) (_hβ_le : β ≤ 1) :
    α + β - α * β ≤ min 1 (α + β) := by
  -- Schnirelmann's bound = α + β - αβ.  Mann's bound = min(1, α + β).
  -- We need: α + β - αβ ≤ min(1, α + β).
  refine le_min ?_ ?_
  · -- α + β - αβ ≤ 1.  Equivalent to (1 - α)(1 - β) ≥ 0.
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) (by linarith : (0 : ℝ) ≤ 1 - β)
    nlinarith
  · -- α + β - αβ ≤ α + β.  Equivalent to αβ ≥ 0.
    have h := mul_nonneg hα_nn hβ_nn
    linarith

/-- **Quantitative gap**: Mann's bound exceeds Schnirelmann's bound by
exactly `σA · σB` whenever `σA + σB ≤ 1`. -/
theorem mann_bound_eq_schnirelmann_plus_product_of_sum_le_one
    (α β : ℝ) (_hα_nn : 0 ≤ α) (_hβ_nn : 0 ≤ β)
    (h_sum_le : α + β ≤ 1) :
    min 1 (α + β) = (α + β - α * β) + α * β := by
  have h_min : min 1 (α + β) = α + β := min_eq_right h_sum_le
  rw [h_min]; ring

/-- **Triviality in the `σA + σB ≥ 1` regime, given closure**: Mann's
bound is `1`, which is also the trivial upper bound on any
Schnirelmann density when we know `σ(mannSumset A B) ≥ 1`. -/
theorem mannInequality_when_sum_ge_one (A B : ℕ → Prop)
    [DecidablePred A] [DecidablePred B]
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B)
    (h_sumset : 1 ≤ schnirelmannDensity (mannSumset A B)) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤
      schnirelmannDensity (mannSumset A B) := by
  have h_min : min 1 (schnirelmannDensity A + schnirelmannDensity B) = 1 :=
    min_eq_left h
  rw [h_min]; exact h_sumset

/-! ## Status summary.

In this file:

* `mannSumset` and its decidability/monotonicity are **closed**.
* `MannEFunctionMonotoneInAlpha A B` is **closed**
  (`mannEFunctionMonotoneInAlpha_holds`).
* `MannCriticalAlphaExists A B` is an **open Prop**.
* `MannEZeroImpliesBound A B` is an **open Prop**.
* `mannTheorem_of_components` is **closed** (mechanical assembly).
* `mannInequality_of_components` is **closed** (Prop-level closure).
* Corner cases (densities `0` or `1`) are closed via Schnirelmann
  monotonicity.

The genuine open content is exactly the conjunction
`MannCriticalAlphaExists ∧ MannEZeroImpliesBound`, which is the
analytic / induction-on-elements core of Mann's 1942 argument.
This is left as a named target for Phase 7.
-/

end Gdbh
