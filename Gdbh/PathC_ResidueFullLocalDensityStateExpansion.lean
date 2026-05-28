/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueFullLocalDensityPairState

/-!
# Path C -- fixed-union state expansion

Round 17 closed pair-state factorization.  This file narrows the remaining
fixed-union state-product residual to one purely finite bijection: the fiber
of ordered pairs with union `u` versus assignments of each prime in `u` to one
of the three states first-only, second-only, or both.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityStateExpansion

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueFullLocalDensityStateProduct
  (ResidueSignedUnionFiberStateProductExpansion
   ResidueSignedUnionFiberStateProductExpansionAtSqrt
   residueSignedUnionFiberStateProductExpansionAtSqrt_of_all
   residueSignedPairPrimeStateFactor)
open Gdbh.PathCResidueFullLocalDensityFiberProduct
  (ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation
   ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt
   residueSignedUnionPrimeFiberFactor)
open Gdbh.PathCResidueFullLocalDensityPairState
  (residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_stateExpansion
   residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_stateExpansion
   residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_stateExpansion
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_stateExpansion
   residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_stateExpansion
   residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_stateExpansion)

/-! ## Pure fixed-union sums -/

/-- The fixed-union pair-state sum stripped of its ambient `residuePrimeSet z`.
Every ordered pair is now drawn from `u.powerset`. -/
noncomputable def residueUnionPairStateSum (n : ℕ) (u : Finset ℕ) : ℝ :=
  ∑ pair ∈ (u.powerset ×ˢ u.powerset).filter
      (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
    ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2

/-- Local contribution of one prime in a three-state assignment:
first-only, second-only, or both. -/
noncomputable def residuePairStateChoiceFactor
    (n p : ℕ) (state : Fin 3) : ℝ :=
  if state = 0 then
    -(1 / (p : ℝ))
  else if state = 1 then
    -(1 / (p : ℝ))
  else if p ∣ n then
    1 / (p : ℝ)
  else
    0

/-- The sum over all assignments of each `p ∈ u` to one of the three pair
states.  This is the product-expanded form of the local state sums. -/
noncomputable def residueUnionStateAssignmentSum
    (n : ℕ) (u : Finset ℕ) : ℝ :=
  ∑ σ : ({p // p ∈ u} → Fin 3),
    ∏ p : {p // p ∈ u}, residuePairStateChoiceFactor n p.1 (σ p)

/-! ## Smaller residuals -/

/-- Ambient reduction: the original fixed-union sum over `residuePrimeSet z`
is the same sum over `u.powerset`, provided `u ⊆ residuePrimeSet z`. -/
def ResidueSignedUnionFiberStateAmbientReduction : Prop :=
  ∀ n z : ℕ, ∀ u ∈ (residuePrimeSet z).powerset,
    (∑ pair ∈ ((residuePrimeSet z).powerset ×ˢ
        (residuePrimeSet z).powerset).filter
          (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u),
        ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2)
      = residueUnionPairStateSum n u

/-- The remaining pure finite-combinatorics residual: identify the
fixed-union ordered-pair fiber with the three-state assignment sum. -/
def ResidueSignedUnionFiberStateAssignmentReduction : Prop :=
  ∀ n : ℕ, ∀ u : Finset ℕ,
    residueUnionPairStateSum n u = residueUnionStateAssignmentSum n u

/-! ## The finite state-assignment bijection -/

/-- The fixed-union ordered-pair fiber. -/
noncomputable def residuePairStateFiber
    (u : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (u.powerset ×ˢ u.powerset).filter
    (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u)

/-- The first divisor set encoded by a three-state assignment. -/
noncomputable def residueStateAssignmentFirstSet
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) : Finset ℕ :=
  (u.attach.filter (fun p => σ p = 0 ∨ σ p = 2)).image Subtype.val

/-- The second divisor set encoded by a three-state assignment. -/
noncomputable def residueStateAssignmentSecondSet
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) : Finset ℕ :=
  (u.attach.filter (fun p => σ p = 1 ∨ σ p = 2)).image Subtype.val

/-- Convert a fixed-union ordered pair to its pointwise three-state
assignment. -/
noncomputable def residuePairToStateAssignment
    (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ) :
    ({p // p ∈ u} → Fin 3) :=
  fun p =>
    if p.1 ∈ pair.1 then
      if p.1 ∈ pair.2 then 2 else 0
    else
      1

/-- Convert a three-state assignment back to its ordered pair. -/
noncomputable def residueStateAssignmentToPair
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) :
    Finset ℕ × Finset ℕ :=
  (residueStateAssignmentFirstSet u σ,
    residueStateAssignmentSecondSet u σ)

private lemma mem_residueStateAssignmentFirstSet
    {u : Finset ℕ} {σ : ({p // p ∈ u} → Fin 3)} {p : ℕ} :
    p ∈ residueStateAssignmentFirstSet u σ ↔
      ∃ hp : p ∈ u, σ ⟨p, hp⟩ = 0 ∨ σ ⟨p, hp⟩ = 2 := by
  classical
  unfold residueStateAssignmentFirstSet
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨q, hq, rfl⟩
    exact ⟨q.2, by simpa using (Finset.mem_filter.mp hq).2⟩
  · rintro ⟨hp, hstate⟩
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, by simpa using hstate, rfl⟩

private lemma mem_residueStateAssignmentSecondSet
    {u : Finset ℕ} {σ : ({p // p ∈ u} → Fin 3)} {p : ℕ} :
    p ∈ residueStateAssignmentSecondSet u σ ↔
      ∃ hp : p ∈ u, σ ⟨p, hp⟩ = 1 ∨ σ ⟨p, hp⟩ = 2 := by
  classical
  unfold residueStateAssignmentSecondSet
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨q, hq, rfl⟩
    exact ⟨q.2, by simpa using (Finset.mem_filter.mp hq).2⟩
  · rintro ⟨hp, hstate⟩
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, by simpa using hstate, rfl⟩

private lemma fin3_eq_zero_or_one_or_two (x : Fin 3) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

private lemma residueStateAssignment_first_union_second
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) :
    residueStateAssignmentFirstSet u σ ∪
        residueStateAssignmentSecondSet u σ = u := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hfirst | hsecond
    · exact (mem_residueStateAssignmentFirstSet.mp hfirst).1
    · exact (mem_residueStateAssignmentSecondSet.mp hsecond).1
  · intro hp
    have hstate :
        σ ⟨p, hp⟩ = 0 ∨ σ ⟨p, hp⟩ = 1 ∨ σ ⟨p, hp⟩ = 2 :=
      fin3_eq_zero_or_one_or_two (σ ⟨p, hp⟩)
    rcases hstate with h0 | h1 | h2
    · exact Finset.mem_union.mpr
        (Or.inl (mem_residueStateAssignmentFirstSet.mpr
          ⟨hp, Or.inl h0⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (mem_residueStateAssignmentSecondSet.mpr
          ⟨hp, Or.inl h1⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (mem_residueStateAssignmentFirstSet.mpr
          ⟨hp, Or.inr h2⟩))

private lemma residueStateAssignmentToPair_mem_fiber
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) :
    residueStateAssignmentToPair u σ ∈ residuePairStateFiber u := by
  classical
  have hfirst_sub : residueStateAssignmentFirstSet u σ ⊆ u := by
    intro p hp
    exact (mem_residueStateAssignmentFirstSet.mp hp).1
  have hsecond_sub : residueStateAssignmentSecondSet u σ ⊆ u := by
    intro p hp
    exact (mem_residueStateAssignmentSecondSet.mp hp).1
  unfold residuePairStateFiber residueStateAssignmentToPair
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hfirst_sub,
       Finset.mem_powerset.mpr hsecond_sub⟩,
     residueStateAssignment_first_union_second u σ⟩

private lemma residueStateAssignmentFirstSet_pairToState_eq_left
    (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ)
    (hUnion : pair.1 ∪ pair.2 = u) :
    residueStateAssignmentFirstSet u
        (residuePairToStateAssignment u pair) = pair.1 := by
  classical
  ext p
  constructor
  · intro h
    rcases mem_residueStateAssignmentFirstSet.mp h with ⟨hpU, hstate⟩
    by_cases hp₁ : p ∈ pair.1
    · exact hp₁
    · have hp₂ : p ∈ pair.2 := by
        have hpUnion : p ∈ pair.1 ∪ pair.2 := by
          simpa [hUnion] using hpU
        exact (Finset.mem_union.mp hpUnion).resolve_left hp₁
      unfold residuePairToStateAssignment at hstate
      simp [hp₁] at hstate
  · intro hp₁
    have hpU : p ∈ u := by
      have hpUnion : p ∈ pair.1 ∪ pair.2 :=
        Finset.mem_union.mpr (Or.inl hp₁)
      simpa [hUnion] using hpUnion
    by_cases hp₂ : p ∈ pair.2
    · exact mem_residueStateAssignmentFirstSet.mpr
        ⟨hpU, Or.inr (by
          simp [residuePairToStateAssignment, hp₁, hp₂])⟩
    · exact mem_residueStateAssignmentFirstSet.mpr
        ⟨hpU, Or.inl (by
          simp [residuePairToStateAssignment, hp₁, hp₂])⟩

private lemma residueStateAssignmentSecondSet_pairToState_eq_right
    (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ)
    (hUnion : pair.1 ∪ pair.2 = u) :
    residueStateAssignmentSecondSet u
        (residuePairToStateAssignment u pair) = pair.2 := by
  classical
  ext p
  constructor
  · intro h
    rcases mem_residueStateAssignmentSecondSet.mp h with ⟨hpU, hstate⟩
    by_cases hp₂ : p ∈ pair.2
    · exact hp₂
    · have hp₁ : p ∈ pair.1 := by
        have hpUnion : p ∈ pair.1 ∪ pair.2 := by
          simpa [hUnion] using hpU
        exact (Finset.mem_union.mp hpUnion).resolve_right hp₂
      unfold residuePairToStateAssignment at hstate
      simp [hp₁, hp₂] at hstate
  · intro hp₂
    have hpU : p ∈ u := by
      have hpUnion : p ∈ pair.1 ∪ pair.2 :=
        Finset.mem_union.mpr (Or.inr hp₂)
      simpa [hUnion] using hpUnion
    by_cases hp₁ : p ∈ pair.1
    · exact mem_residueStateAssignmentSecondSet.mpr
        ⟨hpU, Or.inr (by
          simp [residuePairToStateAssignment, hp₁, hp₂])⟩
    · exact mem_residueStateAssignmentSecondSet.mpr
        ⟨hpU, Or.inl (by
          simp [residuePairToStateAssignment, hp₁])⟩

private lemma residueStateAssignmentToPair_pairToState_eq_pair
    (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ)
    (hUnion : pair.1 ∪ pair.2 = u) :
    residueStateAssignmentToPair u
        (residuePairToStateAssignment u pair) = pair := by
  ext <;> simp [residueStateAssignmentToPair,
    residueStateAssignmentFirstSet_pairToState_eq_left u pair hUnion,
    residueStateAssignmentSecondSet_pairToState_eq_right u pair hUnion]

private lemma residuePairToState_stateAssignmentToPair_eq
    (u : Finset ℕ) (σ : ({p // p ∈ u} → Fin 3)) :
    residuePairToStateAssignment u
        (residueStateAssignmentToPair u σ) = σ := by
  classical
  funext p
  rcases fin3_eq_zero_or_one_or_two (σ p) with h0 | h1 | h2
  · have hfirst : p.1 ∈ residueStateAssignmentFirstSet u σ :=
      mem_residueStateAssignmentFirstSet.mpr ⟨p.2, Or.inl h0⟩
    have hsecond : p.1 ∉ residueStateAssignmentSecondSet u σ := by
      intro hs
      rcases mem_residueStateAssignmentSecondSet.mp hs with
        ⟨hp, hs1 | hs2⟩
      · have heq : (⟨p.1, hp⟩ : {p // p ∈ u}) = p :=
          Subtype.ext rfl
        simp [heq, h0] at hs1
      · have heq : (⟨p.1, hp⟩ : {p // p ∈ u}) = p :=
          Subtype.ext rfl
        simp [heq, h0] at hs2
    unfold residuePairToStateAssignment residueStateAssignmentToPair
    simp [hfirst, hsecond, h0]
  · have hfirst : p.1 ∉ residueStateAssignmentFirstSet u σ := by
      intro hf
      rcases mem_residueStateAssignmentFirstSet.mp hf with
        ⟨hp, hf0 | hf2⟩
      · have heq : (⟨p.1, hp⟩ : {p // p ∈ u}) = p :=
          Subtype.ext rfl
        simp [heq, h1] at hf0
      · have heq : (⟨p.1, hp⟩ : {p // p ∈ u}) = p :=
          Subtype.ext rfl
        simp [heq, h1] at hf2
    unfold residuePairToStateAssignment residueStateAssignmentToPair
    simp [hfirst, h1]
  · have hfirst : p.1 ∈ residueStateAssignmentFirstSet u σ :=
      mem_residueStateAssignmentFirstSet.mpr ⟨p.2, Or.inr h2⟩
    have hsecond : p.1 ∈ residueStateAssignmentSecondSet u σ :=
      mem_residueStateAssignmentSecondSet.mpr ⟨p.2, Or.inr h2⟩
    unfold residuePairToStateAssignment residueStateAssignmentToPair
    simp [hfirst, hsecond, h2]

/-- The fixed-union ordered-pair fiber is equivalent to three-state
assignments on `u`. -/
noncomputable def residuePairStateFiberEquivAssignment
    (u : Finset ℕ) :
    {pair // pair ∈ residuePairStateFiber u} ≃
      ({p // p ∈ u} → Fin 3) where
  toFun pair := residuePairToStateAssignment u pair.1
  invFun σ :=
    ⟨residueStateAssignmentToPair u σ,
      residueStateAssignmentToPair_mem_fiber u σ⟩
  left_inv pair := by
    apply Subtype.ext
    exact residueStateAssignmentToPair_pairToState_eq_pair u pair.1
      (Finset.mem_filter.mp pair.2).2
  right_inv σ := residuePairToState_stateAssignmentToPair_eq u σ

private lemma residuePairStateFactor_eq_choice_of_union
    (n : ℕ) (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ)
    (hUnion : pair.1 ∪ pair.2 = u) (p : {p // p ∈ u}) :
    residueSignedPairPrimeStateFactor n p.1 pair.1 pair.2 =
      residuePairStateChoiceFactor n p.1
        (residuePairToStateAssignment u pair p) := by
  classical
  by_cases hp₁ : p.1 ∈ pair.1
  · by_cases hp₂ : p.1 ∈ pair.2
    · have hpI : p.1 ∈ pair.1 ∩ pair.2 :=
        Finset.mem_inter.mpr ⟨hp₁, hp₂⟩
      unfold residuePairToStateAssignment residuePairStateChoiceFactor
      simp [residueSignedPairPrimeStateFactor, hp₁, hp₂, hpI]
    · have hpI : p.1 ∉ pair.1 ∩ pair.2 := by
        intro h
        exact hp₂ (Finset.mem_inter.mp h).2
      unfold residuePairToStateAssignment residuePairStateChoiceFactor
      simp [residueSignedPairPrimeStateFactor, hp₁, hp₂, hpI]
  · have hp₂ : p.1 ∈ pair.2 := by
      have hpU : p.1 ∈ pair.1 ∪ pair.2 := by
        rw [hUnion]
        exact p.2
      exact (Finset.mem_union.mp hpU).resolve_left hp₁
    have hpI : p.1 ∉ pair.1 ∩ pair.2 := by
      intro h
      exact hp₁ (Finset.mem_inter.mp h).1
    unfold residuePairToStateAssignment residuePairStateChoiceFactor
    simp [residueSignedPairPrimeStateFactor, hp₁, hp₂, hpI]

private lemma residuePairStateProduct_eq_assignmentProduct
    (n : ℕ) (u : Finset ℕ) (pair : Finset ℕ × Finset ℕ)
    (hUnion : pair.1 ∪ pair.2 = u) :
    (∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2) =
      ∏ p : {p // p ∈ u},
        residuePairStateChoiceFactor n p.1
          (residuePairToStateAssignment u pair p) := by
  classical
  calc
    (∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2)
        = ∏ p : {p // p ∈ u},
            residueSignedPairPrimeStateFactor n p.1 pair.1 pair.2 := by
          simpa using (Finset.prod_attach (s := u)
            (f := fun p : ℕ =>
              residueSignedPairPrimeStateFactor n p pair.1 pair.2)).symm
    _ = ∏ p : {p // p ∈ u},
          residuePairStateChoiceFactor n p.1
            (residuePairToStateAssignment u pair p) := by
          refine Finset.prod_congr rfl ?_
          intro p _hp
          exact residuePairStateFactor_eq_choice_of_union n u pair hUnion p

/-! ## Closed ambient and product-expansion pieces -/

/-- The ambient `P` in the Round 16 residual can be removed once the fixed
union `u` is known to be a subset of `P`. -/
theorem residueSignedUnionFiberStateAmbientReduction :
    ResidueSignedUnionFiberStateAmbientReduction := by
  classical
  intro n z u hu
  let P : Finset ℕ := residuePrimeSet z
  have huP : u ⊆ P := Finset.mem_powerset.mp hu
  have hset :
      (P.powerset ×ˢ P.powerset).filter
          (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u) =
        (u.powerset ×ˢ u.powerset).filter
          (fun pair : Finset ℕ × Finset ℕ => pair.1 ∪ pair.2 = u) := by
    ext pair
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpair, hUnion⟩
      rcases Finset.mem_product.mp hpair with ⟨_h₁P, _h₂P⟩
      have h₁u : pair.1 ⊆ u := by
        intro x hx
        have hxU : x ∈ pair.1 ∪ pair.2 := Finset.mem_union.mpr (Or.inl hx)
        simpa [hUnion] using hxU
      have h₂u : pair.2 ⊆ u := by
        intro x hx
        have hxU : x ∈ pair.1 ∪ pair.2 := Finset.mem_union.mpr (Or.inr hx)
        simpa [hUnion] using hxU
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr h₁u, Finset.mem_powerset.mpr h₂u⟩,
          hUnion⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpair, hUnion⟩
      rcases Finset.mem_product.mp hpair with ⟨h₁u, h₂u⟩
      have h₁P : pair.1 ⊆ P := (Finset.mem_powerset.mp h₁u).trans huP
      have h₂P : pair.2 ⊆ P := (Finset.mem_powerset.mp h₂u).trans huP
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr h₁P, Finset.mem_powerset.mpr h₂P⟩,
          hUnion⟩
  dsimp [P] at hset
  unfold residueUnionPairStateSum
  rw [hset]

/-- The three state choices at one prime add up to the local union-fiber
factor. -/
theorem residuePairStateChoiceFactor_sum_eq_unionPrimeFactor
    (n p : ℕ) :
    (∑ state : Fin 3, residuePairStateChoiceFactor n p state) =
      residueSignedUnionPrimeFiberFactor n p := by
  rw [Fin.sum_univ_three]
  unfold residuePairStateChoiceFactor residueSignedUnionPrimeFiberFactor
  by_cases hp : p ∣ n
  · simp [hp]
  · simp [hp]
    ring

/-- The assignment sum is exactly the product of the one-prime union-fiber
factors. -/
theorem residueUnionStateAssignmentSum_eq_primeFiberProduct
    (n : ℕ) (u : Finset ℕ) :
    residueUnionStateAssignmentSum n u =
      ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p := by
  classical
  unfold residueUnionStateAssignmentSum
  calc
    (∑ σ : ({p // p ∈ u} → Fin 3),
        ∏ p : {p // p ∈ u}, residuePairStateChoiceFactor n p.1 (σ p))
        = ∏ p : {p // p ∈ u},
            ∑ state : Fin 3, residuePairStateChoiceFactor n p.1 state := by
          exact (Fintype.prod_sum
            (f := fun p : {p // p ∈ u} =>
              fun state : Fin 3 => residuePairStateChoiceFactor n p.1 state)).symm
    _ = ∏ p : {p // p ∈ u}, residueSignedUnionPrimeFiberFactor n p.1 := by
          refine Finset.prod_congr rfl ?_
          intro p _hp
          exact residuePairStateChoiceFactor_sum_eq_unionPrimeFactor n p.1
    _ = ∏ p ∈ u, residueSignedUnionPrimeFiberFactor n p := by
          simpa using (Finset.prod_attach (s := u)
            (f := fun p : ℕ => residueSignedUnionPrimeFiberFactor n p))

/-- The fixed-union ordered-pair fiber equals the three-state assignment sum. -/
theorem residueSignedUnionFiberStateAssignmentReduction :
    ResidueSignedUnionFiberStateAssignmentReduction := by
  classical
  intro n u
  let F : Finset ℕ × Finset ℕ → ℝ :=
    fun pair =>
      ∏ p ∈ u, residueSignedPairPrimeStateFactor n p pair.1 pair.2
  let G : ({p // p ∈ u} → Fin 3) → ℝ :=
    fun σ =>
      ∏ p : {p // p ∈ u}, residuePairStateChoiceFactor n p.1 (σ p)
  calc
    residueUnionPairStateSum n u
        = ∑ pair : {pair // pair ∈ residuePairStateFiber u},
            F pair.1 := by
          unfold residueUnionPairStateSum residuePairStateFiber F
          simpa using
            (Finset.sum_attach (residuePairStateFiber u)
              (fun pair : Finset ℕ × Finset ℕ =>
                ∏ p ∈ u,
                  residueSignedPairPrimeStateFactor n p pair.1 pair.2)).symm
    _ = ∑ σ : ({p // p ∈ u} → Fin 3), G σ := by
          exact Fintype.sum_equiv (residuePairStateFiberEquivAssignment u)
            (fun pair : {pair // pair ∈ residuePairStateFiber u} =>
              F pair.1)
            G
            (by
              intro pair
              have hUnion : pair.1.1 ∪ pair.1.2 = u :=
                (Finset.mem_filter.mp pair.2).2
              exact residuePairStateProduct_eq_assignmentProduct
                n u pair.1 hUnion)
    _ = residueUnionStateAssignmentSum n u := by
          rfl

/-! ## Bridges to the Round 16 residual -/

/-- The pure assignment-reduction residual closes the Round 16 all-level
state-product expansion. -/
theorem residueSignedUnionFiberStateProductExpansion_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    ResidueSignedUnionFiberStateProductExpansion := by
  classical
  intro n z u hu
  rw [residueSignedUnionFiberStateAmbientReduction n z u hu]
  rw [hAssign n u]
  exact residueUnionStateAssignmentSum_eq_primeFiberProduct n u

/-- The pure assignment-reduction residual closes the at-sqrt state-product
expansion via all-level specialization. -/
theorem residueSignedUnionFiberStateProductExpansionAtSqrt_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    ResidueSignedUnionFiberStateProductExpansionAtSqrt :=
  residueSignedUnionFiberStateProductExpansionAtSqrt_of_all
    (residueSignedUnionFiberStateProductExpansion_of_assignmentReduction hAssign)

/-- Closed all-level state-product expansion. -/
theorem residueSignedUnionFiberStateProductExpansion :
    ResidueSignedUnionFiberStateProductExpansion :=
  residueSignedUnionFiberStateProductExpansion_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- Closed at-sqrt state-product expansion. -/
theorem residueSignedUnionFiberStateProductExpansionAtSqrt :
    ResidueSignedUnionFiberStateProductExpansionAtSqrt :=
  residueSignedUnionFiberStateProductExpansionAtSqrt_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- With pair-state factorization already closed, the pure assignment
residual closes the product-form fiber target. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansion_of_assignmentReduction hAssign)

/-- At-sqrt product-form fiber bridge from the pure assignment residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansionAtSqrt_of_assignmentReduction hAssign)

/-- Closed product-form fiber target. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- Closed at-sqrt product-form fiber target. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt :
    ResidueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluationAtSqrt_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- The pure assignment residual closes the Round 14 fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    Gdbh.PathCResidueFullLocalDensityUnionFiber.ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansion_of_assignmentReduction hAssign)

/-- Closed Round 14 fiber residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedFiberEvaluation :
    Gdbh.PathCResidueFullLocalDensityUnionFiber.ResidueDoubleDivisorFullLocalDensitySignedFiberEvaluation :=
  residueDoubleDivisorFullLocalDensitySignedFiberEvaluation_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- The pure assignment residual closes the signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedUnionReduction :=
  residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansion_of_assignmentReduction hAssign)

/-- Closed signed union reduction. -/
theorem residueDoubleDivisorFullLocalDensitySignedUnionReduction :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedUnionReduction :=
  residueDoubleDivisorFullLocalDensitySignedUnionReduction_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- The pure assignment residual closes the signed prime-factorization
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansion_of_assignmentReduction hAssign)

/-- Closed signed prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorization :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorization :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorization_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

/-- At-sqrt signed prime-factorization bridge from the pure assignment
residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_assignmentReduction
    (hAssign : ResidueSignedUnionFiberStateAssignmentReduction) :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_stateExpansion
    (residueSignedUnionFiberStateProductExpansionAtSqrt_of_assignmentReduction hAssign)

/-- Closed at-sqrt signed prime-factorization residual. -/
theorem residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :
    Gdbh.PathCResidueFullLocalDensitySigned.ResidueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt :=
  residueDoubleDivisorFullLocalDensitySignedPrimeFactorizationAtSqrt_of_assignmentReduction
    residueSignedUnionFiberStateAssignmentReduction

end PathCResidueFullLocalDensityStateExpansion
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityStateExpansion.residueSignedUnionFiberStateAmbientReduction
#print axioms
  Gdbh.PathCResidueFullLocalDensityStateExpansion.residueUnionStateAssignmentSum_eq_primeFiberProduct
#print axioms
  Gdbh.PathCResidueFullLocalDensityStateExpansion.residueSignedUnionFiberStateAssignmentReduction
#print axioms
  Gdbh.PathCResidueFullLocalDensityStateExpansion.residueDoubleDivisorFullLocalDensitySignedFiberProductEvaluation
