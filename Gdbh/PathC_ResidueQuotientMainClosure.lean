/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCountToDensityClosure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- quotient main term closure

This file attacks the quotient-main residual left by Round 21.  The key
finite arithmetic fact is that, for two squarefree products of distinct
residue primes, the CRT quotient denominator is the product over the union
and its compatibility condition is exactly the divisibility condition on the
intersection.
-/

namespace Gdbh
namespace PathCResidueQuotientMainClosure

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition
  (residuePrimeSet residuePrimeSet_prime)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySum residueDoubleDivisorLocalDensitySumAtSqrt
   residuePairCompatibilityWeight)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorQuotientMainAtSqrtBound
   ResidueDoubleDivisorRemainderAtSqrtBound residueDoubleDivisorQuotientMainSum
   residueDoubleDivisorQuotientMainSumAtSqrt residuePairQuotientMainTerm)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private lemma prod_ne_zero_of_primes {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) :
    s.prod id ≠ 0 := by
  have hpos : 0 < s.prod id := by
    refine Finset.prod_pos ?_
    intro p hp
    exact (hs p hp).pos
  exact hpos.ne'

private lemma squarefree_prod_of_primes {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (s.prod id) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (s := s) (f := id) ?_ ?_
  · intro p hp q hq hpq
    have hpP : Nat.Prime p := hs p hp
    have hqP : Nat.Prime q := hs q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
    show IsRelPrime (id p) (id q)
    simpa using (Nat.coprime_iff_isRelPrime.mp hcop)
  · intro p hp
    exact (hs p hp).squarefree

private lemma prod_dvd_iff_forall_prime_dvd {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (n : ℕ) :
    s.prod id ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  classical
  refine ⟨?_, ?_⟩
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction s using Finset.cons_induction with
    | empty =>
        simp
    | cons a s has ih =>
        have haP : Nat.Prime a := hs a (Finset.mem_cons_self a s)
        have hsP : ∀ p ∈ s, Nat.Prime p :=
          fun p hp => hs p (Finset.mem_cons_of_mem hp)
        have ha_dvd : a ∣ n := h a (Finset.mem_cons_self a s)
        have hs_dvd : s.prod id ∣ n := by
          apply ih hsP
          intro p hp
          exact h p (Finset.mem_cons_of_mem hp)
        have hnotdvd : ¬ a ∣ s.prod id := by
          intro hadvd
          rcases (haP.prime.dvd_finset_prod_iff id).mp hadvd with
            ⟨q, hq, haq⟩
          have hqP : Nat.Prime q := hsP q hq
          have hqa : q = a := (hqP.dvd_iff_eq haP.ne_one).mp haq
          exact has (hqa ▸ hq)
        have hcop : Nat.Coprime a (s.prod id) :=
          haP.coprime_iff_not_dvd.mpr hnotdvd
        rw [Finset.prod_cons]
        exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

private lemma gcd_prod_eq_prod_inter_of_primes {d₁ d₂ : Finset ℕ}
    (h₁ : ∀ p ∈ d₁, Nat.Prime p) (h₂ : ∀ p ∈ d₂, Nat.Prime p) :
    Nat.gcd (d₁.prod id) (d₂.prod id) = (d₁ ∩ d₂).prod id := by
  classical
  have h₁nz : d₁.prod id ≠ 0 := prod_ne_zero_of_primes h₁
  have h₂nz : d₂.prod id ≠ 0 := prod_ne_zero_of_primes h₂
  have hg_sq :
      Squarefree (Nat.gcd (d₁.prod id) (d₂.prod id)) :=
    (squarefree_prod_of_primes h₁).squarefree_of_dvd
      (Nat.gcd_dvd_left _ _)
  have hpf :
      (Nat.gcd (d₁.prod id) (d₂.prod id)).primeFactors = d₁ ∩ d₂ := by
    rw [Nat.primeFactors_gcd h₁nz h₂nz]
    change (∏ p ∈ d₁, p).primeFactors ∩
        (∏ p ∈ d₂, p).primeFactors = d₁ ∩ d₂
    rw [Nat.primeFactors_prod h₁, Nat.primeFactors_prod h₂]
  calc
    Nat.gcd (d₁.prod id) (d₂.prod id)
        = ∏ p ∈ (Nat.gcd (d₁.prod id) (d₂.prod id)).primeFactors, p := by
          exact (Nat.prod_primeFactors_of_squarefree hg_sq).symm
    _ = ∏ p ∈ d₁ ∩ d₂, p := by
          rw [hpf]
    _ = (d₁ ∩ d₂).prod id := rfl

private lemma lcm_prod_eq_prod_union_of_primes {d₁ d₂ : Finset ℕ}
    (h₁ : ∀ p ∈ d₁, Nat.Prime p) (h₂ : ∀ p ∈ d₂, Nat.Prime p) :
    Nat.lcm (d₁.prod id) (d₂.prod id) = (d₁ ∪ d₂).prod id := by
  classical
  have hgcd := gcd_prod_eq_prod_inter_of_primes h₁ h₂
  have hinter_pos : 0 < (d₁ ∩ d₂).prod id := by
    refine Finset.prod_pos ?_
    intro p hp
    exact (h₁ p (Finset.mem_inter.mp hp).1).pos
  apply Nat.mul_right_cancel hinter_pos
  calc
    Nat.lcm (d₁.prod id) (d₂.prod id) * (d₁ ∩ d₂).prod id
        = Nat.gcd (d₁.prod id) (d₂.prod id) *
            Nat.lcm (d₁.prod id) (d₂.prod id) := by
          rw [hgcd]
          ring
    _ = (d₁.prod id) * (d₂.prod id) := by
          exact Nat.gcd_mul_lcm (d₁.prod id) (d₂.prod id)
    _ = (d₁ ∪ d₂).prod id * (d₁ ∩ d₂).prod id := by
          exact (Finset.prod_union_inter (s₁ := d₁) (s₂ := d₂) (f := id)).symm

/-! ## Named smaller residuals -/

/-- Pair-level quotient-main reduction.  This is the arithmetic core of the
quotient-main residual. -/
def ResiduePairQuotientMainLocalDensityReduction : Prop :=
  ∀ n : ℕ, ∀ d₁ d₂ : Finset ℕ,
    (∀ p ∈ d₁ ∪ d₂, Nat.Prime p) →
      residuePairQuotientMainTerm n (d₁.prod id) (d₂.prod id)
        = (n : ℝ) * residuePairCompatibilityWeight n d₁ d₂

/-- Sum-level quotient-main reduction, before specializing to `z = sqrt n`
and the canonical depth. -/
def ResidueDoubleDivisorQuotientMainLocalDensityReduction : Prop :=
  ∀ n z k : ℕ,
    residueDoubleDivisorQuotientMainSum n z k
      = (n : ℝ) * residueDoubleDivisorLocalDensitySum n z k

theorem residuePairQuotientMainLocalDensityReduction :
    ResiduePairQuotientMainLocalDensityReduction := by
  classical
  intro n d₁ d₂ hprime
  have h₁ : ∀ p ∈ d₁, Nat.Prime p :=
    fun p hp => hprime p (Finset.mem_union.mpr (Or.inl hp))
  have h₂ : ∀ p ∈ d₂, Nat.Prime p :=
    fun p hp => hprime p (Finset.mem_union.mpr (Or.inr hp))
  have hI : ∀ p ∈ d₁ ∩ d₂, Nat.Prime p :=
    fun p hp => h₁ p (Finset.mem_inter.mp hp).1
  have hgcd := gcd_prod_eq_prod_inter_of_primes h₁ h₂
  have hlcm := lcm_prod_eq_prod_union_of_primes h₁ h₂
  have hcompat_iff :
      (d₁ ∩ d₂).prod id ∣ n ↔ ∀ p ∈ d₁ ∩ d₂, p ∣ n :=
    prod_dvd_iff_forall_prime_dvd hI n
  unfold residuePairQuotientMainTerm residuePairCompatibilityWeight
  rw [hgcd, hlcm]
  by_cases hcompat : ∀ p ∈ d₁ ∩ d₂, p ∣ n
  · rw [if_pos (hcompat_iff.mpr hcompat), if_pos hcompat]
    ring
  · rw [if_neg (fun h => hcompat (hcompat_iff.mp h)), if_neg hcompat]
    ring

theorem residueDoubleDivisorQuotientMainLocalDensityReduction :
    ResidueDoubleDivisorQuotientMainLocalDensityReduction := by
  classical
  intro n z k
  unfold residueDoubleDivisorQuotientMainSum
    residueDoubleDivisorLocalDensitySum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d₁ hd₁
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d₂ hd₂
  have hd₁P :
      d₁ ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd₁).1
  have hd₂P :
      d₂ ⊆ residuePrimeSet z :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd₂).1
  have hprime : ∀ p ∈ d₁ ∪ d₂, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp₁ | hp₂
    · exact residuePrimeSet_prime (hd₁P hp₁)
    · exact residuePrimeSet_prime (hd₂P hp₂)
  have hpair :=
    residuePairQuotientMainLocalDensityReduction n d₁ d₂ hprime
  rw [hpair]
  ring

theorem residueDoubleDivisorQuotientMainAtSqrtBound :
    ResidueDoubleDivisorQuotientMainAtSqrtBound := by
  intro n hn
  unfold residueDoubleDivisorQuotientMainSumAtSqrt
  rw [residueDoubleDivisorQuotientMainLocalDensityReduction]
  change (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n ≤
    (n : ℝ) * Gdbh.PathCGoldbachResidues.goldbachResidueMainFactor n (Nat.sqrt n)
  rw [
    _root_.Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt n hn]

/-! ## Bridges with the quotient-main residual closed -/

theorem residueDoubleDivisorExactCountToLocalDensityAtSqrtBound_of_remainder
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    _root_.Gdbh.PathCResidueDoubleDivisorDensityDecomposition.ResidueDoubleDivisorExactCountToLocalDensityAtSqrtBound :=
  _root_.Gdbh.PathCResidueCountToDensityClosure.residueDoubleDivisorExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
    residueDoubleDivisorQuotientMainAtSqrtBound hRem

theorem residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_remainder
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    _root_.Gdbh.PathCResidueCoprimeSplitDensityBridge.ResidueCoprimeSplitExactCountToLocalDensityAtSqrtBound :=
  _root_.Gdbh.PathCResidueCountToDensityClosure.residueCoprimeSplitExactCountToLocalDensityAtSqrtBound_of_quotientMain_and_remainder
    residueDoubleDivisorQuotientMainAtSqrtBound hRem

theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_remainder
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  _root_.Gdbh.PathCResidueCountToDensityClosure.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_quotientMain_and_remainder
    residueDoubleDivisorQuotientMainAtSqrtBound hRem

theorem pathC_kGoldbach_of_residueRemainder_and_countingInput
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  _root_.Gdbh.PathCResidueCountToDensityClosure.pathC_kGoldbach_of_residueQuotientRemainder_and_countingInput
    residueDoubleDivisorQuotientMainAtSqrtBound hRem hCounting

end PathCResidueQuotientMainClosure
end Gdbh

#print axioms
  Gdbh.PathCResidueQuotientMainClosure.residuePairQuotientMainLocalDensityReduction
#print axioms
  Gdbh.PathCResidueQuotientMainClosure.residueDoubleDivisorQuotientMainLocalDensityReduction
#print axioms
  Gdbh.PathCResidueQuotientMainClosure.residueDoubleDivisorQuotientMainAtSqrtBound
#print axioms
  Gdbh.PathCResidueQuotientMainClosure.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_remainder
