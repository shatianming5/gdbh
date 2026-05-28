/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueBonferroniKernelDecomposition
import Mathlib.Tactic.Ring

/-!
# Path C -- residue prime-set product support

Round 76 exposes the finite arithmetic facts about products of subsets of
`residuePrimeSet z` that were previously private inside the quotient-main
closure.  These lemmas normalize gcd/lcm and coprimality conditions into
intersection/union language for later residue-remainder decompositions.

The file is algebraic only.  It does not assert a new analytic estimate.
-/

namespace Gdbh
namespace PathCResiduePrimeSetProductSupport

open scoped BigOperators
open Finset

open Gdbh.PathCResidueBonferroniKernelDecomposition
  (residuePrimeSet residuePrimeSet_prime)

/-- Any subset of `residuePrimeSet z` consists of primes. -/
theorem residuePrimeSubset_prime {z : ℕ} {s : Finset ℕ}
    (hs : s ⊆ residuePrimeSet z) :
    ∀ p ∈ s, Nat.Prime p :=
  fun _ hp => residuePrimeSet_prime (hs hp)

/-- The product of a residue-prime subset is nonzero. -/
theorem residuePrimeSubset_prod_ne_zero {z : ℕ} {s : Finset ℕ}
    (hs : s ⊆ residuePrimeSet z) :
    s.prod id ≠ 0 := by
  have hprime := residuePrimeSubset_prime hs
  have hpos : 0 < s.prod id := by
    refine Finset.prod_pos ?_
    intro p hp
    exact (hprime p hp).pos
  exact hpos.ne'

/-- The product of a residue-prime subset is squarefree. -/
theorem residuePrimeSubset_squarefree_prod {z : ℕ} {s : Finset ℕ}
    (hs : s ⊆ residuePrimeSet z) :
    Squarefree (s.prod id) := by
  classical
  have hprime := residuePrimeSubset_prime hs
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (s := s) (f := id) ?_ ?_
  · intro p hp q hq hpq
    have hpP : Nat.Prime p := hprime p hp
    have hqP : Nat.Prime q := hprime q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
    show IsRelPrime (id p) (id q)
    simpa using (Nat.coprime_iff_isRelPrime.mp hcop)
  · intro p hp
    exact (hprime p hp).squarefree

/-- A product of residue primes divides `n` iff every prime in the subset
divides `n`. -/
theorem residuePrimeSubset_prod_dvd_iff_forall_prime_dvd
    {z : ℕ} {s : Finset ℕ} (hs : s ⊆ residuePrimeSet z) (n : ℕ) :
    s.prod id ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  classical
  have hprime := residuePrimeSubset_prime hs
  refine ⟨?_, ?_⟩
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction s using Finset.cons_induction with
    | empty =>
        simp
    | cons a s has ih =>
        have haP : Nat.Prime a := hprime a (Finset.mem_cons_self a s)
        have hs_sub : s ⊆ residuePrimeSet z := by
          intro p hp
          exact hs (Finset.mem_cons_of_mem hp)
        have hsP : ∀ p ∈ s, Nat.Prime p :=
          residuePrimeSubset_prime hs_sub
        have ha_dvd : a ∣ n := h a (Finset.mem_cons_self a s)
        have hs_dvd : s.prod id ∣ n := by
          apply ih hs_sub hsP
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

/-- The gcd of two products of residue-prime subsets is the product over
their intersection. -/
theorem residuePrimeSubset_gcd_prod_eq_prod_inter
    {z : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z) :
    Nat.gcd (d1.prod id) (d2.prod id) = (d1 ∩ d2).prod id := by
  classical
  have h1 : ∀ p ∈ d1, Nat.Prime p := residuePrimeSubset_prime hd1
  have h2 : ∀ p ∈ d2, Nat.Prime p := residuePrimeSubset_prime hd2
  have h1nz : d1.prod id ≠ 0 := residuePrimeSubset_prod_ne_zero hd1
  have h2nz : d2.prod id ≠ 0 := residuePrimeSubset_prod_ne_zero hd2
  have hg_sq :
      Squarefree (Nat.gcd (d1.prod id) (d2.prod id)) :=
    (residuePrimeSubset_squarefree_prod hd1).squarefree_of_dvd
      (Nat.gcd_dvd_left _ _)
  have hpf :
      (Nat.gcd (d1.prod id) (d2.prod id)).primeFactors = d1 ∩ d2 := by
    rw [Nat.primeFactors_gcd h1nz h2nz]
    change (∏ p ∈ d1, p).primeFactors ∩
        (∏ p ∈ d2, p).primeFactors = d1 ∩ d2
    rw [Nat.primeFactors_prod h1, Nat.primeFactors_prod h2]
  calc
    Nat.gcd (d1.prod id) (d2.prod id)
        = ∏ p ∈ (Nat.gcd (d1.prod id) (d2.prod id)).primeFactors, p := by
          exact (Nat.prod_primeFactors_of_squarefree hg_sq).symm
    _ = ∏ p ∈ d1 ∩ d2, p := by
          rw [hpf]
    _ = (d1 ∩ d2).prod id := rfl

/-- The lcm of two products of residue-prime subsets is the product over
their union. -/
theorem residuePrimeSubset_lcm_prod_eq_prod_union
    {z : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z) :
    Nat.lcm (d1.prod id) (d2.prod id) = (d1 ∪ d2).prod id := by
  classical
  have hgcd := residuePrimeSubset_gcd_prod_eq_prod_inter hd1 hd2
  have hinter_sub : d1 ∩ d2 ⊆ residuePrimeSet z := by
    intro p hp
    exact hd1 (Finset.mem_inter.mp hp).1
  have hinter_pos : 0 < (d1 ∩ d2).prod id := by
    refine Finset.prod_pos ?_
    intro p hp
    exact (residuePrimeSubset_prime hinter_sub p hp).pos
  apply Nat.mul_right_cancel hinter_pos
  calc
    Nat.lcm (d1.prod id) (d2.prod id) * (d1 ∩ d2).prod id
        = Nat.gcd (d1.prod id) (d2.prod id) *
            Nat.lcm (d1.prod id) (d2.prod id) := by
          rw [hgcd]
          ring
    _ = (d1.prod id) * (d2.prod id) := by
          exact Nat.gcd_mul_lcm (d1.prod id) (d2.prod id)
    _ = (d1 ∪ d2).prod id * (d1 ∩ d2).prod id := by
          exact (Finset.prod_union_inter (s₁ := d1) (s₂ := d2) (f := id)).symm

/-- The gcd-product compatibility condition is equivalently divisibility by
the product over the intersection. -/
theorem residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd
    {z : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z)
    (n : ℕ) :
    Nat.gcd (d1.prod id) (d2.prod id) ∣ n ↔ (d1 ∩ d2).prod id ∣ n := by
  rw [residuePrimeSubset_gcd_prod_eq_prod_inter hd1 hd2]

/-- A residue-prime subset has product one iff it is empty. -/
theorem residuePrimeSubset_prod_eq_one_iff_eq_empty
    {z : ℕ} {s : Finset ℕ} (hs : s ⊆ residuePrimeSet z) :
    s.prod id = 1 ↔ s = ∅ := by
  constructor
  · intro hprod
    rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · rfl
    · have hpP : Nat.Prime p := residuePrimeSubset_prime hs p hp
      have hpdvd : p ∣ s.prod id := Finset.dvd_prod_of_mem id hp
      have hpdvd_one : p ∣ 1 := by
        rw [← hprod]
        exact hpdvd
      have hpone : p = 1 := Nat.dvd_one.mp hpdvd_one
      exact False.elim (hpP.ne_one hpone)
  · intro h
    simp [h]

/-- Coprime products of residue-prime subsets have intersection product one. -/
theorem residuePrimeSubset_prod_inter_eq_one_of_coprime
    {z : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z)
    (hcop : Nat.Coprime (d1.prod id) (d2.prod id)) :
    (d1 ∩ d2).prod id = 1 := by
  have h := Nat.coprime_iff_gcd_eq_one.mp hcop
  rwa [residuePrimeSubset_gcd_prod_eq_prod_inter hd1 hd2] at h

/-- Products of residue-prime subsets are coprime iff the subsets have empty
intersection. -/
theorem residuePrimeSubset_coprime_iff_inter_eq_empty
    {z : ℕ} {d1 d2 : Finset ℕ}
    (hd1 : d1 ⊆ residuePrimeSet z) (hd2 : d2 ⊆ residuePrimeSet z) :
    Nat.Coprime (d1.prod id) (d2.prod id) ↔ d1 ∩ d2 = ∅ := by
  have hinter_sub : d1 ∩ d2 ⊆ residuePrimeSet z := by
    intro p hp
    exact hd1 (Finset.mem_inter.mp hp).1
  rw [Nat.coprime_iff_gcd_eq_one,
    residuePrimeSubset_gcd_prod_eq_prod_inter hd1 hd2,
    residuePrimeSubset_prod_eq_one_iff_eq_empty hinter_sub]

end PathCResiduePrimeSetProductSupport
end Gdbh

#print axioms
  Gdbh.PathCResiduePrimeSetProductSupport.residuePrimeSubset_gcd_prod_eq_prod_inter
#print axioms
  Gdbh.PathCResiduePrimeSetProductSupport.residuePrimeSubset_lcm_prod_eq_prod_union
#print axioms
  Gdbh.PathCResiduePrimeSetProductSupport.residuePrimeSubset_gcd_prod_dvd_iff_inter_prod_dvd
#print axioms
  Gdbh.PathCResiduePrimeSetProductSupport.residuePrimeSubset_coprime_iff_inter_eq_empty
