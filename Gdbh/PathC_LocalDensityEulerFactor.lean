/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P26-T2 (Phase 26 / Path C — Local-density Euler factorization).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Path C — P26-T2: Local-density Euler factorization

This file delivers the general Möbius / Euler-product factorization for a
local-density function `ω : ℕ → ℝ`, generalising the constant-`ω(p) = 2`
identity of `Gdbh.PathCPairedMainTermFromLocalDensity` and
`Gdbh.PathCMoebiusInversionRoute` to *any* prime-indexed density.  We
then specialise to the Goldbach paired-sieve density

```
ω_n(p) = 1   if p ∣ n,
ω_n(p) = 2   otherwise,
```

and show that the resulting Euler product reproduces the project's
`goldbachLocalFactor n z`.

## Main results

* `moebiusEulerProduct_multiplicative_omega` — the *general* identity:
  for any `Finset` of primes `P` and any `ω : ℕ → ℝ`,
  ```
  ∑ d ∈ P.powerset, μ(d.prod id) · (∏ p ∈ d, ω p) / d.prod id
    = ∏ p ∈ P, (1 - ω p / p) .
  ```

* `moebiusEulerProduct_goldbach` — the Goldbach specialisation: for
  `n z : ℕ`,
  ```
  ∑ d ∈ P_z.powerset,
      μ(d.prod id) · (∏ p ∈ d, ω_n p) / d.prod id
    = goldbachLocalFactor n z ,
  ```
  where `P_z := (Finset.Icc 3 z).filter Nat.Prime` is the project's
  truncated odd-prime set, and `ω_n p = 1` if `p ∣ n`, else `2`.

* `goldbachLocalFactor_factor_pBF_singular` — the factorisation
  `goldbachLocalFactor n z = pairedBrunFactor z *
                              truncatedGoldbachSingularMultiplier n z`,
  which is `Gdbh.PathCGoldbachLocalFactor.goldbachLocalFactor_eq_paired_mul_singularMultiplier`
  re-exposed under the local-density Euler-factorization heading.

## Strict constraints (P26-T2)

* No `sorry`, no `axiom`, no `admit`.
* Axiom audit: only `Classical.choice`, `Quot.sound`, `propext`.
* File-write rule: only this file is created.
-/

namespace Gdbh
namespace PathCLocalDensityEulerFactor

open scoped BigOperators
open Finset
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCGoldbachLocalFactor
  (goldbachLocalFactor goldbachBadResidueCard
   goldbachLocalFactor_eq_paired_mul_singularMultiplier
   truncatedGoldbachSingularMultiplier)

/-! ## Section 1 — General Möbius / Euler product identity

For any `Finset` of primes `P` and any density function `ω : ℕ → ℝ`,
expanding `∏ p ∈ P, (1 - ω p / p)` by the multinomial / `prod_one_add`
formula yields the Möbius-weighted alternating sum
`∑ d ∈ P.powerset, μ(d.prod id) · (∏ p ∈ d, ω p) / d.prod id`.

This is the *general* local-density Euler factorization; specialising
to the Goldbach paired-sieve density recovers `goldbachLocalFactor`. -/

/-! ### Section 1.1 — Squarefreeness of subset products of distinct primes -/

private lemma squarefree_prod_of_subset_primes
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    Squarefree (d.prod id) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (s := d) (f := id) ?_ ?_
  · intro p hp q hq hpq
    have hpP : Nat.Prime p := hP p (hd hp)
    have hqP : Nat.Prime q := hP q (hd hq)
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
    show IsRelPrime (id p) (id q)
    simpa using (Nat.coprime_iff_isRelPrime.mp hcop)
  · intro p hp
    exact (hP p (hd hp)).squarefree

/-! ### Section 1.2 — `Ω (d.prod id) = d.card` for subsets of distinct primes -/

private lemma cardFactors_prod_of_subset_primes
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    ArithmeticFunction.cardFactors (d.prod id) = d.card := by
  classical
  induction d using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have hsubS : s ⊆ P := fun x hx => hd (Finset.mem_cons_of_mem hx)
    have haP : Nat.Prime a := hP a (hd (Finset.mem_cons_self a s))
    have ha_ne : a ≠ 0 := haP.ne_zero
    have hs_prod_ne : s.prod id ≠ 0 := by
      have h_pos : 0 < s.prod id := by
        refine Finset.prod_pos ?_
        intro p hp
        exact (hP p (hsubS hp)).pos
      exact h_pos.ne'
    have hreduce : (Finset.cons a s has).prod id = a * s.prod id := by
      change ∏ x ∈ Finset.cons a s has, x = _
      rw [Finset.prod_cons]
      rfl
    rw [hreduce, ArithmeticFunction.cardFactors_mul ha_ne hs_prod_ne,
        ArithmeticFunction.cardFactors_apply_prime haP, ih hsubS,
        Finset.card_cons]
    ring

/-! ### Section 1.3 — Möbius value at a product of distinct primes -/

private lemma moebius_prod_of_subset_primes
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {d : Finset ℕ} (hd : d ⊆ P) :
    (μ (d.prod id) : ℝ) = (-1 : ℝ) ^ d.card := by
  classical
  have hsq : Squarefree (d.prod id) := squarefree_prod_of_subset_primes hP hd
  have hΩ : ArithmeticFunction.cardFactors (d.prod id) = d.card :=
    cardFactors_prod_of_subset_primes hP hd
  rw [show (μ (d.prod id) : ℝ) = ((μ (d.prod id) : ℤ) : ℝ) from rfl,
      ArithmeticFunction.moebius_apply_of_squarefree hsq, hΩ]
  push_cast
  ring

/-! ### Section 1.4 — Cast of `d.prod id` to ℝ as `∏ p ∈ d, (p : ℝ)` -/

private lemma cast_prod_eq_prod_cast (d : Finset ℕ) :
    ((d.prod id : ℕ) : ℝ) = ∏ p ∈ d, ((p : ℝ)) := by
  classical
  have hprod_eq : (d.prod id : ℕ) = ∏ p ∈ d, (id p : ℕ) := rfl
  rw [hprod_eq, Nat.cast_prod]
  simp

/-! ### Section 1.5 — Signed-form general Euler product identity

For any `Finset` of primes `P` (each `p ≥ 1` so the cast `(p : ℝ) ≠ 0`
when needed) and any function `ω : ℕ → ℝ`, the binomial expansion of
`∏(1 - ω(p)/p)` is

```
∑ d ⊆ P, (-1)^|d| · (∏ p ∈ d, ω p) / d.prod id .
```
-/
theorem signedEulerProduct_general
    (P : Finset ℕ) (ω : ℕ → ℝ) :
    (∏ p ∈ P, ((1 : ℝ) - ω p / (p : ℝ)))
      = ∑ d ∈ P.powerset,
          ((-1 : ℝ) ^ d.card * (∏ p ∈ d, ω p) / ((d.prod id : ℕ) : ℝ)) := by
  classical
  -- Step 1: rewrite each factor as `1 + (-(ω p / p))`.
  have h1 :
      (∏ p ∈ P, ((1 : ℝ) - ω p / (p : ℝ)))
        = ∏ p ∈ P, ((1 : ℝ) + (-(ω p / (p : ℝ)))) := by
    refine Finset.prod_congr rfl (fun p _ => by ring)
  -- Step 2: apply `Finset.prod_one_add`.
  have h2 :
      (∏ p ∈ P, ((1 : ℝ) + (-(ω p / (p : ℝ)))))
        = ∑ d ∈ P.powerset, ∏ p ∈ d, (-(ω p / (p : ℝ))) := by
    have := Finset.prod_one_add (f := fun p : ℕ => -(ω p / (p : ℝ))) (s := P)
    exact this
  rw [h1, h2]
  -- Step 3: distribute the negation across each subset product.
  refine Finset.sum_congr rfl ?_
  intro d _hd
  have hneg :
      (∏ p ∈ d, (-(ω p / (p : ℝ))))
        = (-1 : ℝ) ^ d.card * ∏ p ∈ d, (ω p / (p : ℝ)) := by
    have := Finset.prod_neg (s := d) (f := fun p : ℕ => ω p / (p : ℝ))
    simpa using this
  -- Express `∏ p ∈ d, ω(p)/p = (∏ p ∈ d, ω p) / (d.prod id : ℝ)`.
  have hsplit :
      (∏ p ∈ d, (ω p / (p : ℝ)))
        = (∏ p ∈ d, ω p) / (∏ p ∈ d, ((p : ℝ))) :=
    Finset.prod_div_distrib (s := d) (f := fun p => ω p) (g := fun p => ((p : ℝ)))
  have hcast := cast_prod_eq_prod_cast d
  rw [hneg, hsplit, ← hcast]
  ring

/-! ### Section 1.6 — Möbius-form general Euler product identity

Replacing the explicit sign `(-1)^|d|` by `μ(d.prod id)` (under the
distinct-primes hypothesis on `P`) gives the canonical Möbius-form
identity:

```
∏ p ∈ P, (1 - ω(p)/p)
  = ∑ d ∈ P.powerset, μ(d.prod id) · (∏ p ∈ d, ω p) / d.prod id .
```
-/
theorem moebiusEulerProduct_multiplicative_omega
    (P : Finset ℕ) (ω : ℕ → ℝ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∏ p ∈ P, ((1 : ℝ) - ω p / (p : ℝ)))
      = ∑ d ∈ P.powerset,
          ((μ (d.prod id) : ℝ) * (∏ p ∈ d, ω p) / ((d.prod id : ℕ) : ℝ)) := by
  classical
  rw [signedEulerProduct_general P ω]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hsub : d ⊆ P := Finset.mem_powerset.mp hd
  have hμ : (μ (d.prod id) : ℝ) = (-1 : ℝ) ^ d.card :=
    moebius_prod_of_subset_primes hP hsub
  rw [hμ]

/-! ## Section 2 — Goldbach paired-sieve specialisation

For the Goldbach paired sieve at target `n`, the local density is

```
ω_n(p) = 1   if p ∣ n,
ω_n(p) = 2   otherwise.
```

This recovers the project's `goldbachLocalFactor n z` after specialising
`P` to `(Finset.Icc 3 z).filter Nat.Prime`.
-/

/-- The Goldbach paired-sieve local-density function as a function
`ℕ → ℝ`, agreeing with `goldbachBadResidueCard n p` cast to `ℝ`. -/
noncomputable def goldbachDensity (n : ℕ) : ℕ → ℝ :=
  fun p => if p ∣ n then 1 else 2

@[simp] lemma goldbachDensity_of_dvd {n p : ℕ} (h : p ∣ n) :
    goldbachDensity n p = 1 := by
  simp [goldbachDensity, h]

@[simp] lemma goldbachDensity_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) :
    goldbachDensity n p = 2 := by
  simp [goldbachDensity, h]

/-- `goldbachDensity` coincides with `goldbachBadResidueCard` cast to ℝ. -/
lemma goldbachDensity_eq_cast (n p : ℕ) :
    goldbachDensity n p = (goldbachBadResidueCard n p : ℝ) := by
  by_cases hpn : p ∣ n
  · simp [goldbachDensity, goldbachBadResidueCard, hpn]
  · simp [goldbachDensity, goldbachBadResidueCard, hpn]

/-- The Goldbach truncated prime set at sieve level `z`: odd primes in
the interval `[3, z]`. -/
def goldbachPrimeSet (z : ℕ) : Finset ℕ :=
  (Finset.Icc 3 z).filter Nat.Prime

lemma goldbachPrimeSet_subset_primes {z : ℕ} :
    ∀ p ∈ goldbachPrimeSet z, Nat.Prime p := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- The `goldbachLocalFactor n z` written as a product over
`goldbachPrimeSet z` using `goldbachDensity n p`. -/
lemma goldbachLocalFactor_eq_prod_density (n z : ℕ) :
    goldbachLocalFactor n z
      = ∏ p ∈ goldbachPrimeSet z, ((1 : ℝ) - goldbachDensity n p / (p : ℝ)) := by
  classical
  unfold goldbachLocalFactor goldbachPrimeSet
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [goldbachDensity_eq_cast]

/-! ### Möbius / Euler product identity for the Goldbach paired sieve

Combining the general identity (Section 1) with the rewriting of
`goldbachLocalFactor n z` as `∏ p ∈ goldbachPrimeSet z, (1 - ω_n p / p)`
gives the Möbius-form identity. -/

/-- **Möbius-form Euler product identity for the Goldbach paired sieve.**

For any `n z : ℕ`,

```
goldbachLocalFactor n z
  = ∑ d ∈ (goldbachPrimeSet z).powerset,
      μ(d.prod id) · (∏ p ∈ d, goldbachDensity n p) / d.prod id .
```
-/
theorem moebiusEulerProduct_goldbach (n z : ℕ) :
    goldbachLocalFactor n z
      = ∑ d ∈ (goldbachPrimeSet z).powerset,
          ((μ (d.prod id) : ℝ)
              * (∏ p ∈ d, goldbachDensity n p)
            / ((d.prod id : ℕ) : ℝ)) := by
  classical
  rw [goldbachLocalFactor_eq_prod_density n z]
  exact moebiusEulerProduct_multiplicative_omega
    (goldbachPrimeSet z) (goldbachDensity n) goldbachPrimeSet_subset_primes

/-- **Signed-form Euler product identity for the Goldbach paired sieve.**

For any `n z : ℕ`,

```
goldbachLocalFactor n z
  = ∑ d ∈ (goldbachPrimeSet z).powerset,
      (-1)^|d| · (∏ p ∈ d, goldbachDensity n p) / d.prod id .
```

Equivalent to `moebiusEulerProduct_goldbach` after substituting
`μ(d.prod id) = (-1)^|d|` for distinct primes. -/
theorem signedEulerProduct_goldbach (n z : ℕ) :
    goldbachLocalFactor n z
      = ∑ d ∈ (goldbachPrimeSet z).powerset,
          ((-1 : ℝ) ^ d.card
              * (∏ p ∈ d, goldbachDensity n p)
            / ((d.prod id : ℕ) : ℝ)) := by
  classical
  rw [goldbachLocalFactor_eq_prod_density n z]
  exact signedEulerProduct_general (goldbachPrimeSet z) (goldbachDensity n)

/-! ## Section 3 — Factorisation `goldbachLocalFactor = pBF · sing`

We re-expose the existing project factorisation
(`goldbachLocalFactor_eq_paired_mul_singularMultiplier`) under the
local-density Euler-factorisation heading.  This is the *external*
factorisation `pBF(z) · truncatedSingularMultiplier(n,z)` corresponding
to splitting the prime range into `p ∤ n` (uniform `2/p`) and `p ∣ n`
(reduced `1/p`) — exactly the decomposition motivating the Goldbach
density `ω_n`. -/

/-- **External Euler factorisation**.

```
goldbachLocalFactor n z = pairedBrunFactor z * truncatedGoldbachSingularMultiplier n z .
```

This is the prime-range decomposition `∏_{p ≤ z}` =
`∏_{p ≤ z, p ∤ n} · ∏_{p ≤ z, p ∣ n}` applied to the Euler product
`∏(1 - ω_n p / p)`. -/
theorem goldbachLocalFactor_factor_pBF_singular (n z : ℕ) :
    goldbachLocalFactor n z
      = pairedBrunFactor z * truncatedGoldbachSingularMultiplier n z :=
  goldbachLocalFactor_eq_paired_mul_singularMultiplier n z

/-! ## Section 4 — P26-T2 deliverable summary

* `signedEulerProduct_general` and `moebiusEulerProduct_multiplicative_omega`
  give the *general* signed and Möbius forms of the local-density Euler
  identity, parameterised by an arbitrary density `ω : ℕ → ℝ`.

* `signedEulerProduct_goldbach` and `moebiusEulerProduct_goldbach`
  specialise to the Goldbach density `ω_n(p) = 1` if `p ∣ n`, else `2`,
  identifying the Möbius-weighted alternating sum with the project's
  `goldbachLocalFactor n z`.

* `goldbachLocalFactor_factor_pBF_singular` re-exposes the external
  factorisation `goldbachLocalFactor = pairedBrunFactor · truncatedGoldbachSingularMultiplier`
  as the prime-range decomposition `p ∤ n` ⊔ `p ∣ n` of the underlying
  Euler product.

**Axiom budget**: only `Classical.choice`, `Quot.sound`, `propext`.
No `sorry`, no `axiom`, no `admit`. -/
theorem pathC_p26_t2_summary : True := trivial

end PathCLocalDensityEulerFactor
end Gdbh
