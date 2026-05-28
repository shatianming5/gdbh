import Gdbh.PathC_MertensProof
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Path C — P17-T4: Paired main term from local density

Phase 17 decomposes `BrunGoldbachPairedMainTermRefined`.  This file
covers the algebraic identification (Sub-Prop S4) of the truncated
paired-sieve main term as the Euler product `pairedBrunFactor`.

## What is closed

* `paired_eulerProduct_identity_signed`: the exact untruncated identity

  ```
  ∑ d ∈ P.powerset, (-1)^d.card * 2^d.card / (d.prod id)
    = ∏ p ∈ P, (1 - 2/p)
  ```

  for any `Finset ℕ` `P` of primes (all `p ≥ 3` so that the cast `(p : ℝ) ≠ 0`
  but the algebraic identity itself just needs `p ≠ 0`).  No truncation, no
  filter required because *every* subset of a finset of distinct primes
  produces a squarefree product.

* `paired_eulerProduct_identity`: the same identity in the Möbius-function
  form requested by the P17-T4 deliverable, namely

  ```
  ∑ d ∈ P.powerset.filter (Squarefree ∘ (·.prod id)),
      (μ (d.prod id) : ℝ) * 2^d.card / (d.prod id)
    = ∏ p ∈ P, (1 - 2/p) .
  ```

  Note the filter is **redundant** here (we prove the squarefreeness on the
  whole powerset), but it is included to match the requested signature.

* `paired_eulerProduct_identity_pairedBrunFactor`: specialisation of the
  identity to the project's `pairedBrunFactor z`, taking `P` to be the
  prime-filtered `Finset.Icc 3 z`.

## What remains residual

The genuine Bonferroni-truncated inequality (restricting the sum to
`d.card ≤ k` and getting an inequality with the next-term tail) is
isolated as the named open Prop `PairedMainTermFromLocalDensity`.  The
honest residual content is a single classical Bonferroni inequality (a
consequence of inclusion–exclusion) and is documented below.

## Honesty note

The untruncated identity is *exactly* the Euler-product identity for the
paired-sieve weights `μ(d)·2^ω(d)/d` over divisors built from `P`.  It
proves *cleanly* from `Finset.prod_one_add` once we recognise that the
sum is the binomial expansion of `∏(1 + (-2/p))`.  No sign error and no
asymptotic content is hidden here — this is genuinely algebraic.

## Mathlib references

* `Finset.prod_one_add` (binomial expansion of `∏(1 + f i)`).
* `Finset.prod_neg` (`∏ (-f) = (-1)^|s| * ∏ f`).
* `ArithmeticFunction.moebius_apply_of_squarefree`.
* `ArithmeticFunction.cardFactors_mul`, `cardFactors_apply_prime`.
-/

namespace Gdbh
namespace PathCPairedMainTermFromLocalDensity

open scoped BigOperators
open Finset
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos
  one_sub_two_div_prime_pos)

/-! ## Section 1 — Untruncated signed identity

For any `Finset ℕ` `P` consisting of primes `p ≥ 3`, the alternating
sum of `2^|d|/d.prod` over subsets `d ⊆ P` equals the Euler product
`∏_{p ∈ P} (1 - 2/p)`.
-/

/-- Untruncated, *signed* paired Euler product identity:

  `∑ d ⊆ P, (-1)^|d| · 2^|d| / ∏ d = ∏ p ∈ P, (1 - 2/p)`.

Proof: expand `1 - 2/p = 1 + (-(2/p))`, apply `Finset.prod_one_add`,
distribute `∏ d, (-(2/p)) = (-1)^|d| · 2^|d| / d.prod`. -/
theorem paired_eulerProduct_identity_signed
    (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ d ∈ P.powerset,
        ((-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
      = ∏ p ∈ P, (1 - 2/(p : ℝ)) := by
  classical
  -- 1. Rewrite each factor `1 - 2/p` as `1 + (-(2/p))`.
  have h1 :
      (∏ p ∈ P, (1 - 2/(p : ℝ)))
        = ∏ p ∈ P, (1 + (-(2/(p : ℝ)))) := by
    refine Finset.prod_congr rfl ?_
    intro p _hp
    ring
  -- 2. Expand by binomial (`prod_one_add`).
  have h2 :
      (∏ p ∈ P, (1 + (-(2/(p : ℝ)))))
        = ∑ d ∈ P.powerset, ∏ p ∈ d, (-(2/(p : ℝ))) := by
    have := Finset.prod_one_add (f := fun p : ℕ => -(2/(p : ℝ))) (s := P)
    exact this
  -- 3. Distribute each subset product.
  have h3 :
      ∀ d ∈ P.powerset,
        (∏ p ∈ d, (-(2/(p : ℝ))))
          = (-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ) := by
    intro d hd
    have hdP : d ⊆ P := Finset.mem_powerset.mp hd
    -- Pull out the sign factor.
    have hneg :
        (∏ p ∈ d, (-(2/(p : ℝ))))
          = (-1 : ℝ)^d.card * ∏ p ∈ d, (2/(p : ℝ)) := by
      have := Finset.prod_neg (s := d) (f := fun p => (2/(p : ℝ)))
      simpa using this
    -- Express the positive product `∏ (2/p)` as `2^|d| / d.prod`.
    have hpos :
        (∏ p ∈ d, (2/(p : ℝ)))
          = (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ) := by
      have hsplit :
          (∏ p ∈ d, ((2 : ℝ) / (p : ℝ)))
            = (∏ _p ∈ d, (2 : ℝ)) / (∏ p ∈ d, ((p : ℝ))) :=
        Finset.prod_div_distrib (s := d)
          (f := fun _ => (2 : ℝ)) (g := fun p => ((p : ℝ)))
      have hconst : (∏ _p ∈ d, (2 : ℝ)) = (2 : ℝ)^d.card :=
        Finset.prod_const (s := d) (b := (2 : ℝ))
      have hcastProd :
          (∏ p ∈ d, ((p : ℝ))) = ((d.prod id : ℕ) : ℝ) := by
        -- `d.prod id = ∏ p ∈ d, id p`; cast to ℝ via `Finset.prod_natCast`.
        have hprod_eq : (d.prod id : ℕ) = ∏ p ∈ d, (id p : ℕ) := by
          rfl
        rw [hprod_eq, Nat.cast_prod]
        simp
      rw [hsplit, hconst, hcastProd]
    -- Combine.
    rw [hneg, hpos]
    ring
  -- 4. Assemble.
  rw [h1, h2]
  refine Finset.sum_congr rfl ?_
  intro d hd
  exact (h3 d hd).symm

/-! ## Section 2 — Squarefreeness of every subset product

Every subset `d ⊆ P` of a finset of distinct primes has squarefree
product.  This is the (trivial) reason the squarefree filter is
redundant in our Euler-product identity. -/

private lemma squarefree_prod_of_subset_primes {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {d : Finset ℕ} (hd : d ⊆ P) :
    Squarefree (d.prod id) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (s := d) (f := id) ?_ ?_
  · -- pairwise relPrime: distinct primes are coprime, hence isRelPrime
    intro p hp q hq hpq
    have hpP : Nat.Prime p := hP p (hd hp)
    have hqP : Nat.Prime q := hP q (hd hq)
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
    -- `Function.onFun IsRelPrime id p q = IsRelPrime (id p) (id q) = IsRelPrime p q`.
    show IsRelPrime (id p) (id q)
    simpa using (Nat.coprime_iff_isRelPrime.mp hcop)
  · intro p hp
    have hpP : Nat.Prime p := hP p (hd hp)
    exact hpP.squarefree

/-! ## Section 3 — Cardinality of `Ω (d.prod id)` and the Möbius value

For `d ⊆ P` a subset of distinct primes, `Ω (d.prod id) = d.card` and
hence `μ (d.prod id) = (-1)^d.card`. -/

private lemma cardFactors_prod_of_subset_primes {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {d : Finset ℕ} (hd : d ⊆ P) :
    Ω (d.prod id) = d.card := by
  classical
  -- Induction on `d` using `Finset.cons_induction`.
  induction d using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have hsubS : s ⊆ P := fun x hx => hd (Finset.mem_cons_of_mem hx)
    have haP : Nat.Prime a := hP a (hd (Finset.mem_cons_self a s))
    have ha_ne : a ≠ 0 := haP.ne_zero
    have hs_prod_ne : s.prod id ≠ 0 := by
      have : 0 < s.prod id := by
        refine Finset.prod_pos ?_
        intro p hp
        exact (hP p (hsubS hp)).pos
      exact this.ne'
    -- After `Finset.prod_cons`, the goal becomes `Ω (id a * ∏ x ∈ s, id x) = ...`.
    have hreduce : (Finset.cons a s has).prod id = a * s.prod id := by
      change ∏ x ∈ Finset.cons a s has, x = _
      rw [Finset.prod_cons]
      rfl
    rw [hreduce, ArithmeticFunction.cardFactors_mul ha_ne hs_prod_ne,
        ArithmeticFunction.cardFactors_apply_prime haP, ih hsubS, Finset.card_cons]
    ring

private lemma moebius_prod_of_subset_primes {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {d : Finset ℕ} (hd : d ⊆ P) :
    (μ (d.prod id) : ℝ) = (-1 : ℝ)^d.card := by
  classical
  have hsq : Squarefree (d.prod id) := squarefree_prod_of_subset_primes hP hd
  have hΩ : Ω (d.prod id) = d.card := cardFactors_prod_of_subset_primes hP hd
  rw [show (μ (d.prod id) : ℝ) = ((μ (d.prod id) : ℤ) : ℝ) from rfl,
      ArithmeticFunction.moebius_apply_of_squarefree hsq, hΩ]
  push_cast
  ring

/-! ## Section 4 — Möbius-form paired Euler product identity (with filter)

The signed identity rewritten in the Möbius-function form requested by
P17-T4.  The squarefree filter on `P.powerset` is redundant (every
subset of a prime set is squarefree), but we include it to match the
target signature. -/

/-- The exact Euler product identity for the paired Goldbach sieve weights:

  `∑ d ⊆ P, Squarefree (d.prod) → (μ(d.prod) : ℝ) · 2^|d| / d.prod
     = ∏ p ∈ P, (1 - 2/p)`. -/
theorem paired_eulerProduct_identity
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) :
    ∑ d ∈ P.powerset.filter (fun d => Squarefree (d.prod id)),
        ((μ (d.prod id) : ℝ)
          * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
      = ∏ p ∈ P, (1 - 2/(p : ℝ)) := by
  classical
  have hP_prime : ∀ p ∈ P, Nat.Prime p := fun p hp => (hP p hp).1
  -- All powerset subsets are squarefree-product, so the filter is trivially the whole powerset.
  have hFilterEq :
      P.powerset.filter (fun d => Squarefree (d.prod id))
        = P.powerset := by
    refine Finset.filter_eq_self.mpr ?_
    intro d hd
    exact squarefree_prod_of_subset_primes hP_prime (Finset.mem_powerset.mp hd)
  rw [hFilterEq]
  -- Convert each Möbius factor to (-1)^d.card via `moebius_prod_of_subset_primes`.
  have hCongr :
      ∀ d ∈ P.powerset,
        ((μ (d.prod id) : ℝ)
          * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
          = (-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ) := by
    intro d hd
    have hdP : d ⊆ P := Finset.mem_powerset.mp hd
    have hμ := moebius_prod_of_subset_primes hP_prime hdP
    rw [hμ]
  rw [Finset.sum_congr rfl hCongr]
  exact paired_eulerProduct_identity_signed P hP_prime

/-! ## Section 5 — Specialisation to `pairedBrunFactor`

`pairedBrunFactor z = ∏ p ∈ (Icc 3 z).filter Prime, (1 - 2/p)` is the
project's Euler product.  The Möbius-form identity therefore evaluates
it as an alternating sum of `2^|d|/d.prod` over subsets of the prime
divisors `≤ z` (and `≥ 3`).
-/

/-- The paired Brun factor at sieve level `z` equals the alternating
  signed sum over squarefree divisors built from primes in `[3,z]`. -/
theorem paired_eulerProduct_identity_pairedBrunFactor (z : ℕ) :
    ∑ d ∈ ((Finset.Icc 3 z).filter Nat.Prime).powerset,
        ((-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
      = pairedBrunFactor z := by
  classical
  unfold pairedBrunFactor
  refine paired_eulerProduct_identity_signed
    ((Finset.Icc 3 z).filter Nat.Prime) ?_
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-! ## Section 6 — Named open sub-Prop: Bonferroni-truncated version

The truncation-to-`Ω(d) ≤ k` Bonferroni inequality is the genuine
residual content of P17-T4.  We expose it as a named open Prop whose
classical truth is the standard Bonferroni inequality (a consequence
of inclusion–exclusion).
-/

/-- **Named open sub-Prop (Bonferroni-truncated paired main term).**

Mathematically: for any finset `P` of primes `≥ 3` and any `k : ℕ`,
either

* `k` is even, in which case the truncated sum

  `∑_{d ⊆ P, |d| ≤ k} (-1)^|d| · 2^|d| / d.prod`

  is an upper bound for the full Euler product `∏(1 - 2/p)`,
  with the *excess* (truncated minus full) bounded above by

  `(2^(k+1)) · (number of (k+1)-subsets of P) / (smallest (k+1)-product),`

  i.e. by the next-Bonferroni term in absolute value; or

* `k` is odd, in which case the *reverse* inequality holds with the same
  next-term tail bound.

This is a classical Bonferroni-Brun inequality.  Mathlib v4.29.1 status:
**open** — mathlib has partial Möbius-inversion infrastructure
(`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` etc.) but the
explicit truncated form here requires the standard Bonferroni-by-induction
on `|P|` argument.  Closing this Prop is the genuine S4 residual gap.
-/
def PairedMainTermFromLocalDensity : Prop :=
  ∀ (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) (k : ℕ),
    -- Truncated alternating sum (only subsets of size ≤ k).
    let T : ℝ := ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
        ((-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
    let full : ℝ := ∏ p ∈ P, (1 - 2/(p : ℝ))
    -- Bonferroni tail (sum of absolute values of (k+1)-terms over
    -- subsets of P; bounded above by `2^(k+1) · C(|P|,k+1)`).
    let tail : ℝ := ∑ d ∈ P.powerset.filter (fun d => d.card = k + 1),
        ((2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
    (Even k → T ≤ full + tail) ∧ (Odd k → full - tail ≤ T)

/-! ### Helper: Bonferroni-at-`k = 0` inequality.

The standard `1 - ∏(1 - x_p) ≤ ∑ x_p` for `x_p ∈ [0, 1]`. -/

private lemma one_sub_prod_le_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) :
    (1 : ℝ) - (∏ p ∈ P, (1 - 2/(p : ℝ))) ≤ ∑ p ∈ P, (2/(p : ℝ)) := by
  classical
  induction P using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have hpps : ∀ p ∈ s, Nat.Prime p ∧ 3 ≤ p :=
      fun p hp => hP p (Finset.mem_cons_of_mem hp)
    have hap : Nat.Prime a ∧ 3 ≤ a := hP a (Finset.mem_cons_self a s)
    have ih' := ih hpps
    rw [Finset.prod_cons, Finset.sum_cons]
    set X : ℝ := (2 : ℝ) / (a : ℝ)
    set Y : ℝ := ∏ p ∈ s, (1 - 2/(p : ℝ))
    set Z : ℝ := ∑ p ∈ s, (2/(p : ℝ))
    have hY_le_one : Y ≤ 1 := by
      refine Finset.prod_le_one ?_ ?_
      · intro p hp
        exact (one_sub_two_div_prime_pos (hpps p hp).2).le
      · intro p hp
        have h3 : 3 ≤ p := (hpps p hp).2
        have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have h_two_div_nonneg : (0 : ℝ) ≤ 2 / (p : ℝ) :=
          div_nonneg (by norm_num) (le_of_lt hp_pos)
        linarith
    have hX_nn : 0 ≤ X := by
      have ha3 : 3 ≤ a := hap.2
      have ha_real : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha3
      have ha_pos : (0 : ℝ) < (a : ℝ) := by linarith
      exact div_nonneg (by norm_num) (le_of_lt ha_pos)
    have hXY_le_X : X * Y ≤ X := by
      have : X * Y ≤ X * 1 :=
        mul_le_mul_of_nonneg_left hY_le_one hX_nn
      simpa using this
    have habab : (1 - (1 - X) * Y) = (1 - Y) + X * Y := by ring
    rw [habab]
    linarith

/-! ### Helper: the residual Prop holds *vacuously* for `P = ∅`. -/

/-- The Bonferroni Prop is trivially satisfied for any `P` and any `k = 0`:
The `k = 0` truncated sum is exactly `1` (only the empty subset
contributes), the full Euler product over an empty `P` is `1`, and the
tail is the sum of `2/p` over singleton subsets — non-negative.  We
isolate this base case for sanity (it shows the Prop is at least
non-vacuously consistent at `k = 0`). -/
theorem pairedMainTermFromLocalDensity_at_k_zero
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) :
    let T : ℝ := ∑ d ∈ P.powerset.filter (fun d => d.card ≤ 0),
        ((-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
    let full : ℝ := ∏ p ∈ P, (1 - 2/(p : ℝ))
    let tail : ℝ := ∑ d ∈ P.powerset.filter (fun d => d.card = 0 + 1),
        ((2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))
    T ≤ full + tail := by
  classical
  simp only
  -- T : only `d = ∅` survives `d.card ≤ 0`.
  have hT_eq :
      (∑ d ∈ P.powerset.filter (fun d => d.card ≤ 0),
          ((-1 : ℝ)^d.card * (2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ)))
        = (1 : ℝ) := by
    have hFiltSingleton :
        P.powerset.filter (fun d => d.card ≤ 0) = ({∅} : Finset (Finset ℕ)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
        Nat.le_zero, Finset.card_eq_zero]
      constructor
      · rintro ⟨_, hd0⟩; exact hd0
      · rintro rfl
        refine ⟨Finset.empty_subset _, rfl⟩
    rw [hFiltSingleton]
    simp
  rw [hT_eq]
  -- We need 1 ≤ full + tail.  We bound `full ≥ 0` is *not* generally true if any
  -- factor is negative (but for primes ≥ 3 we have `1 - 2/p ∈ (0, 1]`).  Use
  -- pairedBrunFactor-style positivity for the assumed `3 ≤ p`.
  have hfull_pos : 0 < ∏ p ∈ P, (1 - 2/(p : ℝ)) := by
    refine Finset.prod_pos ?_
    intro p hp
    have h3 : 3 ≤ p := (hP p hp).2
    exact one_sub_two_div_prime_pos h3
  have hfull_le_one : ∏ p ∈ P, (1 - 2/(p : ℝ)) ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro p hp
      have h3 : 3 ≤ p := (hP p hp).2
      exact (one_sub_two_div_prime_pos h3).le
    · intro p hp
      have hpp : Nat.Prime p := (hP p hp).1
      have h3 : 3 ≤ p := (hP p hp).2
      have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
      have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
      have h_two_div_nonneg : (0 : ℝ) ≤ 2 / (p : ℝ) :=
        div_nonneg (by norm_num) (le_of_lt hp_pos)
      linarith
  -- Tail (sum over singleton subsets `d = {p}` for `p ∈ P` of `2/p`):
  have htail_nn :
      0 ≤ (∑ d ∈ P.powerset.filter (fun d => d.card = 0 + 1),
          ((2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ))) := by
    refine Finset.sum_nonneg ?_
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdpow, _⟩
    have hsub : d ⊆ P := Finset.mem_powerset.mp hdpow
    have hd_prod_pos : (0 : ℝ) < ((d.prod id : ℕ) : ℝ) := by
      have h : 0 < d.prod id := by
        refine Finset.prod_pos ?_
        intro p hp
        exact ((hP p (hsub hp)).1).pos
      exact_mod_cast h
    have hpow_nn : (0 : ℝ) ≤ (2 : ℝ)^d.card := by positivity
    exact div_nonneg hpow_nn (le_of_lt hd_prod_pos)
  have hkey : (1 : ℝ) - (∏ p ∈ P, (1 - 2/(p : ℝ))) ≤ ∑ p ∈ P, (2/(p : ℝ)) :=
    one_sub_prod_le_sum P hP
  -- Now compute: T = 1, RHS = full + tail; need 1 ≤ full + tail.
  -- tail (the filter for `d.card = 1`) = ∑ p ∈ P, (2/p).
  have htail_eq :
      (∑ d ∈ P.powerset.filter (fun d => d.card = 0 + 1),
          ((2 : ℝ)^d.card / ((d.prod id : ℕ) : ℝ)))
        = ∑ p ∈ P, ((2 : ℝ) / (p : ℝ)) := by
    -- Bijection between singleton subsets of P and elements of P.
    have : (P.powerset.filter (fun d => d.card = 0 + 1))
              = P.image (fun p => ({p} : Finset ℕ)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image,
        Nat.zero_add, Finset.card_eq_one]
      constructor
      · rintro ⟨hsub, p, rfl⟩
        refine ⟨p, ?_, rfl⟩
        exact hsub (Finset.mem_singleton_self p)
      · rintro ⟨p, hp, rfl⟩
        refine ⟨?_, p, rfl⟩
        intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]; exact hp
    rw [this]
    rw [Finset.sum_image (by
      intro p _ q _ hpq
      have : ({p} : Finset ℕ) = {q} := hpq
      exact Finset.singleton_inj.mp this)]
    refine Finset.sum_congr rfl ?_
    intro p _hp
    -- d = {p}, d.card = 1, d.prod id = p
    simp
  -- Goal: 1 ≤ full + tail.  We use `1 - full ≤ ∑ 2/p = tail`.
  rw [htail_eq]
  linarith

/-! ## Section 7 — Summary

`paired_eulerProduct_identity_signed` and `paired_eulerProduct_identity`
are *unconditionally proved* in mathlib v4.29.1 (axiom audit:
`Classical.choice`, `Quot.sound`, `propext`).  The Bonferroni-truncated
form `PairedMainTermFromLocalDensity` is *open* as a residual sub-Prop
of P17-T4 / S4. -/

end PathCPairedMainTermFromLocalDensity
end Gdbh
