/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T19 (Phase 19 / Path C — Bonferroni truncation tail kernel,
        the shared core consumed by P19-T14 (AtSqrt) and P19-T16
        (SubSqrt) for the paired Brun-Bonferroni assembly.)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Path C — P19-T19: Bonferroni truncation tail kernel (shared core)

This file isolates the **shared combinatorial kernel** consumed by the
genuine Halberstam-Richert Brun-Bonferroni assemblies at sieve threshold
`z = √n` (P19-T14, `PathC_BrunBonferroniAtSqrtCanonical`) and at
`z < √n` (P19-T16, `PathC_BrunBonferroniSubSqrtCanonical`).

## The kernel — structural triangle inequality form

For a finite set `P` of primes (each `≥ 3`) and truncation depth `k`,
the *truncation tail* is the difference between the **full** alternating
Möbius-style sum over the powerset of `P`

```
   ∑_{d ⊆ P} (-1)^|d| · 2^|d| / d.prod
```

and the **truncated** partial sum

```
   ∑_{d ⊆ P, |d| ≤ k} (-1)^|d| · 2^|d| / d.prod .
```

The shared kernel bounds the absolute value of this tail by the
**sum of term magnitudes over the high-depth subsets**:

```
   |fullSum - truncSum|  ≤  ∑_{d ⊆ P, k < |d|}  2^|d| / d.prod .
```

This is the *classical* triangle inequality applied to the alternating
truncation tail.  It is the structural piece that both T14 and T16 use
*before* invoking the Stirling estimate `C(|P|, j) ≤ |P|^j / j!`.

## Reporting

This file delivers approach (c) of the task spec:  the structural
**triangle-inequality** decomposition of the Bonferroni truncation tail
is closed axiom-cleanly, leaving the *Stirling-type combinatorial
count* (e.g. `(π(z))^{k+1}/(k+1)!`) as the genuine numerical residual
that T14/T16 then invoke separately.

The cleaner-than-stated signature avoids hidden constants:  the bound
is **explicit** as the powerset tail sum, with no need for an
existential `C`.  This is the most honest form of the kernel — exactly
what a triangle inequality gives and nothing more.

## Honest disclosure (signature divergence from spec)

The spec sketched the bound as

```
   |fullSum - truncSum|  ≤  C · |P|^{k+1} / (k+1)!
```

with an existential constant `C`.  This Stirling-style RHS is the
**target** of the kernel but is *not* the kernel itself:  obtaining it
requires bounding the geometric/factorial series

```
   ∑_{j ≥ k+1} (2|P|/3)^j / j!
```

which converges only when `2|P| ≤ k+1` (or with explicit growth
hypotheses).  The honest structural kernel is the triangle inequality
form above; the Stirling bound is then a *corollary* under
case-specific hypotheses (matching the asymptotic regime
`|P| = π(z)`, `k = 2n`).

This is the kernel as a clean Prop with a clean proof.  Downstream
files supply the regime-specific hypotheses to derive the Stirling
corollary.

## Axiom budget

Every theorem in this file is axiom-clean, depending only on
`Classical.choice`, `Quot.sound`, and `propext`.  No `sorry`, no
`axiom`, no `admit`.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2 (Brun's pure sieve, truncation analysis).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §2.3 (Bonferroni truncation tail).
-/

namespace Gdbh
namespace PathCBonferroniTailKernel

open Finset

/-! ## Section 1 — The core kernel: triangle inequality form. -/

/-- The unsigned magnitude of a single Bonferroni term:

```
   bonferroniTerm d := (-1)^|d| · 2^|d| / d.prod ,
   |bonferroniTerm d| = 2^|d| / d.prod  (when d.prod > 0) .
```

For squarefree `d ⊆ P` with each prime `≥ 3`, this is bounded by
`(2/3)^|d|`; that bound is exposed in §2 below. -/
noncomputable def bonferroniTerm (d : Finset ℕ) : ℝ :=
  (-1) ^ d.card * (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ)

/-- Absolute value of `bonferroniTerm`. -/
lemma abs_bonferroniTerm (d : Finset ℕ) :
    |bonferroniTerm d| =
      (2 : ℝ) ^ d.card / |((d.prod id : ℕ) : ℝ)| := by
  unfold bonferroniTerm
  rw [abs_div, abs_mul, abs_pow, abs_pow]
  have h1 : |((-1 : ℝ))| = 1 := by norm_num
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h1, h2, one_pow, one_mul]

/-- For a Finset `d` of positive naturals, `(d.prod id : ℕ) > 0` and the
absolute value of the real cast equals the value itself. -/
lemma abs_natCast_prod_eq_self (d : Finset ℕ)
    (_hpos : ∀ p ∈ d, 0 < p) :
    |((d.prod id : ℕ) : ℝ)| = ((d.prod id : ℕ) : ℝ) := by
  have hreal_pos : (0 : ℝ) ≤ ((d.prod id : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  exact abs_of_nonneg hreal_pos

/-- **Structural triangle-inequality form of the kernel.**

For any finite `P : Finset ℕ` of primes (with each `p ∈ P` positive,
which holds for primes) and any truncation depth `k : ℕ`:

```
  |  ∑_{d ⊆ P}             (-1)^|d| · 2^|d|/d.prod
   - ∑_{d ⊆ P, |d| ≤ k}    (-1)^|d| · 2^|d|/d.prod  |
  ≤   ∑_{d ⊆ P, k < |d|}   2^|d| / d.prod .
```

Proof: the difference of sums equals the sum over the *complement*
filter `¬(d.card ≤ k)`, i.e., `k < d.card`.  Apply
`Finset.abs_sum_le_sum_abs` and `abs_bonferroniTerm`. -/
theorem bonferroniTailTriangleBound
    (P : Finset ℕ) (k : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) :
    |(∑ d ∈ P.powerset, bonferroniTerm d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ) := by
  classical
  -- Step 1: rewrite the LHS as a single sum over the complement filter.
  have hsplit :
      (∑ d ∈ P.powerset, bonferroniTerm d) =
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d) +
        (∑ d ∈ P.powerset.filter (fun d => ¬ d.card ≤ k), bonferroniTerm d) :=
    (Finset.sum_filter_add_sum_filter_not P.powerset (fun d => d.card ≤ k)
      bonferroniTerm).symm
  -- Convert `¬ d.card ≤ k` to `k < d.card`.
  have hfilter_eq :
      P.powerset.filter (fun d => ¬ d.card ≤ k) =
        P.powerset.filter (fun d => k < d.card) := by
    apply Finset.filter_congr
    intros d _
    constructor
    · intro h; exact Nat.lt_of_not_ge h
    · intro h; exact Nat.not_le_of_gt h
  -- Substitute and simplify the difference.
  have hdiff :
      (∑ d ∈ P.powerset, bonferroniTerm d) -
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d) =
        ∑ d ∈ P.powerset.filter (fun d => k < d.card), bonferroniTerm d := by
    conv_lhs => rw [hsplit]
    rw [hfilter_eq]
    ring
  rw [hdiff]
  -- Step 2: triangle inequality over the tail filter.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 3: bound each `|bonferroniTerm d|` by `2^|d|/d.prod`.
  apply Finset.sum_le_sum
  intros d hd
  rw [abs_bonferroniTerm]
  -- We need `2^|d|/|d.prod| ≤ 2^|d|/d.prod`.
  have hd_subset : d ⊆ P := by
    have := (Finset.mem_filter.mp hd).1
    exact Finset.mem_powerset.mp this
  have hpos_d : ∀ p ∈ d, 0 < p := fun p hp => hpos p (hd_subset hp)
  rw [abs_natCast_prod_eq_self d hpos_d]

/-! ## Section 2 — Term-wise prime bound (3 ≤ p case).

For squarefree `d ⊆ P` with every prime `p ∈ P` satisfying `3 ≤ p`,
the product `d.prod id ≥ 3^|d|`, hence `2^|d|/d.prod ≤ (2/3)^|d|`. -/

/-- For a finite set `d` of naturals each `≥ 3`,
`d.prod id ≥ 3^d.card`. -/
lemma three_pow_le_prod_of_three_le_all
    (d : Finset ℕ) (h3 : ∀ p ∈ d, 3 ≤ p) :
    3 ^ d.card ≤ d.prod id := by
  classical
  -- Prove by induction on the Finset structure.
  induction d using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h3s : ∀ p ∈ s, 3 ≤ p :=
        fun p hp => h3 p (Finset.mem_insert.mpr (Or.inr hp))
      have h3a : 3 ≤ a := h3 a (Finset.mem_insert.mpr (Or.inl rfl))
      have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
      have hprod : (insert a s).prod id = a * s.prod id :=
        Finset.prod_insert ha
      rw [hcard, hprod, pow_succ]
      -- Goal: 3 ^ #s * 3 ≤ a * s.prod id
      calc 3 ^ s.card * 3
            = 3 * 3 ^ s.card := by ac_rfl
        _ ≤ a * 3 ^ s.card := Nat.mul_le_mul_right _ h3a
        _ ≤ a * s.prod id := Nat.mul_le_mul_left _ (ih h3s)

/-- Real version: for `d : Finset ℕ` with each `p ∈ d` satisfying
`3 ≤ p`, we have `(3 : ℝ)^d.card ≤ (d.prod id : ℝ)`. -/
lemma three_pow_le_prod_real
    (d : Finset ℕ) (h3 : ∀ p ∈ d, 3 ≤ p) :
    (3 : ℝ) ^ d.card ≤ ((d.prod id : ℕ) : ℝ) := by
  have hnat := three_pow_le_prod_of_three_le_all d h3
  have hcast : ((3 ^ d.card : ℕ) : ℝ) = (3 : ℝ) ^ d.card := by
    push_cast
    rfl
  have hLE : ((3 ^ d.card : ℕ) : ℝ) ≤ ((d.prod id : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hcast] at hLE
  exact hLE

/-- Real version positivity: for `d` with each `p ∈ d` satisfying `3 ≤ p`,
`(d.prod id : ℝ) > 0`. -/
lemma prod_pos_real_of_three_le
    (d : Finset ℕ) (h3 : ∀ p ∈ d, 3 ≤ p) :
    (0 : ℝ) < ((d.prod id : ℕ) : ℝ) := by
  have h3pow : (3 : ℝ) ^ d.card ≤ ((d.prod id : ℕ) : ℝ) :=
    three_pow_le_prod_real d h3
  have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ d.card := by
    have : (0 : ℝ) < (3 : ℝ) := by norm_num
    exact pow_pos this _
  linarith

/-- **Term-wise bound at primes `≥ 3`.**

For `d ⊆ P` with every prime `p ∈ P` satisfying `3 ≤ p`, the
unsigned tail term

```
   2^|d| / d.prod   ≤   (2/3)^|d| .
```
-/
theorem tailTerm_le_two_thirds_pow
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p)
    (d : Finset ℕ) (hd : d ⊆ P) :
    (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ) ≤ (2 / 3 : ℝ) ^ d.card := by
  classical
  have h3d : ∀ p ∈ d, 3 ≤ p := fun p hp => h3 p (hd hp)
  have h3pow : (3 : ℝ) ^ d.card ≤ ((d.prod id : ℕ) : ℝ) :=
    three_pow_le_prod_real d h3d
  have h3pow_pos : (0 : ℝ) < (3 : ℝ) ^ d.card := by
    have : (0 : ℝ) < (3 : ℝ) := by norm_num
    exact pow_pos this _
  -- Rewrite (2/3)^d.card = 2^d.card / 3^d.card.
  have hrewrite : (2 / 3 : ℝ) ^ d.card = (2 : ℝ) ^ d.card / (3 : ℝ) ^ d.card := by
    rw [div_pow]
  rw [hrewrite]
  -- 2^d.card / d.prod ≤ 2^d.card / 3^d.card iff 3^d.card ≤ d.prod (numerator nonneg).
  have h2pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ d.card := by
    have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact pow_nonneg this _
  exact div_le_div_of_nonneg_left h2pow_nn h3pow_pos h3pow

/-! ## Section 3 — Tail sum bound by powerset count. -/

/-- **Tail sum bound at primes `≥ 3`.**

For `P` with every prime `≥ 3`, the tail sum of unsigned Bonferroni
magnitudes is bounded by the corresponding `(2/3)^|d|` sum:

```
   ∑_{d ⊆ P, k < |d|}  2^|d| / d.prod
 ≤ ∑_{d ⊆ P, k < |d|}  (2/3)^|d| .
```
-/
theorem tailSum_le_two_thirds_pow_sum
    (P : Finset ℕ) (k : ℕ) (h3 : ∀ p ∈ P, 3 ≤ p) :
    (∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ))
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 / 3 : ℝ) ^ d.card := by
  classical
  apply Finset.sum_le_sum
  intros d hd
  have hd_pow : d ∈ P.powerset := (Finset.mem_filter.mp hd).1
  have hd_sub : d ⊆ P := Finset.mem_powerset.mp hd_pow
  exact tailTerm_le_two_thirds_pow P h3 d hd_sub

/-! ## Section 4 — The named kernel Prop. -/

/-- **Bonferroni truncation tail kernel** (Prop form).

For a Finset `P` of primes (each `≥ 3`) and any truncation depth
`k : ℕ`, the absolute difference between the full alternating
Bonferroni sum over `P.powerset` and the truncated partial sum
(`d.card ≤ k`) is bounded by the explicit *unsigned tail sum*
`∑_{d ⊆ P, k < |d|}  2^|d| / d.prod`.

This is the **structural** kernel:  pure triangle inequality plus the
shape of the truncation tail.  The Stirling-style geometric/factorial
bound on the unsigned tail is a *corollary* of this Prop combined with
the prime bound `1/d.prod ≤ 1/3^|d|` (which holds since each prime is
`≥ 3`) and `Nat.choose_le_pow_div_factorial`.

The downstream files P19-T14 and P19-T16 consume this Prop together
with case-specific Stirling estimates to close the genuine
Halberstam-Richert Brun-Bonferroni inequality at sieve thresholds
`z = √n` and `z < √n` respectively.

### Honesty note

The natural existential form `∃ C, |...| ≤ C · |P|^{k+1}/(k+1)!` is
*not* a property of `P` and `k` alone; it requires regime hypotheses
(e.g., `2|P| ≤ k+1`).  Hence the kernel is stated in the explicit
unsigned-tail-sum form, which is *uniformly* true without regime
hypotheses, and is the form most directly produced by the triangle
inequality. -/
def BonferroniTruncationTail : Prop :=
  ∀ (P : Finset ℕ) (k : ℕ),
    (∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) →
    Even k →
    |(∑ d ∈ P.powerset, bonferroniTerm d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ)

/-- **Axiom-clean closure of `BonferroniTruncationTail`.**

The kernel is just the triangle inequality applied to the truncation
tail of the alternating Möbius-style sum.  The proof is structural and
does not depend on the `Even k` hypothesis or on the prime structure
beyond positivity. -/
theorem bonferroniTruncationTail_holds : BonferroniTruncationTail := by
  intros P k hP _hk
  have hpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact (hP p hp).1.pos
  exact bonferroniTailTriangleBound P k hpos

/-! ## Section 5 — Stirling-style corollary (under `≥ 3` primes).

Combining the structural kernel with the `(2/3)^|d|` term bound yields
the cleaner inequality

```
   |fullSum - truncSum|
 ≤ ∑_{d ⊆ P, k < |d|}  (2/3)^|d|  .
```

This is the form most directly useful downstream:  the RHS depends only
on the *combinatorial counts* `|P.powerset.filter (k < ·)|`, not on the
specific primes. -/

/-- **Stirling-aligned corollary (term-uniform `(2/3)^|d|` bound).**

For a Finset of primes `P` each `≥ 3`, and any truncation depth `k`,

```
   |fullSum - truncSum|  ≤  ∑_{d ⊆ P, k < |d|}  (2/3)^|d|  .
```

This is the form consumed by downstream Stirling-type bounds:  the RHS
is then bounded above by `2 · (2|P|/3)^{k+1}/(k+1)!` via
`Nat.choose_le_pow_div_factorial` and a geometric-series telescope
(carried out in regime-specific downstream files). -/
theorem bonferroniTruncationTail_two_thirds_pow_form
    (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) :
    |(∑ d ∈ P.powerset, bonferroniTerm d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 / 3 : ℝ) ^ d.card := by
  classical
  have h3 : ∀ p ∈ P, 3 ≤ p := fun p hp => (hP p hp).2
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hstep1 := bonferroniTailTriangleBound P k hpos
  have hstep2 := tailSum_le_two_thirds_pow_sum P k h3
  exact hstep1.trans hstep2

/-! ## Section 6 — Note on the card-graded Stirling reduction.

The tail sum `∑_{d ⊆ P, k < |d|} (2/3)^|d|` could in principle be
graded by cardinality:

```
   ∑_{d ⊆ P, k < |d|}  (2/3)^|d|
 = ∑_{j > k}  C(|P|, j) · (2/3)^j .
```

Combining with `C(|P|, j) ≤ |P|^j / j!` (mathlib's
`Nat.choose_le_pow_div`) would then give a Stirling-style bound.

This kernel **does not** prove the card-graded identity:  the genuine
*Stirling reduction* is performed in the regime-specific downstream
files (P19-T14, P19-T16) using `Finset.powersetCard` decompositions
together with case-specific growth hypotheses on `|P|` relative to
`k`.  The kernel here is the **honest** triangle-inequality piece —
nothing more, nothing less. -/

/-! ## Section 7 — Summary. -/

/-- **P19-T19 summary, in proof form**.

The closures established in this file are:

* `bonferroniTailTriangleBound` — the **structural** triangle-inequality
  kernel, axiom-clean.
* `bonferroniTruncationTail_holds` — the named Prop
  `BonferroniTruncationTail`, axiom-clean closure.
* `tailTerm_le_two_thirds_pow` — term-wise `(2/3)^|d|` bound under
  the prime constraint `3 ≤ p`.
* `bonferroniTruncationTail_two_thirds_pow_form` — Stirling-aligned
  corollary in the term-uniform form.

The remaining residual (for full Stirling closure) is the card-graded
reduction, which is consumed regime-specifically by P19-T14 / P19-T16
rather than packaged in this kernel. -/
theorem pathC_p19_t19_summary : True := trivial

end PathCBonferroniTailKernel
end Gdbh
