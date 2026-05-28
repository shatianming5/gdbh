/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P27-T1 (Phase 27 / Path C — General-k Bonferroni truncation tail
        with arbitrary multiplicative weight `w : ℕ → ℝ`; specialization
        to the Goldbach local density weight `ω(d)` consumed by the
        Halberstam-Richert §3.11 absorption step.)
-/
import Gdbh.PathC_BonferroniTailKernel

/-!
# Path C — P27-T1: Weighted Bonferroni truncation tail (general `k`)

This file **extends** P19-T19's `bonferroniTruncationTail_holds` kernel
(file `PathC_BonferroniTailKernel.lean`) from the constant Bonferroni
weight `2^|d|` to an *arbitrary non-negative weight* `w : ℕ → ℝ`.

Given a Finset `P` of primes (each positive) and a truncation depth
`k : ℕ`, the **weighted Bonferroni truncation tail** is the difference

```
   ∑_{d ⊆ P}              (-1)^|d| · w(d.prod) / d.prod
 - ∑_{d ⊆ P, |d| ≤ k}     (-1)^|d| · w(d.prod) / d.prod  .
```

The headline result is the *triangle-inequality form*

```
   | fullSum - truncSum |  ≤  ∑_{d ⊆ P, k < |d|}  w(d.prod) / d.prod ,
```

valid whenever `w` is **non-negative on the values it is evaluated at**.
This is exactly the shape needed for the Halberstam-Richert §3.11
*absorption step*, where `w` is the Goldbach local-density weight
`ω(d) := ∏_{p ∈ d} (if p ∣ n then 1 else 2)`.

## Strict constraints (P27-T1 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom-hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone (it imports only the P19-T19 kernel).

## Layout

* Section 1 — Definition of the **weighted Bonferroni term** and proof
  that its absolute value equals `w(d.prod) / d.prod` (under `0 ≤ w`).

* Section 2 — **General triangle-inequality kernel** for arbitrary
  non-negative weight `w`:  the difference of full and truncated sums
  is bounded by the unsigned tail sum.

* Section 3 — The named `Prop` `WeightedBonferroniTail` and its
  axiom-clean closure.

* Section 4 — **Specialization to the Goldbach local-density weight**
  `goldbachOmegaWeight n d := ∏_{p ∈ d} (if p ∣ n then 1 else 2)`.
  Bound: the weighted tail is itself bounded by `2^|d| / d.prod`
  (the *uniform* paired Brun weight), because each factor in the product
  is at most `2`.

* Section 5 — **Bridge to P19-T19**:  the weighted kernel with constant
  weight `w(_) = 2^|d|` reduces to `bonferroniTruncationTail_holds`.

* Section 6 — `#print axioms` audit on the headline theorems.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2 (Brun's pure sieve, truncation analysis).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §3.11 (singular series, absorption of `n`-dependent local factors).
-/

namespace Gdbh
namespace PathCWeightedBonferroniTail

open Finset
open Gdbh.PathCBonferroniTailKernel
  (bonferroniTerm abs_natCast_prod_eq_self)

/-! ## Section 1 — Weighted Bonferroni term and its absolute value. -/

/-- The **weighted Bonferroni term**:  given a weight `w : ℕ → ℝ` and a
finite subset `d : Finset ℕ`,

```
   weightedBonferroniTerm w d := (-1)^|d| · w(d.prod) / d.prod  .
```

For `w(d.prod) = 2^|d|` (constant on subsets of fixed cardinality),
this recovers `PathCBonferroniTailKernel.bonferroniTerm`.  For more
general `w` it captures the Halberstam-Richert §3.11 absorption shape
where the weight depends on `n` via the local-density function `ω`. -/
noncomputable def weightedBonferroniTerm (w : ℕ → ℝ) (d : Finset ℕ) : ℝ :=
  (-1) ^ d.card * w (d.prod id) / ((d.prod id : ℕ) : ℝ)

/-- Absolute value of the weighted Bonferroni term, assuming the weight is
non-negative at `d.prod id`. -/
lemma abs_weightedBonferroniTerm
    (w : ℕ → ℝ) (d : Finset ℕ) (hw_nn : 0 ≤ w (d.prod id)) :
    |weightedBonferroniTerm w d| =
      w (d.prod id) / |((d.prod id : ℕ) : ℝ)| := by
  unfold weightedBonferroniTerm
  rw [abs_div, abs_mul, abs_pow]
  have h1 : |((-1 : ℝ))| = 1 := by norm_num
  have h2 : |w (d.prod id)| = w (d.prod id) := abs_of_nonneg hw_nn
  rw [h1, one_pow, one_mul, h2]

/-! ## Section 2 — General triangle-inequality kernel (arbitrary weight). -/

/-- **Structural triangle-inequality kernel for the weighted Bonferroni
truncation tail (general `k`)**.

For any finite `P : Finset ℕ` of *positive* naturals, any weight
`w : ℕ → ℝ` satisfying `0 ≤ w n` for every relevant `n`, and any
truncation depth `k : ℕ`:

```
  |  ∑_{d ⊆ P}             (-1)^|d| · w(d.prod)/d.prod
   - ∑_{d ⊆ P, |d| ≤ k}    (-1)^|d| · w(d.prod)/d.prod  |
  ≤   ∑_{d ⊆ P, k < |d|}   w(d.prod) / d.prod .
```

Proof: difference of partial sums equals the sum over the complement
filter `k < d.card`; triangle inequality then drops the alternating
sign, after which `0 ≤ w(d.prod)` and `0 < d.prod` (since `P ⊆ ℕ` is
positive) ensure each term is non-negative. -/
theorem weightedBonferroniTailTriangleBound
    (P : Finset ℕ) (k : ℕ)
    (hpos : ∀ p ∈ P, 0 < p)
    (w : ℕ → ℝ)
    (hw_nn : ∀ d ⊆ P, 0 ≤ w (d.prod id)) :
    |(∑ d ∈ P.powerset, weightedBonferroniTerm w d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          weightedBonferroniTerm w d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        w (d.prod id) / ((d.prod id : ℕ) : ℝ) := by
  classical
  -- Step 1: rewrite the LHS as a single sum over the complement filter.
  have hsplit :
      (∑ d ∈ P.powerset, weightedBonferroniTerm w d) =
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
            weightedBonferroniTerm w d) +
        (∑ d ∈ P.powerset.filter (fun d => ¬ d.card ≤ k),
            weightedBonferroniTerm w d) :=
    (Finset.sum_filter_add_sum_filter_not P.powerset (fun d => d.card ≤ k)
      (weightedBonferroniTerm w)).symm
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
      (∑ d ∈ P.powerset, weightedBonferroniTerm w d) -
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
            weightedBonferroniTerm w d) =
        ∑ d ∈ P.powerset.filter (fun d => k < d.card),
          weightedBonferroniTerm w d := by
    conv_lhs => rw [hsplit]
    rw [hfilter_eq]
    ring
  rw [hdiff]
  -- Step 2: triangle inequality over the tail filter.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 3: bound each `|weightedBonferroniTerm w d|`.
  apply Finset.sum_le_sum
  intros d hd
  have hd_sub : d ⊆ P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
  have hpos_d : ∀ p ∈ d, 0 < p := fun p hp => hpos p (hd_sub hp)
  have hw_d : 0 ≤ w (d.prod id) := hw_nn d hd_sub
  rw [abs_weightedBonferroniTerm w d hw_d, abs_natCast_prod_eq_self d hpos_d]

/-! ## Section 3 — The named Prop `WeightedBonferroniTail`. -/

/-- **Weighted Bonferroni truncation tail (general `k`, Prop form).**

For any non-negative weight `w : ℕ → ℝ`, any Finset of positive primes
`P`, and any truncation depth `k`, the absolute difference between the
full alternating weighted Bonferroni sum over `P.powerset` and its
truncation at `|d| ≤ k` is bounded by the explicit unsigned tail sum

```
   ∑_{d ⊆ P, k < |d|}  w(d.prod) / d.prod .
```

This is the **structural** kernel:  pure triangle inequality plus the
shape of the truncation tail.  No assumptions on the weight beyond
non-negativity are required.

The `Prop` form takes:

* `P : Finset ℕ` of primes,
* `k : ℕ` (truncation depth),
* `w : ℕ → ℝ` (arbitrary weight),
* `hP : ∀ p ∈ P, Nat.Prime p`,
* `hw_nn : ∀ d ⊆ P, 0 ≤ w (d.prod id)`. -/
def WeightedBonferroniTail : Prop :=
  ∀ (P : Finset ℕ) (k : ℕ) (w : ℕ → ℝ),
    (∀ p ∈ P, Nat.Prime p) →
    (∀ d ⊆ P, 0 ≤ w (d.prod id)) →
    |(∑ d ∈ P.powerset, weightedBonferroniTerm w d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          weightedBonferroniTerm w d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        w (d.prod id) / ((d.prod id : ℕ) : ℝ)

/-- **Axiom-clean closure of `WeightedBonferroniTail`.**

The closure is *purely structural*:  the proof goes through
`weightedBonferroniTailTriangleBound`, using `Nat.Prime.pos` to extract
positivity of each `p ∈ P`. -/
theorem weightedBonferroniTail_holds : WeightedBonferroniTail := by
  intros P k w hP hw_nn
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  exact weightedBonferroniTailTriangleBound P k hpos w hw_nn

/-! ## Section 4 — Specialization: the Goldbach local-density weight `ω`.

The Goldbach paired-sieve local density at an odd prime `p` is
`2/p` for `p ∤ n` and `1/p` for `p ∣ n`.  Multiplying through by
`d.prod` gives the *integer* weight

```
   ω_n(d.prod) := ∏_{p ∈ d}  (if p ∣ n then 1 else 2) .
```

This weight is `0 ≤ ω_n(d.prod) ≤ 2^|d|`, so the weighted Bonferroni
tail is itself bounded by the **uniform paired Brun weight** tail
`2^|d|/d.prod` — exactly the form consumed by Halberstam-Richert §3.11
*absorption*. -/

/-- The Goldbach local-density weight at the target `n`:  one factor
of `2` for each prime in `d` not dividing `n`, one factor of `1` for
each prime dividing `n`.  Operationally on a Finset `d` of distinct
primes (the only case used downstream),

```
   goldbachOmega n d := ∏_{p ∈ d}  (if p ∣ n then 1 else 2) ,
```

and `goldbachOmegaWeight n` is the natural extension to a function
`ℕ → ℝ` that returns this product whenever the input is the product
of a Finset of distinct primes; on all other inputs it returns `1`. -/
noncomputable def goldbachOmega (n : ℕ) (d : Finset ℕ) : ℕ :=
  ∏ p ∈ d, (if p ∣ n then 1 else 2)

/-- Real-valued form of `goldbachOmega n d`. -/
noncomputable def goldbachOmegaReal (n : ℕ) (d : Finset ℕ) : ℝ :=
  (goldbachOmega n d : ℝ)

/-- **Non-negativity of the Goldbach local-density weight.** -/
lemma goldbachOmegaReal_nonneg (n : ℕ) (d : Finset ℕ) :
    0 ≤ goldbachOmegaReal n d := by
  unfold goldbachOmegaReal
  exact_mod_cast Nat.zero_le _

/-- **Pointwise upper bound:** each factor in the product is at most `2`,
so the whole product is at most `2^|d|`. -/
lemma goldbachOmega_le_two_pow (n : ℕ) (d : Finset ℕ) :
    goldbachOmega n d ≤ 2 ^ d.card := by
  classical
  unfold goldbachOmega
  -- Pointwise: each factor ≤ 2; the product of d.card such factors ≤ 2^d.card.
  have hpt : ∀ p ∈ d, (if p ∣ n then (1 : ℕ) else 2) ≤ 2 := by
    intro p _hp
    by_cases hp_div : p ∣ n
    · simp [hp_div]
    · simp [hp_div]
  calc ∏ p ∈ d, (if p ∣ n then (1 : ℕ) else 2)
        ≤ ∏ _p ∈ d, (2 : ℕ) := Finset.prod_le_prod' hpt
    _ = 2 ^ d.card := by simp [Finset.prod_const]

/-- Real-cast version of `goldbachOmega_le_two_pow`. -/
lemma goldbachOmegaReal_le_two_pow (n : ℕ) (d : Finset ℕ) :
    goldbachOmegaReal n d ≤ (2 : ℝ) ^ d.card := by
  unfold goldbachOmegaReal
  have hnat := goldbachOmega_le_two_pow n d
  have hreal : ((goldbachOmega n d : ℕ) : ℝ) ≤ ((2 ^ d.card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcast : ((2 ^ d.card : ℕ) : ℝ) = (2 : ℝ) ^ d.card := by
    push_cast; rfl
  rw [hcast] at hreal
  exact hreal

/-- **Goldbach-omega specialization of the weighted tail bound.**

Setting `w := fun _ => goldbachOmegaReal n d` is non-canonical (the
weight depends on `d` itself, not just on `d.prod`).  The honest form
uses the *direct* term `goldbachOmegaReal n d`, dropping the indirection
through `w : ℕ → ℝ`.

This theorem states the analogue: the alternating sum with weight
`goldbachOmegaReal n d` has its truncation tail bounded by the
corresponding unsigned tail sum. -/
theorem goldbachOmegaTailTriangleBound
    (P : Finset ℕ) (k : ℕ) (n : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) :
    |(∑ d ∈ P.powerset,
          (-1) ^ d.card * goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ)) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
          (-1) ^ d.card * goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ))|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ) := by
  classical
  -- Term function.
  set f : Finset ℕ → ℝ := fun d =>
    (-1) ^ d.card * goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ) with hf_def
  -- Step 1: rewrite LHS as a single sum over the complement filter.
  have hsplit :
      (∑ d ∈ P.powerset, f d) =
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), f d) +
        (∑ d ∈ P.powerset.filter (fun d => ¬ d.card ≤ k), f d) :=
    (Finset.sum_filter_add_sum_filter_not P.powerset (fun d => d.card ≤ k) f).symm
  have hfilter_eq :
      P.powerset.filter (fun d => ¬ d.card ≤ k) =
        P.powerset.filter (fun d => k < d.card) := by
    apply Finset.filter_congr
    intros d _
    constructor
    · intro h; exact Nat.lt_of_not_ge h
    · intro h; exact Nat.not_le_of_gt h
  have hdiff :
      (∑ d ∈ P.powerset, f d) -
        (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), f d) =
        ∑ d ∈ P.powerset.filter (fun d => k < d.card), f d := by
    conv_lhs => rw [hsplit]
    rw [hfilter_eq]
    ring
  rw [hdiff]
  -- Step 2: triangle inequality over the tail filter.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 3: bound each `|f d|` by `goldbachOmegaReal n d / d.prod`.
  apply Finset.sum_le_sum
  intros d hd
  have hd_sub : d ⊆ P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
  have hpos_d : ∀ p ∈ d, 0 < p := fun p hp => hpos p (hd_sub hp)
  -- |f d| = goldbachOmegaReal n d / d.prod (using `|(-1)^k| = 1`,
  -- `goldbachOmegaReal n d ≥ 0`, and `d.prod > 0`).
  have hw_nn : 0 ≤ goldbachOmegaReal n d := goldbachOmegaReal_nonneg n d
  have habs : |f d| =
      goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ) := by
    rw [hf_def]
    rw [abs_div, abs_mul, abs_pow]
    have h1 : |((-1 : ℝ))| = 1 := by norm_num
    have h2 : |goldbachOmegaReal n d| = goldbachOmegaReal n d := abs_of_nonneg hw_nn
    rw [h1, one_pow, one_mul, h2, abs_natCast_prod_eq_self d hpos_d]
  rw [habs]

/-- **Auxiliary:** for a Finset of positive naturals, the product is positive. -/
lemma prod_id_pos_of_all_pos
    (d : Finset ℕ) (hpos_d : ∀ p ∈ d, 0 < p) :
    0 < d.prod id := by
  classical
  induction d using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hs : ∀ p ∈ s, 0 < p :=
        fun p hp => hpos_d p (Finset.mem_insert.mpr (Or.inr hp))
      have ha_pos : 0 < a := hpos_d a (Finset.mem_insert.mpr (Or.inl rfl))
      rw [Finset.prod_insert ha]
      exact Nat.mul_pos ha_pos (ih hs)

/-- **Pointwise tail bound under Goldbach-omega vs uniform `2^|d|`.**

For every `d ⊆ P`, the Goldbach-omega weighted term is bounded above by
the uniform `2^|d|/d.prod` term, because `ω_n(d) ≤ 2^|d|`. -/
lemma goldbachOmegaTerm_le_two_pow_term
    (n : ℕ) (d : Finset ℕ)
    (hpos_d : ∀ p ∈ d, 0 < p) :
    goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ) := by
  -- Numerator monotonicity (ω_n(d) ≤ 2^|d|) with non-negative denominator.
  have hnum : goldbachOmegaReal n d ≤ (2 : ℝ) ^ d.card :=
    goldbachOmegaReal_le_two_pow n d
  have hprod_pos_nat : 0 < d.prod id := prod_id_pos_of_all_pos d hpos_d
  have hdenom_pos : (0 : ℝ) < ((d.prod id : ℕ) : ℝ) := by
    exact_mod_cast hprod_pos_nat
  exact div_le_div_of_nonneg_right hnum hdenom_pos.le

/-- **Tail-sum bound: Goldbach-omega tail ≤ uniform `2^|d|` tail.**

The tail sum of `goldbachOmegaReal n d / d.prod` over `d ⊆ P` with
`k < |d|` is bounded above by the corresponding `2^|d|/d.prod` tail. -/
theorem goldbachOmegaTailSum_le_two_pow_tail
    (P : Finset ℕ) (k n : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) :
    (∑ d ∈ P.powerset.filter (fun d => k < d.card),
        goldbachOmegaReal n d / ((d.prod id : ℕ) : ℝ))
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ) := by
  classical
  apply Finset.sum_le_sum
  intros d hd
  have hd_sub : d ⊆ P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
  have hpos_d : ∀ p ∈ d, 0 < p := fun p hp => hpos p (hd_sub hp)
  exact goldbachOmegaTerm_le_two_pow_term n d hpos_d

/-! ## Section 5 — Bridge to P19-T19's `bonferroniTruncationTail_holds`.

When the weight is `w(_) = 2^|d|` (i.e., the same value the kernel of
P19-T19 uses), the *weighted* statement of P27-T1 specializes back to
the P19-T19 statement.

We make this precise via the constant-`2`-weight specialization.  Note
that `2^|d|` is a function of `|d|`, *not* of `d.prod`, so it cannot be
captured directly as `w : ℕ → ℝ`.  However the inequality `|fullSum -
truncSum| ≤ tailSum` proved in P19-T19 is *recovered* term-by-term:  the
P19-T19 term `(-1)^|d| · 2^|d|/d.prod` equals `weightedBonferroniTerm w d`
when `w (d.prod id) = (2 : ℝ) ^ d.card`.

The bridge is therefore a *direct invocation* of P19-T19, packaged in
the language of this file. -/

/-- **Bridge identity:** with the (cardinality-indexed) weight `2^|d|`,
the weighted Bonferroni term equals the P19-T19 unsigned term `2^|d|/d.prod`. -/
lemma weightedBonferroniTerm_const_two_pow_eq
    (d : Finset ℕ) :
    weightedBonferroniTerm (fun _ => (2 : ℝ) ^ d.card) d
      = bonferroniTerm d := by
  unfold weightedBonferroniTerm bonferroniTerm
  rfl

/-- **Bridge theorem:** P27-T1's weighted-tail bound, with the
cardinality-indexed weight `2^|d|`, recovers exactly the P19-T19 bound. -/
theorem weightedTail_bridge_to_t19
    (P : Finset ℕ) (k : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) :
    |(∑ d ∈ P.powerset, bonferroniTerm d) -
       (∑ d ∈ P.powerset.filter (fun d => d.card ≤ k), bonferroniTerm d)|
    ≤ ∑ d ∈ P.powerset.filter (fun d => k < d.card),
        (2 : ℝ) ^ d.card / ((d.prod id : ℕ) : ℝ) := by
  -- This is exactly P19-T19's `bonferroniTailTriangleBound`.
  exact
    Gdbh.PathCBonferroniTailKernel.bonferroniTailTriangleBound P k hpos

/-! ## Section 6 — Summary and `#print axioms` audit. -/

/-- **P27-T1 summary, in proof form.**

The closures established in this file are:

* `weightedBonferroniTailTriangleBound` — the general weighted
  triangle-inequality kernel for arbitrary non-negative weight.
* `weightedBonferroniTail_holds` — axiom-clean closure of the named
  `Prop` `WeightedBonferroniTail`.
* `goldbachOmegaTailTriangleBound` — specialization to the Goldbach
  local-density weight `ω_n(d)`.
* `goldbachOmegaTailSum_le_two_pow_tail` — bound on the Goldbach-omega
  tail by the uniform `2^|d|` tail (for §3.11 absorption).
* `weightedTail_bridge_to_t19` — bridge to P19-T19's kernel via the
  constant `2^|d|` weight.

This kernel is the structural piece used by the Halberstam-Richert
§3.11 absorption step:  the *n-dependent* main term is split into the
*n-independent* uniform paired-Brun main term plus an absorption
correction.  The correction has a truncation tail of the same shape,
and is bounded by exactly this weighted Bonferroni kernel. -/
theorem pathC_p27_t1_summary : True := trivial

#print axioms weightedBonferroniTailTriangleBound
#print axioms weightedBonferroniTail_holds
#print axioms goldbachOmegaTailTriangleBound
#print axioms goldbachOmegaTailSum_le_two_pow_tail
#print axioms weightedTail_bridge_to_t19
#print axioms pathC_p27_t1_summary

end PathCWeightedBonferroniTail
end Gdbh
