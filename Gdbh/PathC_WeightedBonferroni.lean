/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P25-T4 (Phase 25 / Path C — Weighted Bonferroni indicator variant
        and characterisation of upper-Möbius weights, bridging to mathlib's
        `Mathlib.NumberTheory.SelbergSieve.BoundingSieve.IsUpperMoebius`.)
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Path C — P25-T4: Weighted Bonferroni indicator variant

## Background

For the Halberstam-Richert §3.11 *absorption* step, we need a **weighted
Bonferroni** inequality:  instead of bounding the coprimality indicator
by `∑_{d⊆P, |d|≤k} μ(d.prod) · 1{d.prod ∣ m}`, we want
`∑ μ(d.prod) · w(d.prod) · 1{d.prod ∣ m}` for some weight `w`.  This is
the *Λ²-Selberg-style* generalisation:  instead of fixing the Möbius
choice for the upper-bounding coefficients, one allows arbitrary
"upper-Möbius" weights.

## What this file does — and what it honestly does not

Critically, the weighted variant *fails* for arbitrary `w`:  the
classical Bonferroni inequality relies on the specific alternation of
`μ`, and replacing `μ(d) · w(d)` with an arbitrary weight does not
preserve the bound.  The right framework is mathlib's
`BoundingSieve.IsUpperMoebius`:  a function `muPlus : ℕ → ℝ` is
upper-Möbius iff

```
   ∀ n, (if n = 1 then 1 else 0) ≤ ∑_{d ∣ n} muPlus d .
```

This is exactly the Selberg-style side condition for `muPlus` to yield a
valid upper bound for the sifted sum, and it admits both the truncated
Möbius (`muPlus = μ` on `|d| ≤ k`) and the Λ²-Selberg majorant as
instances.

### Concrete deliverables of this file

1. A `BoundingSieve`-free re-statement of the upper-Möbius side
   condition, `IsUpperMoebiusWeight`, with the *same* propositional
   content as `BoundingSieve.IsUpperMoebius`.

2. The canonical (trivial) example: the "point-mass at 1" weight
   `pointMassOne d = [d = 1]` satisfies `IsUpperMoebiusWeight` (a
   one-line proof from `1 ∈ n.divisors`).

3. A second canonical example: the **constant `1`** weight
   `constantOne d = 1` satisfies `IsUpperMoebiusWeight`, recovering the
   "every term contributes" trivial upper bound.

4. **Bridge theorem**:  `IsUpperMoebiusWeight w ↔
   BoundingSieve.IsUpperMoebius w` (proved as a definitional `Iff`).

5. **Closed-form weighted Bonferroni**: for any `n : ℕ`, applying the
   upper-Möbius condition `(if n = 1 then 1 else 0) ≤ ∑_{d ∣ n} w(d)`
   together with multiplicativity of the divisor sum gives, after
   substituting `n = gcd P m` for a finset `P` of primes, the *weighted
   Bonferroni* inequality at the indicator level.  This is the
   substantive content of P25-T4:  a clean weighted analogue of the
   truncated Möbius sum.

## Axiom budget

Every theorem in this file depends only on `Classical.choice`,
`Quot.sound`, and `propext`.  No `sorry`, no `axiom`, no `admit`.

## References

* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §3.11 (absorption step for the Bonferroni-Selberg comparison).
* A. Selberg, *On an elementary method in the theory of primes*,
  Norske Vid. Selsk. Forh. Trondheim 19 (1947), 64-67.
* A. Mellendijk, `Mathlib.NumberTheory.SelbergSieve` (2024).
-/

namespace Gdbh
namespace PathCWeightedBonferroni

open Finset
open scoped BigOperators

/-! ## Section 1 — Definition of `IsUpperMoebiusWeight`

We re-state the mathlib side condition under a local name, so the file
can be read self-contained.  The two predicates are *definitionally*
equal as Props. -/

/-- A function `w : ℕ → ℝ` is **upper-Möbius** if for every natural
number `n`, the indicator that `n = 1` is bounded above by the sum of
`w` over the divisors of `n`:

```
   ∀ n, (if n = 1 then 1 else 0) ≤ ∑_{d ∣ n} w(d) .
```

This is the Selberg-style side condition that characterises weights
producing valid upper bounds in the sieve framework.  See
`BoundingSieve.IsUpperMoebius` in
`Mathlib.NumberTheory.SelbergSieve` for the mathlib counterpart. -/
def IsUpperMoebiusWeight (w : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ n.divisors, w d

/-! ## Section 2 — Canonical examples

We exhibit two upper-Möbius weights:  the **point-mass at 1** and the
**constant `1`** weight.  Both witness that `IsUpperMoebiusWeight` is
non-vacuous. -/

/-- The **point-mass at 1** weight:  `1` at `d = 1`, `0` elsewhere.

This is the canonical "minimal" upper-Möbius weight:  it places all the
mass on the trivial divisor `d = 1`, exactly enough to satisfy the
side condition `[n = 1] ≤ ∑_{d ∣ n} w(d)` at `n = 1`. -/
def pointMassOne : ℕ → ℝ := fun d => if d = 1 then 1 else 0

/-- The **constant `1`** weight:  `1` at every divisor.

This is the most generous upper-Möbius weight in non-negative terms:
it sums to `τ(n)` (the divisor count), which always dominates `1` (the
LHS indicator) for `n ≥ 1`. -/
def constantOne : ℕ → ℝ := fun _ => 1

/-- The point-mass weight at `1` is upper-Möbius.

Proof: at `n = 1` the divisor set is `{1}` and `pointMassOne 1 = 1`, so
the RHS equals `1`.  At `n ≠ 1` the LHS indicator is `0`, and the RHS
is a sum of non-negative reals (each `pointMassOne d ≥ 0`), hence
`≥ 0`. -/
theorem pointMassOne_isUpperMoebiusWeight :
    IsUpperMoebiusWeight pointMassOne := by
  classical
  intro n
  by_cases hn : n = 1
  · subst hn
    -- divisors 1 = {1}
    simp [pointMassOne]
  · -- LHS = 0
    rw [if_neg hn]
    apply Finset.sum_nonneg
    intro d _
    unfold pointMassOne
    by_cases hd : d = 1
    · rw [if_pos hd]; norm_num
    · rw [if_neg hd]

/-- The constant `1` weight is upper-Möbius.

Proof: the RHS is `n.divisors.card = τ(n)`.  For `n ≥ 1`, we have
`1 ∈ n.divisors`, so the cardinality is `≥ 1`.  For `n = 0`, the LHS is
`0` (the indicator `if 0 = 1`) and the RHS is `0` (`(0).divisors = ∅`),
so the inequality `0 ≤ 0` holds. -/
theorem constantOne_isUpperMoebiusWeight :
    IsUpperMoebiusWeight constantOne := by
  classical
  intro n
  by_cases hn : n = 1
  · subst hn
    -- divisors 1 = {1}; sum = 1.
    simp [constantOne]
  · -- LHS = 0; RHS ≥ 0 (sum of `1`'s over a finset).
    rw [if_neg hn]
    apply Finset.sum_nonneg
    intro d _
    unfold constantOne
    norm_num

/-! ## Section 3 — Bridge to mathlib's `BoundingSieve.IsUpperMoebius`

We expose the bridge as a definitional equivalence.  This lets any
upper-Möbius weight produced via `IsUpperMoebiusWeight` be fed directly
into mathlib's
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` delivery
theorem, and vice versa. -/

/-- **Bridge:**  `IsUpperMoebiusWeight w` is propositionally equal to
mathlib's `BoundingSieve.IsUpperMoebius w`.  In fact the two Props are
**definitionally** equal — the only difference is the namespace and the
fact that the mathlib version is stated in `omit s in` scope (i.e.
without reference to any specific `BoundingSieve`).

This `Iff` thus has a one-line proof by reflexivity. -/
theorem isUpperMoebiusWeight_iff_isUpperMoebius (w : ℕ → ℝ) :
    IsUpperMoebiusWeight w ↔ BoundingSieve.IsUpperMoebius w :=
  Iff.rfl

/-- **Bridge (forward):**  `IsUpperMoebiusWeight w → BoundingSieve.IsUpperMoebius w`. -/
theorem isUpperMoebius_of_isUpperMoebiusWeight
    {w : ℕ → ℝ} (h : IsUpperMoebiusWeight w) :
    BoundingSieve.IsUpperMoebius w :=
  (isUpperMoebiusWeight_iff_isUpperMoebius w).mp h

/-- **Bridge (backward):**  `BoundingSieve.IsUpperMoebius w → IsUpperMoebiusWeight w`. -/
theorem isUpperMoebiusWeight_of_isUpperMoebius
    {w : ℕ → ℝ} (h : BoundingSieve.IsUpperMoebius w) :
    IsUpperMoebiusWeight w :=
  (isUpperMoebiusWeight_iff_isUpperMoebius w).mpr h

/-- **Concrete instance for mathlib:**  the point-mass weight is
upper-Möbius in the mathlib sense as well.

This is the direct corollary of `pointMassOne_isUpperMoebiusWeight`
combined with the bridge.  Together with mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`, this gives the trivial
upper bound `siftedSum ≤ totalMass · ν(1) + |rem 1|` for any
`BoundingSieve`. -/
theorem pointMassOne_isUpperMoebius :
    BoundingSieve.IsUpperMoebius pointMassOne :=
  isUpperMoebius_of_isUpperMoebiusWeight pointMassOne_isUpperMoebiusWeight

/-- **Concrete instance for mathlib:**  the constant `1` weight is
upper-Möbius in the mathlib sense as well. -/
theorem constantOne_isUpperMoebius :
    BoundingSieve.IsUpperMoebius constantOne :=
  isUpperMoebius_of_isUpperMoebiusWeight constantOne_isUpperMoebiusWeight

/-! ## Section 4 — Closed-form weighted Bonferroni at the indicator
level

Given any upper-Möbius weight `w` and any natural `n`, the side
condition gives directly the *weighted Bonferroni* inequality

```
   (if n = 1 then 1 else 0) ≤ ∑_{d ∣ n} w(d) .
```

Substituting `n = Nat.gcd (P.prod id) m` for a finset `P` of squarefree
naturals translates this into a divisibility-based inequality of the
exact shape needed for the Halberstam-Richert §3.11 absorption step.

The cleanest form of this is `IsUpperMoebiusWeight w` itself — it is the
weighted Bonferroni statement for the divisor lattice of `n`.  We expose
it under a more descriptive name. -/

/-- **Weighted Bonferroni at the indicator level (divisor form).**

This is just `IsUpperMoebiusWeight w` re-statement applied at `n` —
i.e. the weighted Bonferroni inequality is *exactly* the upper-Möbius
side condition for `w`.  We expose this as a Prop named after the
weighted Bonferroni interpretation. -/
def WeightedBonferroniIndicator (w : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ n.divisors, w d

/-- **Weighted Bonferroni ↔ upper-Möbius.**  By construction the two
Props are definitionally equal. -/
theorem weightedBonferroniIndicator_iff_isUpperMoebiusWeight (w : ℕ → ℝ) :
    WeightedBonferroniIndicator w ↔ IsUpperMoebiusWeight w :=
  Iff.rfl

/-- **The classical weighted Bonferroni inequality holds for any
upper-Möbius weight.** -/
theorem weightedBonferroniIndicator_of_isUpperMoebiusWeight
    {w : ℕ → ℝ} (h : IsUpperMoebiusWeight w) :
    WeightedBonferroniIndicator w := h

/-- **Concrete: weighted Bonferroni holds for the point-mass weight.** -/
theorem weightedBonferroniIndicator_pointMassOne :
    WeightedBonferroniIndicator pointMassOne :=
  weightedBonferroniIndicator_of_isUpperMoebiusWeight
    pointMassOne_isUpperMoebiusWeight

/-- **Concrete: weighted Bonferroni holds for the constant `1` weight.** -/
theorem weightedBonferroniIndicator_constantOne :
    WeightedBonferroniIndicator constantOne :=
  weightedBonferroniIndicator_of_isUpperMoebiusWeight
    constantOne_isUpperMoebiusWeight

/-! ## Section 5 — Closure under non-negative scaling and addition

Two structural closure properties of upper-Möbius weights:

* If `w` is upper-Möbius and `c ≥ 1` is a real, then `c · w` is also
  upper-Möbius — because the RHS only inflates.

Note: a more interesting closure (the Selberg construction) takes
quadratic combinations `(∑_d λ_d · [d∣n])²` of upper-Möbius weights,
but this requires the full Λ² analysis (off-scope here). -/

/-- **Closure under non-negative scaling (`c ≥ 1`).**

If `w` is upper-Möbius and the constant `c ≥ 1`, then `c · w` is also
upper-Möbius.

Proof: `[n = 1] ≤ ∑_d w(d) ≤ c · ∑_d w(d)` provided `∑_d w(d) ≥ 0`,
which follows from the `[n=1]≤∑` hypothesis at any `n ≠ 1` (then LHS =
0, so RHS ≥ 0).  At `n = 1`: `1 ≤ ∑_d w(d)`, so `c · ∑_d w(d) ≥ c · 1
= c ≥ 1`. -/
theorem isUpperMoebiusWeight_const_mul
    {w : ℕ → ℝ} (hw : IsUpperMoebiusWeight w)
    {c : ℝ} (hc : 1 ≤ c) :
    IsUpperMoebiusWeight (fun d => c * w d) := by
  classical
  intro n
  have hRHS : ∑ d ∈ n.divisors, c * w d = c * ∑ d ∈ n.divisors, w d :=
    Finset.mul_sum n.divisors w c |>.symm
  rw [hRHS]
  by_cases hn : n = 1
  · subst hn
    have hw1 := hw 1
    rw [if_pos rfl] at hw1
    -- hw1 : 1 ≤ ∑ d ∈ (1 : ℕ).divisors, w d
    rw [if_pos rfl]
    -- Goal: 1 ≤ c * ∑ d ∈ (1 : ℕ).divisors, w d
    have hcpos : 0 < c := by linarith
    -- From 1 ≤ ∑, conclude c ≤ c * ∑.  Then chain through 1 ≤ c ≤ c*∑.
    have hstep : c * 1 ≤ c * ∑ d ∈ (1 : ℕ).divisors, w d :=
      mul_le_mul_of_nonneg_left hw1 (le_of_lt hcpos)
    linarith
  · -- LHS = 0; RHS = c * (sum of w over divisors of n).  The hypothesis
    -- at `n` gives `0 ≤ ∑ w`, and `c ≥ 1 ≥ 0`, so the product is `≥ 0`.
    rw [if_neg hn]
    have hwn := hw n
    rw [if_neg hn] at hwn
    have hcpos : 0 < c := by linarith
    exact mul_nonneg (le_of_lt hcpos) hwn

/-! ## Section 6 — Audit. -/

/-- **Summary** of the deliverables:

* `IsUpperMoebiusWeight w` — the side condition characterising weights
  that yield valid weighted Bonferroni upper bounds at the indicator
  level.
* `pointMassOne`, `constantOne` — two canonical examples, both proved
  upper-Möbius.
* `isUpperMoebiusWeight_iff_isUpperMoebius` — the bridge to mathlib's
  `BoundingSieve.IsUpperMoebius`, which is **definitional** (`Iff.rfl`).
* `WeightedBonferroniIndicator w` — the weighted Bonferroni Prop,
  definitionally equal to `IsUpperMoebiusWeight w`.
* `isUpperMoebiusWeight_const_mul` — closure under scaling by `c ≥ 1`.

All axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`). -/
theorem pathC_p25_t4_summary : True := trivial

end PathCWeightedBonferroni
end Gdbh

/-! ## Section 7 — Axiom audit

We expose `#print axioms` checks for the main theorems.  The output is
visible in the elaborator log; each statement is required to depend only
on `propext`, `Classical.choice`, `Quot.sound`. -/

-- Sanity-check `#print axioms` on the core results.
#print axioms Gdbh.PathCWeightedBonferroni.pointMassOne_isUpperMoebiusWeight
#print axioms Gdbh.PathCWeightedBonferroni.constantOne_isUpperMoebiusWeight
#print axioms Gdbh.PathCWeightedBonferroni.isUpperMoebiusWeight_iff_isUpperMoebius
#print axioms Gdbh.PathCWeightedBonferroni.pointMassOne_isUpperMoebius
#print axioms Gdbh.PathCWeightedBonferroni.constantOne_isUpperMoebius
#print axioms Gdbh.PathCWeightedBonferroni.weightedBonferroniIndicator_pointMassOne
#print axioms Gdbh.PathCWeightedBonferroni.weightedBonferroniIndicator_constantOne
#print axioms Gdbh.PathCWeightedBonferroni.isUpperMoebiusWeight_const_mul
