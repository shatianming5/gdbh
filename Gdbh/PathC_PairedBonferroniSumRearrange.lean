/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T3 (Phase 19 / Path C — Paired Bonferroni sum rearrangement,
the combinatorial Kernel A piece for the Brun-Goldbach pair sift).
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Gdbh.PathC_PairedBrunBonferroni
import Gdbh.PathC_GoldbachPairCRTCount

/-!
# Path C — P19-T3: Paired Bonferroni sum rearrangement (Kernel A)

This file is the **P19-T3 deliverable** in Phase 19 (Path C closure).  Its
target is the *paired Bonferroni sum rearrangement* identity, the
combinatorial Kernel A piece that, together with the paired CRT counting
kernel `Gdbh.PathCGoldbachPairCRTCount.goldbachPairCRTCount_holds`, closes
the Brun-Goldbach sieve at the pair level.

## Mathematical content

For a finite set `P` of primes, a truncation depth `k`, and a target
`n ≥ 2`, define the (truncated) Bonferroni indicator function

```
   S(m, k) := ∑_{d ⊆ P, |d| ≤ k} μ(d.prod) · 1{d.prod ∣ m} .
```

Paired Bonferroni for the Goldbach sift bounds

```
   goldbachSiftedPair n z  ≤  ∑_{m=1}^{n-1} S(m, k) · S(n - m, k) .
```

The rearrangement identity (this file) rewrites the RHS as a double sum
over `(d₁, d₂)` of subsets of `P`:

```
   ∑_{m=1}^{n-1} S(m, k) · S(n - m, k)
     = ∑_{d₁, d₂}  μ(d₁.prod) · μ(d₂.prod) · #{m ∈ [1, n-1] :
                                                d₁.prod ∣ m ∧ d₂.prod ∣ (n - m)} .
```

Combined with `goldbachPairCRTCount_holds`, this reduces the Brun-Goldbach
bound to a controlled finite sum.

## Proof strategy

The identity is **purely combinatorial** — no number theory is used
beyond what's encoded in the indicator functions.  The proof composes:

1. `Finset.sum_mul_sum` — distribute the product over the two divisor
   sums.
2. `Finset.sum_comm` — swap the `m` sum past the `d₁`, `d₂` sums.
3. `Finset.mul_sum` — pull `μ(d₁.prod) · μ(d₂.prod)` out of the
   inner `m` sum.
4. Pointwise simplification: the product of two indicators
   `1{d₁.prod ∣ m} · 1{d₂.prod ∣ n-m}` equals the indicator of the
   conjunction.
5. `Finset.sum_boole` (or `Finset.natCast_card_filter`) — recognise
   `∑ m, 1{P m}` as a cardinality cast.

This is a one-page tactic proof.  No `sorry`, no `axiom`, no `admit`.

## Axiom budget

The only axioms transitively used are `Classical.choice`, `Quot.sound`,
and `propext`.

## Theorem names exported

* `Gdbh.PathCPairedBonferroniSumRearrange.PairedBonferroniSumRearrange`
  — the named Prop.
* `Gdbh.PathCPairedBonferroniSumRearrange.pairedBonferroniSumRearrange_holds`
  — closure of the Prop.
-/

namespace Gdbh
namespace PathCPairedBonferroniSumRearrange

open scoped BigOperators
open Finset

/-- **Paired Bonferroni sum rearrangement.**

For a finite set `P` of primes, a truncation depth `k`, and a target
`n ≥ 2`, the sum over `m ∈ [1, n-1]` of the product
`S(m, k) · S(n - m, k)` — where `S(m, k) = ∑_{d ⊆ P, |d| ≤ k} μ(d.prod)
· 1{d.prod ∣ m}` — equals the double sum

```
  ∑_{d₁, d₂ ⊆ P, |d_i| ≤ k}  μ(d₁.prod) · μ(d₂.prod)
                                · #{m ∈ [1, n-1] : d₁.prod ∣ m ∧ d₂.prod ∣ (n - m)} .
```

This is a clean Finset rearrangement identity.  It is purely
combinatorial (no Bonferroni inequalities are used here); the Bonferroni
inequalities apply to bound `goldbachSiftedPair n z` by the LHS. -/
def PairedBonferroniSumRearrange : Prop :=
  ∀ (P : Finset ℕ) (n k : ℕ),
    2 ≤ n →
    (∀ p ∈ P, Nat.Prime p) →
    (∑ m ∈ Finset.Icc 1 (n - 1),
      (∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
         (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
           (if (d₁.prod id) ∣ m then (1 : ℝ) else 0)) *
      (∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
         (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
           (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0)))
    = ∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
        ∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
          (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
            (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
            ((Finset.Icc 1 (n - 1)).filter
              (fun m => (d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m))).card

/-- **Closure of `PairedBonferroniSumRearrange`.**

Strategy.  Pure Finset rearrangement:

* `Finset.sum_mul_sum`     — distribute `(∑_{d₁}) · (∑_{d₂})` as
  `∑_{d₁} ∑_{d₂} (…)`.
* `Finset.sum_comm`        — swap the `m` sum past the `(d₁, d₂)` sums.
* `Finset.mul_sum`         — factor `μ(d₁.prod) · μ(d₂.prod)` out of the
  inner `m` sum.
* Pointwise indicator simplification — the product of two `if`
  indicators is the `if` of the conjunction.
* `Finset.sum_boole` (resp. `Finset.natCast_card_filter`) — recognise
  `∑ 1{P m}` as `#{m | P m}`.

The hypotheses `2 ≤ n` and `(∀ p ∈ P, Nat.Prime p)` are *not* used in the
rearrangement (the identity holds for arbitrary `P` and arbitrary `n`);
we keep them in the signature to match the upstream Brun-Goldbach
context. -/
theorem pairedBonferroniSumRearrange_holds : PairedBonferroniSumRearrange := by
  classical
  intro P n k _hn _hP
  -- Notation shorthand.
  set F : Finset (Finset ℕ) := P.powerset.filter (fun d => d.card ≤ k) with hF_def
  -- Step 1: distribute the product of inner sums on the LHS,
  --   `(∑ d₁, A d₁ m) · (∑ d₂, B d₂ m) = ∑ d₁, ∑ d₂, A d₁ m · B d₂ m`.
  have hLHS_dist :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        (∑ d₁ ∈ F,
           (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
             (if (d₁.prod id) ∣ m then (1 : ℝ) else 0)) *
        (∑ d₂ ∈ F,
           (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
             (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0)))
      = ∑ m ∈ Finset.Icc 1 (n - 1),
          ∑ d₁ ∈ F,
            ∑ d₂ ∈ F,
              ((ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
                  (if (d₁.prod id) ∣ m then (1 : ℝ) else 0)) *
              ((ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
                  (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro m _hm
    exact Finset.sum_mul_sum _ _ _ _
  rw [hLHS_dist]
  -- Step 2: swap the outer `m` sum past the `d₁` sum — `∑ m ∑ d₁ … = ∑ d₁ ∑ m …`.
  rw [Finset.sum_comm]
  -- For each fixed `d₁`, swap the inner `m` and `d₂` sums.
  refine Finset.sum_congr rfl ?_
  intro d₁ _hd₁
  rw [Finset.sum_comm]
  -- For each fixed `d₂`, simplify the inner `m` sum.
  refine Finset.sum_congr rfl ?_
  intro d₂ _hd₂
  -- Abbreviate the Möbius values.
  set a : ℝ := (ArithmeticFunction.moebius (d₁.prod id) : ℝ) with ha_def
  set b : ℝ := (ArithmeticFunction.moebius (d₂.prod id) : ℝ) with hb_def
  -- Step 3: rewrite each summand `(a · 1{D₁ ∣ m}) · (b · 1{D₂ ∣ n-m})`
  --                       as `a · b · 1{D₁ ∣ m ∧ D₂ ∣ n-m}`.
  have hinner_pt :
      ∀ m ∈ Finset.Icc 1 (n - 1),
        (a * (if (d₁.prod id) ∣ m then (1 : ℝ) else 0)) *
          (b * (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0))
        = a * b *
            (if ((d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m))
              then (1 : ℝ) else 0) := by
    intro m _hm
    by_cases h₁ : (d₁.prod id) ∣ m
    · by_cases h₂ : (d₂.prod id) ∣ (n - m)
      · have hand : (d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m) := ⟨h₁, h₂⟩
        rw [if_pos h₁, if_pos h₂, if_pos hand]
        ring
      · have hnot : ¬ ((d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m)) := by
          intro h; exact h₂ h.2
        rw [if_pos h₁, if_neg h₂, if_neg hnot]
        ring
    · have hnot : ¬ ((d₁.prod id) ∣ m ∧ (d₂.prod id) ∣ (n - m)) := by
        intro h; exact h₁ h.1
      rw [if_neg h₁, if_neg hnot]
      ring
  rw [Finset.sum_congr rfl hinner_pt]
  -- Step 4: factor `a * b` out of the `m` sum, then recognise the remaining
  -- `∑ m, 1{P m}` as the cast cardinality of the filtered set.
  rw [← Finset.mul_sum]
  -- The boolean sum equals the cardinality cast (in ℝ).
  -- `Finset.sum_boole` : `(∑ x ∈ s, if p x then 1 else 0 : R) = (s.filter p).card`.
  rw [Finset.sum_boole]
  -- Goal now matches the RHS form.

end PathCPairedBonferroniSumRearrange
end Gdbh
