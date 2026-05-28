/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T40 (Phase 19 / Path C — Möbius partial-sum bound on
        subsets:  fine control of the partial sums of
        `μ(D.prod) · 2^|D|/D.prod` over truncated subsets `Q ⊆ P`,
        for the Brun-Bonferroni paired sift.)
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Gdbh.PathC_MoebiusInversionRoute
import Gdbh.PathC_BonferroniTailKernel

/-!
# Path C — P19-T40: Möbius partial sum bound on subsets

This file delivers a **fine partial-sum bound** for the alternating
Möbius-weighted density sum
```
   S(Q) := ∑_{D ⊆ Q} μ(D.prod id) · 2^|D| / D.prod id
```
over an arbitrary subset `Q ⊆ P` of a `Finset` of primes `P` (each
`≥ 3`).  Two complementary results are proved:

* **`moebius_euler_product_over_subset`** — the **untruncated**
  identity:
  ```
     S(Q) = ∏_{p ∈ Q} (1 - 2/p) .
  ```
  This is the *subset-form* generalisation of the closed P19-T28
  identity `paired_eulerProduct_moebius_form` (which handles `Q = P`).
  The generalisation is by **direct application** of the closed identity
  to `Q` (viewed as its own `Finset` of primes, with primality inherited
  from `P` via the subset hypothesis).

* **`moebius_truncated_partial_sum_bonferroni`** — the **Bonferroni-style**
  partial-sum equation:
  ```
    |∑_{D ⊆ P, |D| ≤ k} bonferroniTerm D - ∏_{p ∈ P} (1 - 2/p)|
       ≤ ∑_{D ⊆ P, k < |D|} (2/3)^|D|  .
  ```
  Here `bonferroniTerm D = (-1)^|D| · 2^|D|/D.prod = μ(D.prod) · 2^|D|/D.prod`
  on the primality-on-`P` domain.  This decomposes the full Euler product
  into a **truncated main term** plus a **Bonferroni-controlled tail**.

The two results together give the **Bonferroni-paired-sift fine bound**
infrastructure needed for the truncated subset analysis:  for any
`Q ⊆ P`, the subset partial sum has the Euler-product closed form, and
the truncated partial sum over `P` has the Bonferroni tail bound.

## Mathematical content (honest assessment)

* The subset-Euler-product identity `moebius_euler_product_over_subset`
  is a **routine corollary** of `paired_eulerProduct_moebius_form`,
  since the underlying combinatorial identity
  `∏ (1 + a_p) = ∑_{D ⊆ Q} ∏_{p ∈ D} a_p` is intrinsically over the
  *index set Q* without any reference to a larger ambient set `P`.

* The Bonferroni-tail bound `moebius_truncated_partial_sum_bonferroni`
  is a **direct combination** of the two existing P19-T28 (Möbius-form
  identity) and P19-T19 (Bonferroni triangle inequality + `(2/3)^|d|`
  bound) closures.  No new combinatorial idea is introduced.

* **Hypothesis on `Q`**:  We require *only* `Q ⊆ P` and the primality
  hypothesis on `P` (each `p ∈ P` is prime and `≥ 3`).  No additional
  `Squarefree` hypothesis on `Q` is needed:  squarefreeness of
  `D.prod id` for `D ⊆ Q ⊆ P` follows automatically from `P`'s primes
  being distinct (as elements of a `Finset`, which is by construction
  a finite set of distinct values).

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom budget: only `Classical.choice`, `Quot.sound`, `propext`.
* File-write rule: only this new file is created.

## References

* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press 1974, §2.
* mathlib4 v4.29.1,
  `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`.
* In-project:
  - `Gdbh.PathCMoebiusInversionRoute.paired_eulerProduct_moebius_form`
    (P19-T28, untruncated Möbius-form Euler-product identity).
  - `Gdbh.PathCBonferroniTailKernel.bonferroniTruncationTail_two_thirds_pow_form`
    (P19-T19, Bonferroni truncation tail bound).
-/

namespace Gdbh
namespace PathCMoebiusPartialSumBound

open scoped BigOperators
open Finset

/-! ## §1 — Subset-form Möbius-Euler product identity

We prove the identity
```
   ∑_{D ⊆ Q} μ(D.prod id) · 2^|D| / D.prod id  =  ∏_{p ∈ Q} (1 - 2/p)
```
for any subset `Q ⊆ P` of a `Finset` of primes `P` (each `≥ 3`).

Strategy:  apply the **closed** P19-T28 identity
`paired_eulerProduct_moebius_form` to `Q`, using the inherited
primality hypothesis `∀ p ∈ Q, Nat.Prime p`.  No new combinatorial work
is needed beyond observing that the underlying identity is intrinsically
parameterised by the *index set*, not by any ambient larger set.
-/

/-- **Möbius-form Euler product identity over a subset.**

For any `Finset` of primes `P` with each prime `≥ 3`, and any
subset `Q ⊆ P`, the alternating Möbius-weighted density sum over the
powerset of `Q` equals the Euler product
`∏_{p ∈ Q} (1 - 2/p)`.

This is the **subset-form generalisation** of
`Gdbh.PathCMoebiusInversionRoute.paired_eulerProduct_moebius_form`:
that theorem handles `Q = P` exactly, and we re-apply it to `Q`
(using inherited primality) to obtain the subset version. -/
theorem moebius_euler_product_over_subset
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p)
    (Q : Finset ℕ) (hQ : Q ⊆ P) :
    ∑ D ∈ Q.powerset, (((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ) *
                        (2 : ℝ) ^ D.card / ((D.prod id : ℕ) : ℝ))
      = ∏ p ∈ Q, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
  classical
  -- Inherit primality on Q from primality on P via the subset hypothesis.
  have hQ_primes : ∀ p ∈ Q, Nat.Prime p := fun p hp => (hP p (hQ hp)).1
  -- Apply the closed P19-T28 identity to Q (viewed as its own Finset of primes).
  have hMoeb :=
    Gdbh.PathCMoebiusInversionRoute.paired_eulerProduct_moebius_form Q hQ_primes
  -- The identity reads `∏ p ∈ Q, (1 - 2/p) = ∑ D ∈ Q.powerset, ...`; reverse.
  exact hMoeb.symm

/-! ## §2 — Bonferroni truncation tail (re-export and combination)

We combine the closed P19-T28 untruncated identity with the closed
P19-T19 Bonferroni tail bound to deliver a *combined* Bonferroni-style
inequality:

```
  |∑_{D ⊆ P, |D| ≤ k} μ(D.prod) · 2^|D|/D.prod  -  ∏_{p ∈ P} (1 - 2/p)|
     ≤ ∑_{D ⊆ P, k < |D|} (2/3)^|D| .
```

This is the **fine partial-sum bound**:  the truncated partial sum is
**equal to the Euler product up to a tail** that is **explicitly
controlled** by the Bonferroni `(2/3)^|D|` estimate.

This inequality is the form consumed by downstream Stirling-type
upper bounds on `∑_{|D|=ℓ}` over the truncation regime. -/

/-- **Bonferroni-paired Möbius partial-sum bound** (the main P19-T40
deliverable).

For any `Finset` of primes `P` with each prime `≥ 3`, and any truncation
depth `k`,
```
  |  ∑_{D ⊆ P, |D| ≤ k}  μ(D.prod) · 2^|D|/D.prod  -  ∏_{p ∈ P} (1 - 2/p)  |
   ≤  ∑_{D ⊆ P, k < |D|}  (2/3)^|D|  .
```

Proof sketch:  the absolute value of the difference between the
truncated and full Möbius sums is bounded by the Bonferroni tail
(P19-T19); the full Möbius sum equals the Euler product (P19-T28).
Combining gives the bound. -/
theorem moebius_truncated_partial_sum_bonferroni
    (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) :
    |(∑ D ∈ P.powerset.filter (fun D => D.card ≤ k),
        Gdbh.PathCBonferroniTailKernel.bonferroniTerm D) -
       (∏ p ∈ P, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))|
    ≤ ∑ D ∈ P.powerset.filter (fun D => k < D.card),
        (2 / 3 : ℝ) ^ D.card := by
  classical
  -- Hypotheses for downstream invocations.
  have hP_primes : ∀ p ∈ P, Nat.Prime p := fun p hp => (hP p hp).1
  -- Step 1: the full Möbius sum equals the Euler product (P19-T28).
  have hEuler :
      (∏ p ∈ P, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))
        = ∑ D ∈ P.powerset,
            (((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
              * (2 : ℝ) ^ D.card / ((D.prod id : ℕ) : ℝ)) :=
    Gdbh.PathCMoebiusInversionRoute.paired_eulerProduct_moebius_form P hP_primes
  -- Step 2: identify `bonferroniTerm D` with the Möbius-form summand for
  -- each `D ⊆ P` (under the primality hypothesis on `P`).
  -- For each D in the powerset, μ(D.prod) = (-1)^|D| as reals (by the
  -- distinct-primes hypothesis on D ⊆ P), so:
  --   μ(D.prod) · 2^|D| / D.prod = (-1)^|D| · 2^|D| / D.prod = bonferroniTerm D.
  have hSumEq :
      (∑ D ∈ P.powerset,
          (((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
              * (2 : ℝ) ^ D.card / ((D.prod id : ℕ) : ℝ)))
        = ∑ D ∈ P.powerset, Gdbh.PathCBonferroniTailKernel.bonferroniTerm D := by
    refine Finset.sum_congr rfl ?_
    intro D hD
    have hD_sub : D ⊆ P := Finset.mem_powerset.mp hD
    have hD_primes : ∀ p ∈ D, Nat.Prime p := fun p hp => hP_primes p (hD_sub hp)
    have hμ : ((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
                = (-1 : ℝ) ^ D.card :=
      Gdbh.PathCMoebiusInversionRoute.moebius_prod_distinct_primes hD_primes
    -- Substitute and unfold `bonferroniTerm`.
    unfold Gdbh.PathCBonferroniTailKernel.bonferroniTerm
    rw [hμ]
  -- Step 3: from `hEuler` and `hSumEq`, the Euler product equals the full
  -- `bonferroniTerm` sum.
  have hEulerBon :
      (∏ p ∈ P, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))
        = ∑ D ∈ P.powerset, Gdbh.PathCBonferroniTailKernel.bonferroniTerm D := by
    rw [hEuler, hSumEq]
  -- Step 4: rewrite the goal using `hEulerBon` to replace the Euler product
  -- with the full sum, then apply the P19-T19 Bonferroni triangle inequality.
  rw [hEulerBon]
  -- Goal:  |truncSum - fullSum| ≤ tail .
  -- The triangle bound gives `|fullSum - truncSum| ≤ tail`; rewrite via
  -- `|x - y| = |y - x|`.
  have hTail :=
    Gdbh.PathCBonferroniTailKernel.bonferroniTruncationTail_two_thirds_pow_form P k hP
  -- hTail :  |fullSum - truncSum|  ≤  tail .
  -- Rewrite the absolute value in the goal:
  rw [abs_sub_comm]
  exact hTail

/-! ## §3 — Subset-form Bonferroni partial-sum bound (Q ⊆ P)

Combining §1 (subset Euler product identity over Q) with §2 (Bonferroni
tail bound, applied to Q in place of P), we obtain the subset version
of the fine partial-sum bound:

```
  |∑_{D ⊆ Q, |D| ≤ k} μ(D.prod) · 2^|D|/D.prod  -  ∏_{p ∈ Q} (1 - 2/p)|
     ≤ ∑_{D ⊆ Q, k < |D|} (2/3)^|D| .
```

This is the **most general form** of the partial-sum bound:  any
truncated partial sum over any subset `Q ⊆ P` is approximated by the
Euler product over `Q`, up to a Bonferroni-controlled tail. -/

/-- **Subset-form Bonferroni partial-sum bound.**  For any subset
`Q ⊆ P` of a `Finset` of primes `P` (each `≥ 3`) and any truncation
depth `k`:
```
  |  ∑_{D ⊆ Q, |D| ≤ k}  μ(D.prod) · 2^|D|/D.prod
     -  ∏_{p ∈ Q} (1 - 2/p)  |
   ≤  ∑_{D ⊆ Q, k < |D|}  (2/3)^|D|  .
```

This is obtained by applying `moebius_truncated_partial_sum_bonferroni`
to `Q` (with the inherited primality hypothesis on `Q`). -/
theorem moebius_truncated_partial_sum_bonferroni_subset
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p)
    (Q : Finset ℕ) (hQ : Q ⊆ P) (k : ℕ) :
    |(∑ D ∈ Q.powerset.filter (fun D => D.card ≤ k),
        Gdbh.PathCBonferroniTailKernel.bonferroniTerm D) -
       (∏ p ∈ Q, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))|
    ≤ ∑ D ∈ Q.powerset.filter (fun D => k < D.card),
        (2 / 3 : ℝ) ^ D.card := by
  classical
  -- Inherit hypothesis on Q.
  have hQ_hyp : ∀ p ∈ Q, Nat.Prime p ∧ 3 ≤ p := fun p hp => hP p (hQ hp)
  -- Direct application of the P-form to Q.
  exact moebius_truncated_partial_sum_bonferroni Q k hQ_hyp

/-! ## §4 — `μ(D.prod) · 2^|D|/D.prod` form (re-expression of the §3 bound)

For clarity, we also state the bound in **explicit Möbius-summand
form** (rather than `bonferroniTerm`), to emphasise the connection with
`moebius_euler_product_over_subset` of §1. -/

/-- **Subset-form Bonferroni partial-sum bound — Möbius-summand
notation.**

```
  |  ∑_{D ⊆ Q, |D| ≤ k}  μ(D.prod) · 2^|D|/D.prod
     -  ∏_{p ∈ Q} (1 - 2/p)  |
   ≤  ∑_{D ⊆ Q, k < |D|}  (2/3)^|D|  .
```
-/
theorem moebius_truncated_partial_sum_bonferroni_subset_explicit
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p)
    (Q : Finset ℕ) (hQ : Q ⊆ P) (k : ℕ) :
    |(∑ D ∈ Q.powerset.filter (fun D => D.card ≤ k),
        (((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
              * (2 : ℝ) ^ D.card / ((D.prod id : ℕ) : ℝ))) -
       (∏ p ∈ Q, ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))|
    ≤ ∑ D ∈ Q.powerset.filter (fun D => k < D.card),
        (2 / 3 : ℝ) ^ D.card := by
  classical
  -- Identify the two forms of the summand on the truncation range.
  have hQ_primes : ∀ p ∈ Q, Nat.Prime p := fun p hp => (hP p (hQ hp)).1
  have hRewrite :
      (∑ D ∈ Q.powerset.filter (fun D => D.card ≤ k),
          (((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
                * (2 : ℝ) ^ D.card / ((D.prod id : ℕ) : ℝ)))
        = ∑ D ∈ Q.powerset.filter (fun D => D.card ≤ k),
            Gdbh.PathCBonferroniTailKernel.bonferroniTerm D := by
    refine Finset.sum_congr rfl ?_
    intro D hD
    have hD_pow : D ∈ Q.powerset := (Finset.mem_filter.mp hD).1
    have hD_sub_Q : D ⊆ Q := Finset.mem_powerset.mp hD_pow
    have hD_primes : ∀ p ∈ D, Nat.Prime p := fun p hp => hQ_primes p (hD_sub_Q hp)
    have hμ : ((ArithmeticFunction.moebius (D.prod id) : ℤ) : ℝ)
                = (-1 : ℝ) ^ D.card :=
      Gdbh.PathCMoebiusInversionRoute.moebius_prod_distinct_primes hD_primes
    unfold Gdbh.PathCBonferroniTailKernel.bonferroniTerm
    rw [hμ]
  rw [hRewrite]
  exact moebius_truncated_partial_sum_bonferroni_subset P hP Q hQ k

/-! ## §5 — Summary / outcome classification

The deliverables of this file are:

1. `moebius_euler_product_over_subset` (§1):  the **untruncated** subset
   Euler product identity
   ```
     ∑_{D ⊆ Q} μ(D.prod) · 2^|D| / D.prod = ∏_{p ∈ Q} (1 - 2/p) .
   ```

2. `moebius_truncated_partial_sum_bonferroni` (§2):  the **full-P**
   Bonferroni-style partial-sum bound
   ```
     |truncSum_P,k - Euler_P| ≤ tail_P,k (in (2/3)^|d|) .
   ```

3. `moebius_truncated_partial_sum_bonferroni_subset` (§3):  the **subset**
   Bonferroni-style partial-sum bound
   ```
     |truncSum_Q,k - Euler_Q| ≤ tail_Q,k (in (2/3)^|d|) .
   ```

4. `moebius_truncated_partial_sum_bonferroni_subset_explicit` (§4):  same
   in explicit Möbius-summand notation.

**Axiom budget**: only `Classical.choice`, `Quot.sound`, `propext`.
No `sorry`, no `axiom`, no `admit`.

**Outcome classification** (per task spec):  **outcome (a)** — the
claimed bound is fully established.  The subset-form Euler product
identity, the full-P Bonferroni tail bound, and the subset-form
Bonferroni tail bound are all proved axiom-cleanly.

**Honest assessment**:  the subset-form Euler product identity §1 is
a *routine corollary* of the existing closed P19-T28 identity (since
the underlying combinatorial identity is intrinsically parameterised
by the index set).  The Bonferroni bounds §2 / §3 / §4 are *direct
combinations* of the existing closed P19-T28 (full identity) and
P19-T19 (Bonferroni tail) results;  no genuinely new combinatorial
work is introduced.  The novelty is in the *packaging*:  delivering the
explicit subset-form partial-sum bound as a single ready-to-use kernel
for downstream Brun-Bonferroni paired-sift assemblies.

**No additional hypothesis on Q is needed**:  squarefreeness of
`D.prod id` for `D ⊆ Q` follows from `Q ⊆ P` and `P`'s primes being
distinct (as elements of a `Finset` of primes).

**Files written**:  only `Gdbh/PathC_MoebiusPartialSumBound.lean`. -/
theorem pathC_p19_t40_summary : True := trivial

end PathCMoebiusPartialSumBound
end Gdbh
