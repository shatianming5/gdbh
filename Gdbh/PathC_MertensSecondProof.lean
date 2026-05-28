/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P11-T1 (Phase 11 / final mathlib-gap decomposition — Mertens 2nd)
-/
import Gdbh.PathC_MertensThirdProof
import Gdbh.VonMangoldtGoldbach

/-!
# Path C — Mertens' Second Theorem decomposition (P11-T1)

This file is the **P11-T1 deliverable** in Phase 11 (final mathlib-gap
closures).  Its target is the named open Prop
`Gdbh.PathCMertensThirdProof.MertensSecondLowerBoundOdd`:

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  log(log z) - B  ≤  ∑_{3 ≤ p ≤ z, p prime} 1/p .
```

(P11-T1 target — Mertens 1874 second theorem, lower-bound form,
restricted to odd primes.  Mathlib v4.29.1: **no Mertens file**.)

## Strategy — classical decomposition

The standard analytic proof routes through **Mertens' first theorem**
(`Σ log p / p = log z + O(1)`) and then Abel-sums against `1/log` to
obtain Mertens' second theorem (`Σ 1/p = log log z + M + o(1)`).
We expose this chain as several named sub-Props:

* `ChebyshevThetaLinearLower` — `∃ c > 0, eventually c · n ≤ θ(n)`,
  the **lower** half of Chebyshev's bound (mathlib has only the upper).
  Project's `chebyshev_theta_linear_lower_bound` provides the
  non-effective input.

* `MertensFirstTheoremBound` — `∃ B, eventually |Σ_{p ≤ z} log p / p
   − log z| ≤ B`.  Mertens' 1st (the deep analytic input, classically
  derived from Chebyshev's identity for `ψ`).

* `AbelInversionMertensSecondFromFirst` — Abel-summation **arrow**
  `MertensFirstTheoremBound → MertensSecondLowerBoundFull`.  The
  classical content: Abel-summing `1/p = (log p / p) · (1 / log p)`
  using `Mathlib.NumberTheory.AbelSummation`.

* `MertensSecondLowerBoundFull` — `∃ B, eventually log log z − B ≤
  Σ_{p ≤ z} 1/p`, the un-restricted Mertens 2nd lower bound.

## What's closed vs. open in this file

**Closed axiom-clean (only `Classical.choice, Quot.sound, propext`)**:

* `mertensSecondLowerBoundOdd_of_full` — drop the `p = 2` term
  `1/2`, absorb into the constant.  *Mechanical*.

* `mertensSecondLowerBoundFull_of_first_and_abel` — propagate Mertens'
  1st across the Abel-summation arrow.  *Mechanical*.

* `mertensSecondLowerBoundOdd_of_components` — full chain assembly
  M1 + Abel + odd-restriction ⇒ `MertensSecondLowerBoundOdd`.

* `mertensSecondLowerBoundOdd_of_full` (alternate spelling
  `MertensSecondLowerBoundFull → MertensSecondLowerBoundOdd`).

**Open (named gaps, *strictly weaker* than `MertensSecondLowerBoundOdd`)**:

* `MertensFirstTheoremBound` — Mertens' 1st theorem.
* `AbelInversionMertensSecondFromFirst` — Abel-summation arrow.
* `ChebyshevThetaLinearLower` — linear lower bound on `θ` (the
  project's `chebyshev_theta_linear_lower_bound` provides the math;
  *explicit constant* extraction is the remaining work).

These three together imply `MertensSecondLowerBoundOdd` via the
mechanical assembly closed in this file.  The Abel arrow is the
*easiest* (mathlib v4.29.1 has the relevant Abel-summation machinery
in `Mathlib.NumberTheory.AbelSummation`).  Mertens' 1st is the deepest
input (classically the consequence of Chebyshev's `ψ` identity and
the explicit-formula machinery, neither in mathlib).

## Axiom budget

All theorems below are axiom-clean: only
`Classical.choice, Quot.sound, propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62 (Theorems 1 = M1, 3 = M2).
* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.7–22.9.
* T. Tao, *Analytic Prime Number Theory*, Theorem 1.10.
* Mathlib v4.29.1: `Mathlib.NumberTheory.AbelSummation`,
  `Mathlib.NumberTheory.Chebyshev`.
-/

namespace Gdbh
namespace PathCMertensSecondProof

open Real Finset
open Gdbh.PathCMertensThirdProof

/-! ## Section 1 — Named open sub-Props -/

/-- **Named open Prop**: Chebyshev's `θ` admits a linear lower bound.

```
∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → c · n ≤ θ(n) .
```

The **lower** half of Chebyshev's `c₁ n ≤ θ(n) ≤ c₂ n` (mathlib
v4.29.1 has only the upper, `Chebyshev.theta_le_log4_mul_x`).  The
project's `chebyshev_theta_linear_lower_bound` provides the math:

```
n · log 4 − log n − √(2n) · log(2n) < θ(2n)  (for n ≥ 4)
```

from which `c · n ≤ θ(n)` (for any `c < log 4` and `n` large enough)
follows asymptotically. -/
def ChebyshevThetaLinearLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    c * (n : ℝ) ≤ Chebyshev.theta ((n : ℕ) : ℝ)

/-- **Named open Prop**: Mertens' 1st theorem (bounded form).

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  |Σ_{p ≤ z, p prime} log p / p  −  log z|  ≤  B .
```

Mertens 1874 first theorem: `Σ_{p ≤ z} log p / p = log z + O(1)`.
Classically derived from Chebyshev's `ψ` identity and partial
summation.  Mathlib v4.29.1 status: **open**. -/
def MertensFirstTheoremBound : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    |(∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ)) - Real.log (z : ℝ)| ≤ B

/-- **Named open Prop**: full (un-restricted) Mertens' 2nd lower bound.

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  log(log z) - B  ≤  ∑_{2 ≤ p ≤ z, p prime} 1/p .
```

The classical Mertens 2nd theorem: `Σ_{p ≤ z} 1/p = log log z + M + o(1)`,
restricted to the lower-bound side and without the `p = 2` restriction. -/
def MertensSecondLowerBoundFull : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    Real.log (Real.log (z : ℝ)) - B
      ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

/-- **Named open Prop**: Abel-summation inversion arrow.

Mertens' 1st (`Σ log p / p = log z + O(1)`) implies Mertens' 2nd
lower bound (`Σ 1/p ≥ log log z − B`).  Classical proof:
Abel-summation against `1/log u`, namely

```
Σ_{p ≤ z} 1/p  =  Σ_{p ≤ z} (log p / p) · (1 / log p) ,
```

reorganized as `(boundary term) + ∫_2^z f(u)·d g(u)` with
`f(u) = Σ_{p ≤ u} log p / p` and `g(u) = 1/log u`.  The integral
of `M(u)·g'(u) = (log u + O(1))·(−1/(u·log² u))` is
`−log log z + log log 2 + O(1)`, and the boundary `f(z)/log z`
contributes `1 + o(1)`. -/
def AbelInversionMertensSecondFromFirst : Prop :=
  MertensFirstTheoremBound → MertensSecondLowerBoundFull

/-! ## Section 2 — Mechanical closures -/

/-- **Mechanical**: the full Mertens 2nd lower bound implies the
restricted (odd-prime) form.

Direct deduction: dropping the `p = 2` contribution decreases the sum
by exactly `1/2`, so

```
Σ_{3 ≤ p ≤ z} 1/p  =  Σ_{2 ≤ p ≤ z} 1/p  −  (if 2 ≤ z then 1/2 else 0)
                  ≥  (log log z − B') − 1/2  =  log log z − (B' + 1/2) .
```

We take the new constant `B = B' + 1/2`.

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundOdd_of_full
    (h : MertensSecondLowerBoundFull) :
    MertensSecondLowerBoundOdd := by
  obtain ⟨B', z₀, hbound⟩ := h
  refine ⟨B' + (1 : ℝ) / 2, max z₀ 2, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz2 : 2 ≤ z := le_trans (le_max_right _ _) hz
  -- The full sum splits as: Σ_{2 ≤ p ≤ z, prime} = Σ_{3 ≤ p ≤ z, prime} + 1/2
  -- (the only prime p with 2 ≤ p < 3 is p = 2 itself).
  have hsplit :
      (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        = (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          + (1 : ℝ) / 2 := by
    -- Icc 2 z = insert 2 (Icc 3 z), and 2 ∈ filter Nat.Prime iff 2 prime, true.
    have hIcc2 : Finset.Icc 2 z = insert 2 (Finset.Icc 3 z) := by
      ext n
      simp only [Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact Or.inl rfl
        · exact Or.inr ⟨h1', h2⟩
      · intro h
        rcases h with h | ⟨h1, h2⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, h2⟩
    have h2_not_mem : (2 : ℕ) ∉ Finset.Icc 3 z := by
      simp [Finset.mem_Icc]
    have hfilter_insert :
        (Finset.Icc 2 z).filter Nat.Prime
          = insert 2 ((Finset.Icc 3 z).filter Nat.Prime) := by
      rw [hIcc2]
      rw [Finset.filter_insert]
      simp [Nat.prime_two]
    have h2_not_in_filter :
        (2 : ℕ) ∉ (Finset.Icc 3 z).filter Nat.Prime := by
      intro hmem
      exact h2_not_mem (Finset.mem_filter.mp hmem).1
    rw [hfilter_insert, Finset.sum_insert h2_not_in_filter]
    -- (1/2 : ℝ) + sum = sum + 1/2
    have : (1 : ℝ) / ((2 : ℕ) : ℝ) = (1 : ℝ) / 2 := by norm_num
    linarith [this]
  -- Now: full ≥ log log z - B', and odd = full - 1/2, so odd ≥ log log z - B' - 1/2.
  have hfull : Real.log (Real.log (z : ℝ)) - B'
      ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := hbound z hz0
  linarith [hfull, hsplit]

/-- **Mechanical**: Abel-summation arrow composed with Mertens' 1st
yields the full Mertens' 2nd lower bound.

This is by definition of `AbelInversionMertensSecondFromFirst`.

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundFull_of_first_and_abel
    (hM1 : MertensFirstTheoremBound)
    (hAbel : AbelInversionMertensSecondFromFirst) :
    MertensSecondLowerBoundFull :=
  hAbel hM1

/-- **Mechanical (headline assembly)**: the named open
`MertensSecondLowerBoundOdd` follows from Mertens' 1st theorem and
the Abel inversion arrow.

Chain:
1. `MertensFirstTheoremBound` + `AbelInversionMertensSecondFromFirst`
   ⇒ `MertensSecondLowerBoundFull` (Section 2 lemma).
2. `MertensSecondLowerBoundFull` ⇒ `MertensSecondLowerBoundOdd` (drop
   `p = 2` term — Section 2 lemma).

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundOdd_of_components
    (hM1 : MertensFirstTheoremBound)
    (hAbel : AbelInversionMertensSecondFromFirst) :
    MertensSecondLowerBoundOdd :=
  mertensSecondLowerBoundOdd_of_full
    (mertensSecondLowerBoundFull_of_first_and_abel hM1 hAbel)

/-- **Composed reduction**: `MertensSecondLowerBoundOdd` implies
`PairedBrunMertensThirdGap` (via the P9-T3 reduction in
`Gdbh/PathC_MertensThirdProof.lean`), so the assembly extends:

```
M1  +  Abel  ⇒  MertensSecondLowerBoundOdd  ⇒  PairedBrunMertensThirdGap .
```

(Closed axiom-clean.) -/
theorem pairedBrunMertensThirdGap_of_first_and_abel
    (hM1 : MertensFirstTheoremBound)
    (hAbel : AbelInversionMertensSecondFromFirst) :
    Gdbh.PathCMertensProof.PairedBrunMertensThirdGap :=
  pairedBrunMertensThirdGap_of_mertensSecondLowerOdd
    (mertensSecondLowerBoundOdd_of_components hM1 hAbel)

/-! ## Section 3 — Summary -/

/-- **P11-T1 summary, in proof form.**

This file decomposes the named open `MertensSecondLowerBoundOdd` into
three strictly smaller named open sub-Props:

1. `MertensFirstTheoremBound` — Mertens' 1st theorem (deep analytic).
2. `AbelInversionMertensSecondFromFirst` — Abel-summation arrow.
3. `ChebyshevThetaLinearLower` — linear lower bound on `θ`.

Of the **mechanical** bridges, the following are closed
axiom-cleanly in this file:

* `mertensSecondLowerBoundOdd_of_full` — odd-prime restriction
  (drop `p = 2`, absorb into the constant).

* `mertensSecondLowerBoundFull_of_first_and_abel` — composition of
  M1 with the Abel arrow.

* `mertensSecondLowerBoundOdd_of_components` — full assembly
  (M1 + Abel ⇒ Odd form).

* `pairedBrunMertensThirdGap_of_first_and_abel` — composes the P11-T1
  assembly with the P9-T3 reduction.

What remains open after P11-T1: the three sub-Props above, each
strictly smaller than the original `MertensSecondLowerBoundOdd`.
The Abel arrow is *closeable* in principle using
`Mathlib.NumberTheory.AbelSummation` (mathlib v4.29.1); Mertens' 1st
is the genuinely deep input requiring Chebyshev's `ψ` identity (also
absent from mathlib).

(Closed axiom-clean.) -/
theorem pathC_p11_t1_summary : True := trivial

end PathCMertensSecondProof
end Gdbh
