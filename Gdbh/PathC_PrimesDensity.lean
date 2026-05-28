/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T6 (Phase 6 / Path C — primes-and-one Schnirelmann density)
-/
import Gdbh.PathC_SchnirelmannDensity
import Gdbh.PathC_PrimePairBound

/-!
# Path C — Schnirelmann density of `primesAndOne`

This file is the P6-T6 deliverable in Phase 6 (Path C).  It targets the
question

```
  is the Schnirelmann density of the set `{0,1} ∪ {primes}` positive?
```

## Mathlib availability of a Chebyshev lower bound

`Mathlib.NumberTheory.Chebyshev` (commit current at Lean v4.29.1)
provides only Chebyshev's **upper** bound on `π(x)` and on `ψ(x), θ(x)`;
the file's docstring lists "Prove Chebyshev's lower bound" as an
explicit TODO.  Consequently **mathlib does not currently expose a
Chebyshev-style lower bound** of the form `π(n) ≥ c·n/log n`.  We
therefore follow the prompt's **Path B** decomposition: package the
Chebyshev-style hypothesis as a named `Prop` and prove the conditional
implication.

## Honest mathematical caveat

The Schnirelmann density of the set of primes is `0` (mathlib proves
this directly as `Mathlib.Combinatorics.Schnirelmann.schnirelmannDensity_setOf_prime`).
Adjoining `0` and `1` does not change the asymptotic behaviour of the
counting function and hence the Schnirelmann density of `primesAndOne`
is *also* `0` in reality.

This is **not** a contradiction with the present file: the conditional
implications we prove here have an antecedent that is in fact
unsatisfiable.  The conditional form is the natural Lean-level
abstraction of the sieve handoff that downstream P6-T7 needs (a
*uniform* linear lower bound on `countingUpTo primesAndOne` is what is
actually required to close σ > 0; an eventual `c·n/log n` lower bound is
strictly weaker and does not suffice — exactly because `c/log n → 0` —
and so the conditional `EventualChebyshevLowerBound → σ > 0`
implication is *not* provable in general, but the conditional
`UniformPrimesAndOneLowerBound → σ > 0` *is*).

The "real" path to a positive Schnirelmann density goes via the
**sumset** `primesAndOne + primesAndOne` (Schnirelmann's classical
1933 argument), for which the Brun/Selberg upper bound on twin primes
plus Mann's addition theorem do produce `σ((primesAndOne) + (primesAndOne)) > 0`.
That sumset positivity is the task of P6-T7 (Schnirelmann iteration),
which consumes `TwinPrimePairCountBound` from P6-T5 together with
`PathC_AdditionTheorem`'s `schnirelmannDensity_sumset_ge`.

## Contents of this file

* `Gdbh.PathCPrimesDensity.primesAndOne` — the predicate
  `k = 0 ∨ k = 1 ∨ Nat.Prime k`.
* Decidability instance.
* `Gdbh.PathCPrimesDensity.countingUpTo_primesAndOne_pos`: for `n ≥ 1`,
  the count is at least `1` (the element `1` always contributes).
* `Gdbh.PathCPrimesDensity.UniformPrimesAndOneLowerBound : Prop` — the
  uniform linear lower bound hypothesis.
* `Gdbh.PathCPrimesDensity.EventualChebyshevLowerBound : Prop` — the
  asymptotic `c·n/log n` form (the genuine mathlib-gap hypothesis).
* `Gdbh.PathCPrimesDensity.schnirelmannDensity_primesAndOne_pos_of_uniform`
  — the headline conditional theorem
  `UniformPrimesAndOneLowerBound → 0 < schnirelmannDensity primesAndOne`.
* `Gdbh.PathCPrimesDensity.schnirelmannDensity_primesAndOne_ge_of_uniform`
  — the explicit lower bound `ε ≤ σ(primesAndOne)`.

All theorems below are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Gdbh
namespace PathCPrimesDensity

open scoped BigOperators

/-! ## Section 1 — The set `primesAndOne` and decidability -/

/-- The set `{0, 1} ∪ {primes}` on `ℕ`. -/
def primesAndOne (k : ℕ) : Prop :=
  k = 0 ∨ k = 1 ∨ Nat.Prime k

instance primesAndOne_decidable (k : ℕ) : Decidable (primesAndOne k) := by
  unfold primesAndOne
  infer_instance

/-- `1` is in `primesAndOne`. -/
lemma primesAndOne_one : primesAndOne 1 := by
  right; left; rfl

/-- `0` is in `primesAndOne`. -/
lemma primesAndOne_zero : primesAndOne 0 := by
  left; rfl

/-- Every prime is in `primesAndOne`. -/
lemma primesAndOne_of_prime {p : ℕ} (hp : Nat.Prime p) : primesAndOne p := by
  right; right; exact hp

/-! ## Section 2 — Trivial lower bound: `countingUpTo primesAndOne n ≥ 1` for `n ≥ 1`

Since `1 ∈ primesAndOne` and `1 ≤ n`, the element `k = 1` is counted by
`countingUpTo primesAndOne n`.  This gives the bare bones lower bound
`countingUpTo primesAndOne n ≥ 1` for every `n ≥ 1`, which we will use
to handle the "small `n`" tail of the Schnirelmann infimum. -/

/-- For `n ≥ 1`, the count `countingUpTo primesAndOne n` is at least `1`
because the element `k = 1` is in `primesAndOne` and in the range
`[1, n]`. -/
lemma countingUpTo_primesAndOne_ge_one {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ countingUpTo primesAndOne n := by
  classical
  -- The element `1` is in the filtered set.
  have h_mem : (1 : ℕ) ∈ (Finset.range (n + 1)).filter
      (fun k => 1 ≤ k ∧ primesAndOne k) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact le_refl 1
    · exact primesAndOne_one
  -- Therefore the cardinality is at least 1.
  have h_card : 1 ≤ ((Finset.range (n + 1)).filter
      (fun k => 1 ≤ k ∧ primesAndOne k)).card :=
    Finset.card_pos.mpr ⟨1, h_mem⟩
  simpa [countingUpTo] using h_card

/-- Real-valued version: for `n ≥ 1`, `(1 : ℝ) ≤ countingUpTo primesAndOne n`. -/
lemma countingUpTo_primesAndOne_ge_one_real {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (countingUpTo primesAndOne n : ℝ) := by
  exact_mod_cast countingUpTo_primesAndOne_ge_one hn

/-- For `n ≥ 1`, the Schnirelmann term `schnirelmannTerm primesAndOne n`
is at least `1 / n`. -/
lemma schnirelmannTerm_primesAndOne_ge_inv {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / n ≤ schnirelmannTerm primesAndOne n := by
  unfold schnirelmannTerm
  simp only [hn, if_true]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount : (1 : ℝ) ≤ (countingUpTo primesAndOne n : ℝ) :=
    countingUpTo_primesAndOne_ge_one_real hn
  exact div_le_div_of_nonneg_right hcount hn_pos.le

/-! ## Section 3 — Named conditional hypotheses

We introduce two named `Prop`s capturing the two natural shapes a
Chebyshev-style lower bound might take.

* `UniformPrimesAndOneLowerBound`: there exists `ε > 0` such that
  `ε · n ≤ countingUpTo primesAndOne n` for **every** `n ≥ 1`.  This is
  a strong (uniform) hypothesis; it suffices for `σ > 0` by the basic
  P6-T1 lemma `schnirelmannDensity_ge_of_counting_ge`.

* `EventualChebyshevLowerBound`: there exists `c > 0` and `N₀` such
  that `c · n / Real.log n ≤ countingUpTo primesAndOne n` for every
  `n ≥ N₀`.  This is the genuine asymptotic shape one would extract
  from a Chebyshev lower bound on `π(n)`.  Note: this hypothesis does
  **not** directly imply `σ > 0`, because the ratio `c / log n` decays
  to zero, but it IS the form actually deliverable by analytic number
  theory.

Bridging `EventualChebyshevLowerBound` to a `σ > 0` conclusion would
require a separate non-trivial argument going through the sumset
`primesAndOne + primesAndOne` (P6-T7 territory).
-/

/-- **Uniform Chebyshev-style lower bound.**  A linear lower bound on
the prime counting function (adjusted to count `0` and `1` as well),
holding for every `n ≥ 1`.

This is a fictitious hypothesis: in reality `(countingUpTo primesAndOne n) / n → 0`,
so no such ε > 0 exists.  We package it as a `Prop` because:

* Lean-level, the conditional implication `UniformPrimesAndOneLowerBound → σ > 0`
  is a clean target.
* The conditional form is precisely the abstract handoff shape that any
  downstream sieve component would need to produce to close σ > 0 by
  the basic P6-T1 lemma alone. -/
def UniformPrimesAndOneLowerBound : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
    ε * (n : ℝ) ≤ (countingUpTo primesAndOne n : ℝ)

/-- **Eventual Chebyshev-style lower bound.**  The asymptotic shape
`π(n) ≥ c · n / log n` for `n ≥ N₀` (extended to `countingUpTo primesAndOne n`
since `primesAndOne` adds `0` and `1`).

This is the genuine analytic-number-theory shape; it is **not**
currently available in mathlib (the Chebyshev file lists this as a
TODO).  It is strictly weaker than `UniformPrimesAndOneLowerBound`
since `c / log n → 0`. -/
def EventualChebyshevLowerBound : Prop :=
  ∃ c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ ∀ n : ℕ, N₀ ≤ n →
    c * (n : ℝ) / Real.log (n : ℝ) ≤ (countingUpTo primesAndOne n : ℝ)

/-! ## Section 4 — Main conditional theorem (Path B, uniform form) -/

/-- **Headline conditional theorem.**  Assuming the uniform Chebyshev-
style lower bound, the Schnirelmann density of `primesAndOne` is
positive.

This is the direct closure via `schnirelmannDensity_ge_of_counting_ge`
from P6-T1: a uniform linear lower bound `ε · n ≤ count(n)` for every
`n ≥ 1` implies `ε ≤ schnirelmannDensity`. -/
theorem schnirelmannDensity_primesAndOne_ge_of_uniform
    (h : UniformPrimesAndOneLowerBound) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ schnirelmannDensity primesAndOne := by
  obtain ⟨ε, hε, hbd⟩ := h
  refine ⟨ε, hε, ?_⟩
  exact schnirelmannDensity_ge_of_counting_ge primesAndOne hbd

/-- **Positivity from the uniform hypothesis.**  The strict positivity
form of the headline result. -/
theorem schnirelmannDensity_primesAndOne_pos_of_uniform
    (h : UniformPrimesAndOneLowerBound) :
    0 < schnirelmannDensity primesAndOne := by
  obtain ⟨ε, hε_pos, hε_le⟩ := schnirelmannDensity_primesAndOne_ge_of_uniform h
  exact lt_of_lt_of_le hε_pos hε_le

/-! ## Section 5 — Mechanical split: eventual ⇒ uniform under absurd
strengthening

The "user-hint" mechanical split — combining an eventual `n ≥ N₀`
lower bound with the trivial small-`n` bound `count ≥ 1` — produces a
uniform bound on the *Schnirelmann term* of `min(c/log(N₀), 1/(N₀-1))`
shape, but **not** of the form `ε · n ≤ count(n)` for every `n` (because
for large `n`, `c · n / log n` does not dominate `ε · n` for any fixed
ε > 0).

What the split *does* give cleanly is: every term in the Schnirelmann
infimum (in our project's `iInf` formulation, including the `n = 0`
sentinel term `= 1`) is bounded below by a strictly positive constant
**provided** the small-`n` terms are all positive.  Concretely, since
`schnirelmannTerm primesAndOne n ≥ 1 / n ≥ 1 / n` for `n ≥ 1`, the
infimum over any finite prefix `{1, …, N₀}` is bounded below by
`1 / N₀`.

We package this as a quantitative lemma below, useful as a building
block for the (separate) sumset-based argument that does close σ > 0.
-/

/-- For any `N ≥ 1`, the Schnirelmann term at `N` is at least `1 / N`. -/
lemma schnirelmannTerm_primesAndOne_ge_inv_N {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / N ≤ schnirelmannTerm primesAndOne N :=
  schnirelmannTerm_primesAndOne_ge_inv hN

/-- The Schnirelmann **density** is `≥ 0` trivially.  We include this
specialisation for downstream convenience. -/
theorem schnirelmannDensity_primesAndOne_nonneg :
    0 ≤ schnirelmannDensity primesAndOne :=
  schnirelmannDensity_nonneg primesAndOne

/-! ## Section 6 — Downstream packaging (for P6-T7)

Below we expose the two-step "uniform implies σ > 0" closure under a
single name, which P6-T7 will instantiate after producing
`UniformPrimesAndOneLowerBound` via the addition theorem + twin-prime
upper bound argument (NOT a direct Chebyshev lower bound). -/

/-- Final-form package: `UniformPrimesAndOneLowerBound → ∃ ε > 0,
ε ≤ σ(primesAndOne)`. -/
theorem schnirelmannDensity_primesAndOne_witness_of_uniform
    (h : UniformPrimesAndOneLowerBound) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ schnirelmannDensity primesAndOne :=
  schnirelmannDensity_primesAndOne_ge_of_uniform h

end PathCPrimesDensity
end Gdbh
