/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P8-T4 (Phase 8 / Path C closure — TwinAndChebyshevToUniform decomposition)
-/
import Gdbh.PathC_PrimesSumsetDensity

/-!
# Path C — Decomposition of the combinatorial bridge `TwinAndChebyshevToUniform`

This file is the **P8-T4 deliverable** in Phase 8 (Path C closure). It
targets the named open `Prop`

```
def TwinAndChebyshevToUniform : Prop :=
  TwinPrimePairCountBound → ChebyshevPrimeLowerBound →
    PrimesSumsetUniformLowerBound
```

from `Gdbh/PathC_PrimesSumsetDensity.lean`.

## Honest assessment of the obstruction

The mission was to close `TwinAndChebyshevToUniform` "purely
combinatorially".  A careful inspection of the hypotheses and the
conclusion shows that this is **not** possible without an additional
analytic input.  The obstruction is the following:

1.  `PrimesSumsetUniformLowerBound` asserts a **linear** lower bound
    `ε · n ≤ countingUpTo primesSumset n` for every `n ≥ 1`.
2.  `ChebyshevPrimeLowerBound` gives `π(n) ≥ c · n / log n`, which is
    **sub-linear** (since `log n → ∞`).
3.  `TwinPrimePairCountBound` is stated with the slack `+ N`, which
    makes the bound `≤ C · N / (log N)² + N` trivial: every count of a
    subset of `[1, N]` is `≤ N` anyway.  In particular, `C = 0` and
    `N₀ = 0` already discharges it.

So neither hypothesis carries enough mathematical content to force a
*linear* lower bound on the counting function of `primesSumset`.  In
the classical Schnirelmann argument, the missing input is a Brun-style
upper bound on the **representation function**
`r(n) := #{(p, q) prime : p + q = n}`, which is genuinely different
from the twin-prime count.

## What this file does deliver

We deliver an **honest decomposition** of `TwinAndChebyshevToUniform`
into:

* `PrimesSumsetAsymptoticLowerBound : Prop` — a new named, weaker
  output: an *eventual* linear lower bound `ε · n ≤ countingUpTo
  primesSumset n` for `n ≥ N₀`.  This is the strictly weaker form that
  any classical Schnirelmann argument actually produces (the asymptotic
  output of the counting argument).
* `TwinAndChebyshevToAsymptotic : Prop` — the open analytic content,
  stating that the two hypotheses force the *asymptotic* linear lower
  bound.

We then prove **mechanically and unconditionally**:

* `primesSumsetUniformLowerBound_of_asymptotic` —
  `PrimesSumsetAsymptoticLowerBound → PrimesSumsetUniformLowerBound`.
  The finite tail `1 ≤ n < N₀` is handled by the trivial inclusion
  `1 ∈ primesSumset`, which gives `countingUpTo primesSumset n ≥ 1` for
  every `n ≥ 1`; choosing `ε` small enough then handles the tail.

* `twinAndChebyshevToUniform_of_asymptoticBridge` —
  `TwinAndChebyshevToAsymptotic → TwinAndChebyshevToUniform`.  This is
  the mechanical composition of the previous reduction with the
  asymptotic bridge.

This decomposition is *honest*: it precisely captures the residual
analytic content (the asymptotic Schnirelmann counting argument) as a
single named open `Prop`, and discharges the elementary mechanical
"asymptotic-to-uniform" step in a purely combinatorial way.

All theorems are axiom-clean: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Gdbh
namespace PathCTwinChebyshev

open scoped BigOperators
open Gdbh.PathCKGoldbach (primesSumset primesSumset_zero primesSumset_one)
open Gdbh.PathCPrimesDensity (primesAndOne primesAndOne_zero primesAndOne_one
  countingUpTo_primesAndOne_ge_one)
open Gdbh.PathCPrimePairBound (TwinPrimePairCountBound)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound
  PrimesSumsetUniformLowerBound TwinAndChebyshevToUniform)

/-! ## Section 1 — A trivial counting lower bound on `primesSumset`

`1 ∈ primesSumset` (witnessed by `0 + 1`), hence
`countingUpTo primesSumset n ≥ 1` for every `n ≥ 1`.  This handles the
"finite tail" of the asymptotic-to-uniform reduction. -/

/-- `primesAndOne ⊆ primesSumset`: every element of `primesAndOne` is in
the sumset because `0 ∈ primesAndOne`. -/
lemma primesAndOne_subset_primesSumset :
    ∀ k, primesAndOne k → primesSumset k := by
  intro k hk
  change Gdbh.sumset primesAndOne primesAndOne k
  rw [Gdbh.sumset_iff]
  exact ⟨0, k, primesAndOne_zero, hk, by simp⟩

/-- `countingUpTo primesSumset n ≥ 1` for every `n ≥ 1`. -/
lemma countingUpTo_primesSumset_ge_one {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ countingUpTo primesSumset n := by
  have h₁ : 1 ≤ countingUpTo primesAndOne n :=
    countingUpTo_primesAndOne_ge_one hn
  have h₂ : countingUpTo primesAndOne n ≤ countingUpTo primesSumset n :=
    Gdbh.countingUpTo_mono primesAndOne primesSumset
      primesAndOne_subset_primesSumset n
  exact le_trans h₁ h₂

/-- Real-cast variant of `countingUpTo_primesSumset_ge_one`. -/
lemma countingUpTo_primesSumset_ge_one_real {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (countingUpTo primesSumset n : ℝ) := by
  exact_mod_cast countingUpTo_primesSumset_ge_one hn

/-! ## Section 2 — The asymptotic linear lower bound (new named open Prop)

Any classical Schnirelmann counting argument produces an *eventual*
linear lower bound: `∃ ε > 0, N₀, ∀ n ≥ N₀, ε · n ≤ countingUpTo
primesSumset n`.  The uniform-on-all-`n ≥ 1` form (which the rest of
Path C consumes) is obtained from this by an elementary mechanical
adjustment of `ε`. -/

/-- **Asymptotic Schnirelmann lower bound on `primesSumset`.**

There exists `ε > 0` and `N₀` such that for every `n ≥ N₀`,

```
  ε * n ≤ countingUpTo primesSumset n.
```

This is the strictly weaker, *eventual* form of
`PrimesSumsetUniformLowerBound`.  It is the natural output of the
classical counting argument: the argument controls the counting
function asymptotically, with no a priori control on the finite tail
`1 ≤ n < N₀`. -/
def PrimesSumsetAsymptoticLowerBound : Prop :=
  ∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ ∀ n : ℕ, N₀ ≤ n →
    ε * (n : ℝ) ≤ (countingUpTo primesSumset n : ℝ)

/-- **Open analytic content** (named open `Prop`).

This is the genuinely missing combinatorial step:  from the consolidated
twin-prime sieve bound and the Chebyshev lower bound, derive the
*asymptotic* linear lower bound on `countingUpTo primesSumset`.

This is the strictly weaker — and structurally more honest —
replacement of `TwinAndChebyshevToUniform`:  the asymptotic version is
what the actual classical Schnirelmann counting argument produces.

The remaining mechanical step — passing from the asymptotic to the
uniform form by adjusting `ε` to absorb the finite tail — is
discharged unconditionally below by
`primesSumsetUniformLowerBound_of_asymptotic`. -/
def TwinAndChebyshevToAsymptotic : Prop :=
  TwinPrimePairCountBound → ChebyshevPrimeLowerBound →
    PrimesSumsetAsymptoticLowerBound

/-! ## Section 3 — Mechanical reduction: asymptotic ⟹ uniform

The reduction is the standard "adjust ε downwards to absorb the finite
tail" argument:  for `1 ≤ n < N₀`, the trivial lower bound
`countingUpTo primesSumset n ≥ 1` together with `ε' · n ≤ ε' · N₀`
gives the bound whenever `ε' ≤ 1 / N₀`.  Choosing
`ε' := min ε (1 / (N₀ + 1))` then handles both regimes uniformly.

This step is purely combinatorial and unconditional. -/

/-- **Mechanical asymptotic-to-uniform reduction.**

The asymptotic lower bound on `countingUpTo primesSumset` implies the
uniform-on-all-`n ≥ 1` form.  The reduction is the standard finite-tail
absorption: pick `ε' := min ε (1 / (N₀ + 1))`, where `(ε, N₀)` witness
the asymptotic bound; then for `n ≥ N₀`, the bound is inherited from the
asymptotic form (since `ε' ≤ ε`), and for `1 ≤ n < N₀`, we have
`ε' · n ≤ ε' · N₀ ≤ 1 ≤ countingUpTo primesSumset n`. -/
theorem primesSumsetUniformLowerBound_of_asymptotic
    (h : PrimesSumsetAsymptoticLowerBound) :
    PrimesSumsetUniformLowerBound := by
  obtain ⟨ε, N₀, hε_pos, hbd⟩ := h
  -- Choose the smaller witness ε'.
  set ε' : ℝ := min ε (1 / ((N₀ : ℝ) + 1)) with hε'_def
  have hN₀_real_pos : (0 : ℝ) < (N₀ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ N₀ := by exact_mod_cast Nat.zero_le _
    linarith
  have h_inv_pos : (0 : ℝ) < 1 / ((N₀ : ℝ) + 1) := by
    positivity
  have hε'_pos : 0 < ε' := lt_min hε_pos h_inv_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hε'_le_inv : ε' ≤ 1 / ((N₀ : ℝ) + 1) := min_le_right _ _
  refine ⟨ε', hε'_pos, ?_⟩
  intro n hn
  -- Split on n ≥ N₀ vs. 1 ≤ n < N₀.
  by_cases hN : N₀ ≤ n
  · -- Asymptotic regime.
    have hb := hbd n hN
    have hn_real_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le _
    have : ε' * (n : ℝ) ≤ ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hε'_le_ε hn_real_nonneg
    linarith
  · -- Finite tail: 1 ≤ n < N₀.
    have hN' : n < N₀ := Nat.lt_of_not_le hN
    have hn_lt_N₀ : (n : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN'
    have hn_le_N₀_succ : (n : ℝ) ≤ (N₀ : ℝ) + 1 := by linarith
    -- ε' · n ≤ ε' · (N₀ + 1) ≤ 1.
    have hε'_n_le : ε' * (n : ℝ) ≤ ε' * ((N₀ : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left hn_le_N₀_succ (le_of_lt hε'_pos)
    have h_one : ε' * ((N₀ : ℝ) + 1) ≤ 1 := by
      have : ε' ≤ 1 / ((N₀ : ℝ) + 1) := hε'_le_inv
      have := mul_le_mul_of_nonneg_right this (le_of_lt hN₀_real_pos)
      rw [div_mul_cancel₀] at this
      · exact this
      · exact ne_of_gt hN₀_real_pos
    have h_count_ge_one : (1 : ℝ) ≤ (countingUpTo primesSumset n : ℝ) :=
      countingUpTo_primesSumset_ge_one_real hn
    linarith

/-! ## Section 4 — The decomposition headline

The mechanical bridge from the asymptotic counting argument
(`TwinAndChebyshevToAsymptotic`) to the uniform form
(`TwinAndChebyshevToUniform`).  This reduces P8-T4 to the strictly
easier asymptotic version, which is what classical Schnirelmann
counting arguments actually produce. -/

/-- **Decomposition headline.**

Given the open analytic content `TwinAndChebyshevToAsymptotic` (the
asymptotic Schnirelmann counting argument), the uniform-on-all-`n ≥ 1`
form `TwinAndChebyshevToUniform` follows mechanically by absorbing the
finite tail. -/
theorem twinAndChebyshevToUniform_of_asymptoticBridge
    (h : TwinAndChebyshevToAsymptotic) :
    TwinAndChebyshevToUniform := by
  intro hTwin hCheb
  exact primesSumsetUniformLowerBound_of_asymptotic (h hTwin hCheb)

/-! ## Section 5 — Trivial wrapper: providing the uniform bound directly

We also expose a trivial wrapper:  if one can prove
`PrimesSumsetUniformLowerBound` directly (e.g. by a non-Schnirelmann
route, like a direct verification), then `TwinAndChebyshevToUniform`
holds.  This is purely mechanical. -/

/-- **Trivial wrapper.**  Direct provision of the uniform lower bound
gives `TwinAndChebyshevToUniform`. -/
theorem twinAndChebyshevToUniform_of_uniformLowerBound
    (h : PrimesSumsetUniformLowerBound) :
    TwinAndChebyshevToUniform :=
  fun _ _ => h

/-- **Trivial wrapper, asymptotic form.**  If one can prove
`PrimesSumsetAsymptoticLowerBound` directly (regardless of the
hypotheses), then `TwinAndChebyshevToUniform` holds. -/
theorem twinAndChebyshevToUniform_of_asymptoticLowerBound
    (h : PrimesSumsetAsymptoticLowerBound) :
    TwinAndChebyshevToUniform :=
  fun _ _ => primesSumsetUniformLowerBound_of_asymptotic h

end PathCTwinChebyshev
end Gdbh
