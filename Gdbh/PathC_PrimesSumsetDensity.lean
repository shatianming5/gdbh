/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P7-T2 (Phase 7 / Path C — primes-sumset Schnirelmann density)
-/
import Gdbh.PathC_SchnirelmannDensity
import Gdbh.PathC_AdditionTheorem
import Gdbh.PathC_PrimesDensity
import Gdbh.PathC_PrimePairBound
import Gdbh.PathC_KGoldbach

/-!
# Path C — Positivity of the Schnirelmann density of `primesSumset`

This file is the P7-T2 deliverable in Phase 7 (Path C closure).  It
targets the **bridge field** of the `PathC_AnalyticContent` bundle in
`Gdbh/PathC_Final.lean`:

```
  primesSumsetDensityFromTwinBound :
    TwinPrimePairCountBound → 0 < Gdbh.schnirelmannDensity primesSumset
```

i.e. the implication "the consolidated twin-prime upper bound implies
that the sumset `primesAndOne + primesAndOne` has positive Schnirelmann
density".

## The classical counting bridge

The elementary Schnirelmann-style argument is:

1. **Chebyshev lower bound** `π(N) ≥ c · N / log N` for `N ≥ N₀`
   (mathlib gap — see below).

2. **Twin-prime upper bound**
   `TwinPrimePairCountBound`: `#{n ≤ N : n, n+2 prime} ≤ C N / log² N + N`
   for `N ≥ N₀`.

3. For each prime `p ≤ N`, the elements `{p + q : q prime, q ≤ N}` lie
   in `primesSumset ∩ [0, 2N]`.  Ordered pair count `= π(N)²`.

4. The number of coincidences `p₁ + q₁ = p₂ + q₂` is bounded above by
   sieve-type counts that are sub-quadratic in `π(N)`; under Brun's
   bound, the *distinct* sums are at least `(c²/C) · N` for `N` large.

5. So `countingUpTo primesSumset (2 N) ≥ (c²/C) · N` for `N` large,
   hence `schnirelmannDensity primesSumset ≥ c²/(2C) > 0`.

The **mathlib gap** is step 1: `Mathlib.NumberTheory.Chebyshev` (v4.29.1)
proves *only* the Chebyshev **upper** bound on `π(x)`; the file's
docstring lists "Prove Chebyshev's lower bound" as an explicit TODO.

The **elementary counting gap** is step 4: turning `TwinPrimePairCountBound`
(which counts twin primes `p, p+2`) into a bound on the *Goldbach
representation function* `r(n) := #{(p, q) : p + q = n, p, q prime}` is
itself a non-trivial sieve identity (formally, both arise as Brun-sieve
bounds with different "convolution kernels", but the formal connection
is not packaged in mathlib).

## Honest decomposition

We follow the established pattern of `Gdbh/PathC_PrimesDensity.lean` and
`Gdbh/PathC_PrimePairBound.lean`: package each open analytic content as
a named `Prop`, and prove the mechanical chain of conditional bridges.

* `Gdbh.PathCPrimesSumsetDensity.ChebyshevPrimeLowerBound : Prop` — the
  mathlib-missing Chebyshev lower bound `π(n) ≥ c n / log n`.
* `Gdbh.PathCPrimesSumsetDensity.PrimesSumsetUniformLowerBound : Prop`
  — the abstract output of the counting argument: there exists `ε > 0`
  such that `ε · n ≤ countingUpTo primesSumset n` for every `n ≥ 1`.
  This is exactly the linear lower bound `schnirelmannDensity_ge_of_counting_ge`
  consumes.
* `Gdbh.PathCPrimesSumsetDensity.TwinAndChebyshevToUniform : Prop` —
  the *counting bridge* itself, a named `Prop`: from
  `TwinPrimePairCountBound` and `ChebyshevPrimeLowerBound`, derive
  `PrimesSumsetUniformLowerBound`.

* `primesSumsetDensity_pos_of_uniformLowerBound`
  — `PrimesSumsetUniformLowerBound → 0 < σ(primesSumset)`
  (mechanical; direct application of `schnirelmannDensity_ge_of_counting_ge`).
* `primesSumsetDensity_pos_of_twinBound_and_chebyshev`
  — `TwinPrimePairCountBound → ChebyshevPrimeLowerBound →
       TwinAndChebyshevToUniform → 0 < σ(primesSumset)`
  (the chained bridge with all three inputs).

All theorems below are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Gdbh
namespace PathCPrimesSumsetDensity

open scoped BigOperators
open Gdbh.PathCKGoldbach (primesSumset primesSumset_zero primesSumset_one)
open Gdbh.PathCPrimesDensity (primesAndOne)
open Gdbh.PathCPrimePairBound (TwinPrimePairCountBound)

/-! ## Section 1 — Named open Props (the analytic content) -/

/-- **Chebyshev's prime-counting lower bound.**

There exists `c > 0` and `N₀` such that for every `n ≥ N₀`,

```
  c · n / log n ≤ π n
```

where `π = Nat.primeCounting` is mathlib's prime-counting function.

This is the **mathlib gap** in Path C closure:
`Mathlib.NumberTheory.Chebyshev` (commit v4.29.1) provides only the
Chebyshev *upper* bound on `π(x)` and lists "Prove Chebyshev's lower
bound" as an explicit TODO in its docstring.  We package the lower
bound as a named `Prop` so that the rest of the bridge can be proved
mechanically. -/
def ChebyshevPrimeLowerBound : Prop :=
  ∃ c : ℝ, ∃ N₀ : ℕ, 0 < c ∧ ∀ n : ℕ, N₀ ≤ n →
    c * (n : ℝ) / Real.log (n : ℝ) ≤ (Nat.primeCounting n : ℝ)

/-- **Uniform Schnirelmann lower bound on `primesSumset`.**

There exists `ε > 0` such that for every `n ≥ 1`,

```
  ε · n ≤ countingUpTo primesSumset n.
```

This is the **abstract output** of the elementary counting argument
sketched in the file-level docstring (steps 3–5): once the analytic
inputs (Chebyshev lower bound + twin-prime sieve bound) are supplied,
this linear lower bound is exactly what `schnirelmannDensity_ge_of_counting_ge`
consumes to conclude `0 < σ(primesSumset)`. -/
def PrimesSumsetUniformLowerBound : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
    ε * (n : ℝ) ≤ (countingUpTo primesSumset n : ℝ)

/-- **Counting bridge** (named open `Prop`).

From the consolidated twin-prime sieve bound and the Chebyshev lower
bound, the uniform linear lower bound on `countingUpTo primesSumset n`
holds.

This Prop packages the **elementary counting argument** of the
classical Schnirelmann program: ordered pair count `π(N)²` minus
coincidences (bounded by sieve estimates) gives a quadratic count of
distinct sums on `[0, 2N]`, which after dividing by `2N` is a linear
density.

Formally, this argument has two ingredients:

* `TwinPrimePairCountBound` (P6-T5 consolidated output of Brun/Selberg
  sieves) bounding twin-prime-like coincidences.
* `ChebyshevPrimeLowerBound` (mathlib gap) bounding `π(N)` from below.

The elementary counting step turning these into a linear lower bound
on `countingUpTo primesSumset n` is mechanical real-analytic
manipulation, but goes through the representation function
`r(n) := #{(p, q) primes : p + q = n}` whose upper bound is *not*
literally `TwinPrimePairCountBound` (which counts twin primes
`p, p+2`).  The translation requires a Brun-style sieve identity not
packaged in mathlib.

We therefore expose this counting step itself as a named open `Prop`,
following the established pattern of `PathC_PrimesDensity` and
`PathC_PrimePairBound`. -/
def TwinAndChebyshevToUniform : Prop :=
  TwinPrimePairCountBound → ChebyshevPrimeLowerBound →
    PrimesSumsetUniformLowerBound

/-! ## Section 2 — The mechanical density bridge

The uniform linear lower bound on the counting function of
`primesSumset` immediately implies positivity of its Schnirelmann
density, via the basic P6-T1 lemma. -/

/-- **Mechanical bridge.**  The uniform Schnirelmann lower bound on
`primesSumset` implies positivity of `σ(primesSumset)`. -/
theorem primesSumsetDensity_pos_of_uniformLowerBound
    (h : PrimesSumsetUniformLowerBound) :
    0 < Gdbh.schnirelmannDensity primesSumset := by
  obtain ⟨ε, hε_pos, hbd⟩ := h
  have hε_le : ε ≤ Gdbh.schnirelmannDensity primesSumset :=
    Gdbh.schnirelmannDensity_ge_of_counting_ge primesSumset hbd
  exact lt_of_lt_of_le hε_pos hε_le

/-- **Explicit witness form.**  The uniform Schnirelmann lower bound
yields an explicit positive witness `ε` such that
`ε ≤ σ(primesSumset)`. -/
theorem primesSumsetDensity_ge_of_uniformLowerBound
    (h : PrimesSumsetUniformLowerBound) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ Gdbh.schnirelmannDensity primesSumset := by
  obtain ⟨ε, hε_pos, hbd⟩ := h
  refine ⟨ε, hε_pos, ?_⟩
  exact Gdbh.schnirelmannDensity_ge_of_counting_ge primesSumset hbd

/-! ## Section 3 — The full chained bridge -/

/-- **Headline conditional bridge** (chained form).

From the three named open `Prop`s — `TwinPrimePairCountBound`,
`ChebyshevPrimeLowerBound`, and the counting bridge
`TwinAndChebyshevToUniform` — we deduce `0 < σ(primesSumset)`.

This is the **honest** delivery of the P7-T2 bridge: the implication
is mechanical *given* the three named inputs, and the file documents
exactly which mathlib lemma and which counting argument are still
missing. -/
theorem primesSumsetDensity_pos_of_twinBound_and_chebyshev
    (hTwin : TwinPrimePairCountBound)
    (hCheb : ChebyshevPrimeLowerBound)
    (hCount : TwinAndChebyshevToUniform) :
    0 < Gdbh.schnirelmannDensity primesSumset :=
  primesSumsetDensity_pos_of_uniformLowerBound (hCount hTwin hCheb)

/-! ## Section 4 — Partial bridge (just the twin-prime bound)

For consumption inside the `PathC_AnalyticContent` bundle, we expose
the bridge **as a single function** of `TwinPrimePairCountBound`,
parameterised by the two remaining open `Prop`s.  This matches the
signature of the bundle field
`primesSumsetDensityFromTwinBound : TwinPrimePairCountBound → 0 < σ`. -/

/-- **Bundled bridge.**  Given Chebyshev's prime-counting lower bound
and the counting Prop, the bundle field
`primesSumsetDensityFromTwinBound : TwinPrimePairCountBound → 0 < σ(primesSumset)`
is produced mechanically. -/
theorem primesSumsetDensityFromTwinBound_of_chebyshev_and_counting
    (hCheb : ChebyshevPrimeLowerBound)
    (hCount : TwinAndChebyshevToUniform) :
    TwinPrimePairCountBound → 0 < Gdbh.schnirelmannDensity primesSumset :=
  fun hTwin => primesSumsetDensity_pos_of_twinBound_and_chebyshev hTwin hCheb hCount

/-! ## Section 5 — Bundle field synonym

We expose under a short name the bundle-field-shaped function consumed
by `Gdbh.PathCFinal.PathC_AnalyticContent`. -/

/-- Alias matching the `PathC_AnalyticContent.primesSumsetDensityFromTwinBound`
field signature exactly. -/
theorem primesSumsetDensityFromTwinBound
    (hCheb : ChebyshevPrimeLowerBound)
    (hCount : TwinAndChebyshevToUniform) :
    TwinPrimePairCountBound → 0 < Gdbh.schnirelmannDensity primesSumset :=
  primesSumsetDensityFromTwinBound_of_chebyshev_and_counting hCheb hCount

/-! ## Section 6 — Trivial structural lemmas

For downstream convenience, we record that the Schnirelmann density of
`primesSumset` is nonneg and `≤ 1`, and a simple monotonicity remark. -/

/-- The Schnirelmann density of `primesSumset` is nonneg. -/
theorem schnirelmannDensity_primesSumset_nonneg :
    0 ≤ Gdbh.schnirelmannDensity primesSumset :=
  Gdbh.schnirelmannDensity_nonneg primesSumset

/-- The Schnirelmann density of `primesSumset` is `≤ 1`. -/
theorem schnirelmannDensity_primesSumset_le_one :
    Gdbh.schnirelmannDensity primesSumset ≤ 1 :=
  Gdbh.schnirelmannDensity_le_one primesSumset

/-- `primesSumset ⊇ primesAndOne` (since `0 ∈ primesAndOne`).  Hence
`σ(primesAndOne) ≤ σ(primesSumset)`. -/
theorem schnirelmannDensity_primesAndOne_le_primesSumset :
    Gdbh.schnirelmannDensity primesAndOne ≤
      Gdbh.schnirelmannDensity primesSumset := by
  -- primesSumset = sumset primesAndOne primesAndOne, and
  -- 0 ∈ primesAndOne, so primesAndOne ⊆ primesSumset.
  refine Gdbh.schnirelmannDensity_mono _ _ ?_
  intro k hk
  -- k ∈ primesAndOne ⇒ k = 0 + k ∈ sumset primesAndOne primesAndOne
  change Gdbh.sumset primesAndOne primesAndOne k
  rw [Gdbh.sumset_iff]
  refine ⟨0, k, ?_, hk, by simp⟩
  -- 0 ∈ primesAndOne
  exact Gdbh.PathCPrimesDensity.primesAndOne_zero

end PathCPrimesSumsetDensity
end Gdbh
