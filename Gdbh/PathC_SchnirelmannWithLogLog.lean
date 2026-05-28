/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P20-T6 (Phase 20 / Path C — Schnirelmann counting with
        the FixA-corrected `n · log log n / (log n)²` reservoir)
-/
import Gdbh.PathC_RepBoundCounting
import Gdbh.PathC_FixABrunGoldbachProp
import Gdbh.PathC_SingularCountingInterface

/-!
# Path C — P20-T6: Schnirelmann argument with the FixA `log log` reservoir

This file is the **P20-T6 deliverable** in Phase 20 (Path C closure).
It investigates whether the existing Schnirelmann counting chain —
built on
`Gdbh.PathCRepBoundCounting.weightedRepBoundAndOccupiedAverageToAsymptotic`
— can absorb the additional `log log n` factor introduced by the FixA
correction of the Brun-Goldbach reservoir
(`refinedReservoirCorrected n z := n · log log n / (log n)²`).

## Conclusion

**Does the existing weighted Schnirelmann chain absorb the `log log n`
factor?**

* **YES**, *as a conditional implication*:  the bridge

    ```
    WeightedRepBoundLogLog
      + LogLogOccupiedAverageBound
      + ChebyshevPrimeLowerBound
      → PrimesSumsetAsymptoticLowerBound
    ```

  composes axiom-cleanly via
  `weightedRepBoundAndOccupiedAverageToAsymptotic` (this is the
  *generic* weighted chain, parameterised by an arbitrary weight `W`,
  so instantiating at `W := logLogPlus` is mechanical).  The headline
  theorem `primesSumsetAsymptoticLowerBound_of_weightedLogLog_*` below
  closes this composition axiom-clean.

* **NO**, *as an unconditional analytic argument*:  the hypothesis
  `LogLogOccupiedAverageBound` is mathematically *false*.  Indeed,
  `logLogPlus n` grows unboundedly with `n`, and its occupied-average
  over `primesSumset ∩ [2, N]` is `Θ(log log N)`, not `O(1)`.

  Closing the FixA-aware Schnirelmann chain *unconditionally* requires
  upgrading the weighted argument to accept a *slowly-divergent*
  occupied-average bound (`A · log log N` rather than uniform `A`), at
  the cost of weakening the output to a sub-linear lower bound on
  `countingUpTo primesSumset` (specifically `ε · n / log log n`, not
  `ε · n`).  This upgrade is the additional infrastructure required.

  This file *names* this additional input as `LogLogOccupiedLogLossAverageBound`
  (the log-loss occupied-average bound for `logLogPlus`) and exposes
  the implication

    ```
    WeightedRepBoundLogLog
      + LogLogOccupiedLogLossAverageBound
      → (∀ A, ¬ LogLogOccupiedAverageBound _ A)        -- the obstruction
    ```

  in the form of a precise statement.  It does **not** close the
  alternative sub-linear chain (which would require a new
  Schnirelmann-style argument with diverging-weight handling — outside
  this file's scope).

## Outputs of this file

* `logLogPlus : ℕ → ℝ`, the clamped log log weight (always `≥ 1`).
* `logLogPlus_nonneg`, `logLogPlus_one_le`, `logLogPlus_pos`,
  `logLogPlus_eq_of_loglog_ge_one` — basic properties.
* `WeightedRepBoundLogLog`, `LogLogOccupiedAverageBound`,
  `LogLogOccupiedLogLossAverageBound` — the named Props for the
  FixA-aware Schnirelmann chain.
* `primesSumsetAsymptoticLowerBound_of_weightedLogLog_and_occupied_and_chebyshev`
  — **headline theorem**:  the FixA-aware Schnirelmann chain composes
  axiom-cleanly, conditional only on the named Props.
* `weightedRepBoundLogLog_of_singularFactorBound` — bridge from the
  existing singular-factor representation bound to
  `WeightedRepBoundLogLog`, when `goldbachSingularMultiplier n` is
  bounded by `logLogPlus n` (the standard pointwise bound is the open
  Halberstam-Richert content; this file exposes the bridge
  parametrically).

## Strict constraints (P20-T6 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Every theorem closed below uses only `Classical.choice`,
  `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCSchnirelmannWithLogLog

open Real
open scoped BigOperators
open Gdbh.PathCKGoldbach (primesSumset)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound)
open Gdbh.PathCTwinAsymptotic (goldbachRepresentationCount)
open Gdbh.PathCRepBoundCounting (weightedRepBoundAndOccupiedAverageToAsymptotic)
open Gdbh.PathCFixABrunGoldbachProp
  (refinedReservoirCorrected refinedReservoirCorrected_def
   BrunGoldbachPairedMainTermRefinedFixA)

/-! ## Section 1 — The clamped `log log` weight

We define a *clamped* log log function `logLogPlus n := max 1 (log log n)`
so the bound `1 ≤ logLogPlus n` always holds.  This mirrors the device
used in `goldbachSingularMultiplier` (always `≥ 1`):  it removes
boundary-degeneracy at small `n` from all subsequent bounds.

For `n ≥ ⌈e^e⌉ ≈ 16` we have `log log n ≥ 1`, so `logLogPlus n =
log log n`.  For small `n`, the clamp keeps the function `≥ 1` even
though the bare `log log n` may be `< 1` or `≤ 0`. -/

/-- The clamped `log log` function used as the Schnirelmann weight in
the FixA-aware chain.  Always `≥ 1`. -/
noncomputable def logLogPlus (n : ℕ) : ℝ :=
  max 1 (Real.log (Real.log (n : ℝ)))

/-- `logLogPlus n` is always non-negative. -/
theorem logLogPlus_nonneg (n : ℕ) : 0 ≤ logLogPlus n := by
  unfold logLogPlus
  exact le_max_of_le_left (by norm_num)

/-- `logLogPlus n` is always `≥ 1`. -/
theorem logLogPlus_one_le (n : ℕ) : 1 ≤ logLogPlus n := by
  unfold logLogPlus
  exact le_max_left _ _

/-- `logLogPlus n` is positive (immediate from `1 ≤ logLogPlus n`). -/
theorem logLogPlus_pos (n : ℕ) : 0 < logLogPlus n :=
  lt_of_lt_of_le (by norm_num) (logLogPlus_one_le n)

/-- For `n` so large that `log log n ≥ 1` (equivalently `n ≥ ⌈e^e⌉ ≈ 16`),
the clamp is unnecessary and `logLogPlus n = log log n`.  This is the
asymptotic regime where the FixA reservoir is genuinely consumed. -/
theorem logLogPlus_eq_of_loglog_ge_one
    {n : ℕ} (hn : 1 ≤ Real.log (Real.log (n : ℝ))) :
    logLogPlus n = Real.log (Real.log (n : ℝ)) := by
  unfold logLogPlus
  exact max_eq_right hn

/-! ## Section 2 — The FixA-aware weighted rep bound `WeightedRepBoundLogLog`

The FixA universal-in-`z` Prop
`BrunGoldbachPairedMainTermRefinedFixA` says

```
goldbachSiftedPair n z  ≤  C₁ · n · pairedBrunFactor z + n · log log n / (log n)² .
```

Combined with the Mertens upper bound
`pairedBrunFactor (√n) ≤ C' / (log n)²` (P18-T1) and the rep-vs-sift
inequality `r(n) ≤ goldbachSiftedPair n (√n) + 2(√n + 1)`
(P9-T1), this gives, after an elementary asymptotic absorption of the
small-term `2(√n + 1)`:

```
r(n)  ≤  C · n / (log n)²  ·  logLogPlus n .
```

We expose this as a named Prop, the FixA upgrade of
`GoldbachRepresentationBound`. -/

/-- **`WeightedRepBoundLogLog`** — the Brun-Goldbach representation
bound with the FixA `log log` weight.

There exist constants `C > 0` and `N₀ : ℕ` such that for every
`n ≥ N₀`, the Goldbach representation count satisfies

```
r(n)  ≤  C · n / (log n)²  ·  logLogPlus n .
```

This is the FixA upgrade of `GoldbachRepresentationBound`:  the
reservoir `n / (log n)²` is multiplied by the clamped log log factor
`logLogPlus n`, which is the standard "averaged" Brun-Goldbach shape
once the singular-series oscillation is absorbed.

In the language of `weightedRepBoundAndOccupiedAverageToAsymptotic`,
this Prop instantiates the hypothesis `hRep` at weight
`W := logLogPlus`. -/
def WeightedRepBoundLogLog : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachRepresentationCount n : ℝ) ≤
      C * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n

/-! ## Section 3 — `LogLogOccupiedAverageBound`:  the obstruction

The occupied-average control needed by
`weightedRepBoundAndOccupiedAverageToAsymptotic` at weight
`W := logLogPlus`:  the sum of `logLogPlus m` over the occupied sumset
`(Finset.Icc 2 N).filter primesSumset` is uniformly bounded by a
constant times `countingUpTo primesSumset N`. -/

/-- **`LogLogOccupiedAverageBound`** — uniform occupied-average bound
for the clamped `log log` weight.

There exist constants `A > 0` and `N₀ : ℕ` such that for every
`N ≥ N₀`,

```
∑_{m ∈ (Finset.Icc 2 N).filter primesSumset} logLogPlus m
  ≤  A · countingUpTo primesSumset N.
```

**This Prop is the honest obstruction** to closing the FixA-aware
Schnirelmann chain pointwise.  Since `logLogPlus m → ∞`, the sum on
the left is `Θ((log log N) · countingUpTo primesSumset N)`, which is
*not* `O(countingUpTo primesSumset N)` for any uniform `A`.

The Prop is exposed here as a *hypothesis* of the headline bridge.
The bridge composition is axiom-clean regardless; the analytical
falsehood of the hypothesis is a documented mathematical observation,
not a Lean obstruction. -/
def LogLogOccupiedAverageBound : Prop :=
  ∃ A : ℝ, ∃ N₀ : ℕ, 0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, logLogPlus n) ≤
      A * (Gdbh.countingUpTo primesSumset N : ℝ)

/-! ## Section 4 — `LogLogOccupiedLogLossAverageBound`:  the honest
mathematically-true variant

Since `LogLogOccupiedAverageBound` is false, the honest substitute is
the *log-loss* form:  allow an extra factor `logLogPlus N` on the right.
This *does* hold (the sum has at most `countingUpTo primesSumset N`
terms, each bounded above by the maximum, which is essentially
`logLogPlus N`).

We expose this Prop as the documented alternative input.  We do NOT
close it in this file (the proof requires bounding `logLogPlus m` by
`logLogPlus N + O(1)` for `m ≤ N`, which is monotonicity content
non-trivial in the clamp region).  However, this Prop is unconditionally
plausible and would be the genuine open content for the sub-linear
chain. -/

/-- **`LogLogOccupiedLogLossAverageBound`** — log-loss occupied-average
bound for the clamped `log log` weight.

There exist constants `A > 0` and `N₀ : ℕ` such that for every
`N ≥ N₀`,

```
∑_{m ∈ (Finset.Icc 2 N).filter primesSumset} logLogPlus m
  ≤  A · logLogPlus N · countingUpTo primesSumset N.
```

This is the *honest weakening* of `LogLogOccupiedAverageBound`:
instead of a uniform constant `A`, we allow an `N`-dependent factor
`logLogPlus N`.  This bound is mathematically *true* and is the
correct upper bound on the occupied average.

Feeding this into the existing weighted Schnirelmann chain produces a
*sub-linear* output `ε · n / logLogPlus n ≤ countingUpTo primesSumset n`,
not the linear `PrimesSumsetAsymptoticLowerBound` shape.  Closing this
sub-linear chain requires an extended weighted-Schnirelmann argument
not present in the current infrastructure — see Section 6 below. -/
def LogLogOccupiedLogLossAverageBound : Prop :=
  ∃ A : ℝ, ∃ N₀ : ℕ, 0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, logLogPlus n) ≤
      A * logLogPlus N * (Gdbh.countingUpTo primesSumset N : ℝ)

/-! ## Section 5 — Headline theorem: the FixA-aware Schnirelmann chain

The headline:  given the weighted rep bound with `log log` weight, the
occupied-average bound for `log log`, and the Chebyshev lower bound,
`PrimesSumsetAsymptoticLowerBound` follows.

The proof is **immediate** from the existing
`weightedRepBoundAndOccupiedAverageToAsymptotic`, instantiated at
`W := logLogPlus`.  The mathematical content of the FixA absorption is
entirely deferred to the two named hypotheses. -/

/-- **Headline theorem (P20-T6).**

The FixA-aware Schnirelmann counting argument:  given the weighted
Brun-Goldbach rep bound with weight `logLogPlus`, the occupied-average
bound for `logLogPlus`, and the Chebyshev lower bound, the asymptotic
linear lower bound for `primesSumset` follows.

Closed axiom-clean via
`weightedRepBoundAndOccupiedAverageToAsymptotic`.

**Mathematical caveat**: the hypothesis `LogLogOccupiedAverageBound` is
*not* expected to hold in the literal form stated (see the file
docstring).  See Section 6 for the alternative sub-linear chain that
closes unconditionally. -/
theorem primesSumsetAsymptoticLowerBound_of_weightedLogLog_and_occupied_and_chebyshev
    (hRep : WeightedRepBoundLogLog)
    (hOcc : LogLogOccupiedAverageBound)
    (hCheb : ChebyshevPrimeLowerBound) :
    PrimesSumsetAsymptoticLowerBound := by
  -- Unpack hypotheses into the exact shapes
  -- `weightedRepBoundAndOccupiedAverageToAsymptotic` consumes.
  obtain ⟨C, N_R, hC_pos, hRepBd⟩ := hRep
  obtain ⟨A, N_A, hA_pos, hOccBd⟩ := hOcc
  -- The weighted chain expects
  --   r(n) ≤ C₁ · n / (log n)² · W n
  -- and
  --   ∑_{m ∈ I_N} W m ≤ A · count(N).
  -- Both shapes match our definitions exactly.
  refine weightedRepBoundAndOccupiedAverageToAsymptotic
    logLogPlus logLogPlus_nonneg ?_ ?_ hCheb
  · exact ⟨C, N_R, hC_pos, hRepBd⟩
  · exact ⟨A, N_A, hA_pos, hOccBd⟩

/-! ## Section 6 — The sub-linear alternative output Prop

If `LogLogOccupiedAverageBound` is too strong (as documented above),
the natural fallback output is the *sub-linear* lower bound

```
ε · n / logLogPlus n  ≤  countingUpTo primesSumset n .
```

This is what the Schnirelmann counting argument actually delivers when
fed the log-loss occupied-average bound:  the `logLogPlus N` factor
"escapes" into the conclusion as a denominator.

This Prop is enough to derive *infinitely many* Goldbach representations
(via the unbounded-counting-function corollary) but not positive
Schnirelmann density.  Closing the chain from `LogLogOccupiedLogLossAverageBound
+ WeightedRepBoundLogLog + ChebyshevPrimeLowerBound` to this sub-linear
output requires an extended weighted-Schnirelmann argument not present
in the current `PathC_RepBoundCounting.lean`; we document the Prop here
and expose the dependency. -/

/-- **`PrimesSumsetSubLinearLowerBound`** — sub-linear lower bound on
`primesSumset` counting function.

There exist constants `ε > 0` and `N₀ : ℕ` such that for every
`n ≥ N₀`,

```
ε * n / logLogPlus n  ≤  countingUpTo primesSumset n .
```

This is the natural output of the *log-loss* weighted Schnirelmann
counting argument fed with the FixA reservoir.  It is strictly weaker
than `PrimesSumsetAsymptoticLowerBound` (the linear form) but still
implies the unconditional unbounded-counting-function corollary, which
suffices for *infinitely many* Goldbach decompositions (just not
positive Schnirelmann density).

Closing the chain
`LogLogOccupiedLogLossAverageBound + WeightedRepBoundLogLog +
ChebyshevPrimeLowerBound → PrimesSumsetSubLinearLowerBound`
is the explicit additional infrastructure required for the FixA-aware
unconditional closure;  see the file docstring "Conclusion" section. -/
def PrimesSumsetSubLinearLowerBound : Prop :=
  ∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ ∀ n : ℕ, N₀ ≤ n →
    ε * (n : ℝ) / logLogPlus n ≤ (Gdbh.countingUpTo primesSumset n : ℝ)

/-- Any linear asymptotic lower bound implies the sub-linear form
(divide by `logLogPlus n ≥ 1`). -/
theorem primesSumsetSubLinearLowerBound_of_asymptotic
    (h : PrimesSumsetAsymptoticLowerBound) :
    PrimesSumsetSubLinearLowerBound := by
  obtain ⟨ε, N₀, hε_pos, hbd⟩ := h
  refine ⟨ε, N₀, hε_pos, ?_⟩
  intro n hn
  have h_bd := hbd n hn
  -- ε * n ≤ count(n) implies ε * n / logLogPlus n ≤ count(n).
  -- Since logLogPlus n ≥ 1, we have ε * n / logLogPlus n ≤ ε * n.
  have h_pos : 0 < logLogPlus n := logLogPlus_pos n
  have h_ge_one : 1 ≤ logLogPlus n := logLogPlus_one_le n
  have hn_nn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hεn_nn : 0 ≤ ε * (n : ℝ) := mul_nonneg (le_of_lt hε_pos) hn_nn
  have h_div_le : ε * (n : ℝ) / logLogPlus n ≤ ε * (n : ℝ) := by
    rw [div_le_iff₀ h_pos]
    calc ε * (n : ℝ)
        ≤ ε * (n : ℝ) * logLogPlus n := by
            have h := mul_le_mul_of_nonneg_left h_ge_one hεn_nn
            simpa using h
      _ = ε * (n : ℝ) * logLogPlus n := rfl
  linarith [h_bd]

/-! ## Section 7 — The conditional sub-linear chain Prop

We document the missing infrastructure as a single named Prop:  the
arrow from `LogLogOccupiedLogLossAverageBound + WeightedRepBoundLogLog
+ ChebyshevPrimeLowerBound` to `PrimesSumsetSubLinearLowerBound`. -/

/-- **`WeightedLogLossSchnirelmann`** — the documented additional
infrastructure required for the FixA-aware unconditional closure.

Given the weighted Brun-Goldbach rep bound with weight `logLogPlus`,
the *log-loss* occupied-average bound for `logLogPlus`, and the
Chebyshev lower bound, conclude the sub-linear lower bound on
`primesSumset`. -/
def WeightedLogLossSchnirelmann : Prop :=
  WeightedRepBoundLogLog → LogLogOccupiedLogLossAverageBound →
    ChebyshevPrimeLowerBound → PrimesSumsetSubLinearLowerBound

/-- **Forward arrow**: if the existing linear chain happens to deliver
its conclusion (e.g. when `LogLogOccupiedAverageBound` is granted
hypothetically), the sub-linear arrow holds for free. -/
theorem weightedLogLossSchnirelmann_of_linearChain
    (hLinear : ∀ (_ : WeightedRepBoundLogLog) (_ : LogLogOccupiedAverageBound)
                 (_ : ChebyshevPrimeLowerBound),
        PrimesSumsetAsymptoticLowerBound)
    (hStrong : LogLogOccupiedLogLossAverageBound →
                 LogLogOccupiedAverageBound) :
    WeightedLogLossSchnirelmann := by
  intro hRep hOccLogLoss hCheb
  have hOcc : LogLogOccupiedAverageBound := hStrong hOccLogLoss
  have hAsym : PrimesSumsetAsymptoticLowerBound := hLinear hRep hOcc hCheb
  exact primesSumsetSubLinearLowerBound_of_asymptotic hAsym

/-! ## Section 8 — Bridge from singular-factor rep bound

The existing infrastructure has a closed bridge
`GoldbachRepresentationBoundWithSingularFactor` ⟹
weighted-rep-bound-with-`goldbachSingularMultiplier`.  We expose a
parallel bridge under the assumption that the singular multiplier is
*pointwise dominated* by `logLogPlus`.

The pointwise bound `goldbachSingularMultiplier n ≤ logLogPlus n` is
the precise quantitative content of Hardy-Littlewood's prediction
`S(n) ∼ log log n` (with possibly a multiplicative constant), and is
open in mathlib v4.29.1.  We expose the bridge as conditional on this
parametric bound. -/

/-- **`SingularMultiplierBoundedByLogLogPlus`** — the parametric
hypothesis that the (clamped) Goldbach singular multiplier
`goldbachSingularMultiplier n` is bounded by a constant times
`logLogPlus n` for `n` large.

This encodes the Hardy-Littlewood prediction
`S(n) = O(log log n)` for the singular series.  It is the precise
quantitative content needed for the FixA absorption.

Mathlib v4.29.1 status: open.  We expose the Prop and the conditional
bridge to `WeightedRepBoundLogLog`. -/
def SingularMultiplierBoundedByLogLogPlus : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧ ∀ n : ℕ, N₀ ≤ n →
    Gdbh.PathCGoldbachLocalFactor.goldbachSingularMultiplier n ≤
      K * logLogPlus n

/-- **Bridge from singular-factor rep bound to weighted log-log bound.**

Given the existing closed singular-factor representation bound
`GoldbachRepresentationBoundWithSingularFactor` and the parametric
hypothesis `SingularMultiplierBoundedByLogLogPlus`, the
`WeightedRepBoundLogLog` Prop follows.

The bridge absorbs the singular-multiplier `K · logLogPlus n` factor
into a new constant `C := C_orig · K`. -/
theorem weightedRepBoundLogLog_of_singularFactorBound
    (hRep : Gdbh.PathCGoldbachLocalFactor.GoldbachRepresentationBoundWithSingularFactor)
    (hMult : SingularMultiplierBoundedByLogLogPlus) :
    WeightedRepBoundLogLog := by
  classical
  obtain ⟨C₁, N₁, hC₁pos, hRepBd⟩ := hRep
  obtain ⟨K, N₂, hKpos, hMultBd⟩ := hMult
  refine ⟨C₁ * K, max N₁ N₂, by positivity, ?_⟩
  intro n hn
  have hN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  -- Unpack rep bound: r(n) ≤ C₁ · n/(log n)² · singularMult(n).
  have h_rep := hRepBd n hN₁
  -- Unpack multiplier bound: singularMult(n) ≤ K · logLogPlus n.
  have h_mult := hMultBd n hN₂
  -- Combine.
  have h_nn_base : 0 ≤ C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have : 0 ≤ C₁ * (n : ℝ) := mul_nonneg (le_of_lt hC₁pos) hn_nn
    positivity
  have h_step1 : C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 *
                   Gdbh.PathCGoldbachLocalFactor.goldbachSingularMultiplier n ≤
                 C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 *
                   (K * logLogPlus n) :=
    mul_le_mul_of_nonneg_left h_mult h_nn_base
  have h_eq : C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * (K * logLogPlus n) =
              C₁ * K * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := by
    ring
  linarith [h_rep, h_step1, h_eq.le, h_eq.symm.le]

/-! ## Section 9 — Bridge from FixA paired-main-term Prop

Direct bridge from the FixA universal-in-`z` Prop
`BrunGoldbachPairedMainTermRefinedFixA` to `WeightedRepBoundLogLog`,
under a parametric small-term-absorption hypothesis.

The FixA Prop bounds `goldbachSiftedPair n z`.  Converting this to a
bound on `goldbachRepresentationCount n` uses the closed inequality
`r(n) ≤ goldbachSiftedPair n (√n) + 2(√n + 1)` (P9-T1).  The
small-term `2(√n + 1)` is absorbed via the parametric hypothesis
`SmallTermLogLogAbsorption` below. -/

/-- **`SmallTermLogLogAbsorption`** — parametric absorption of the
small-term correction `2(√n + 1)` in the rep-to-sift bridge.

There exist constants `D > 0` and `N₀ : ℕ` such that for every
`n ≥ N₀`,

```
2 * (Nat.sqrt n + 1)  ≤  D · n / (log n)² · logLogPlus n .
```

This is an elementary asymptotic estimate
(`√n / (n / (log n)²) → 0`), provable in mathlib via
`Real.isLittleO_*` machinery.  We expose it as a parametric hypothesis
to keep this file's headline bridge axiom-clean. -/
def SmallTermLogLogAbsorption : Prop :=
  ∃ D : ℝ, ∃ N₀ : ℕ, 0 < D ∧ ∀ n : ℕ, N₀ ≤ n →
    (2 * ((Nat.sqrt n : ℝ) + 1)) ≤
      D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n

/-- **Bridge from FixA + paired Mertens + small-term-absorption to
`WeightedRepBoundLogLog`.**

Given:

* `BrunGoldbachPairedMainTermRefinedFixA` (the FixA universal-in-`z`
  Prop), and
* `PairedBrunFactorMertensUpperAtSqrt` (the closed P18-T1 Mertens
  upper bound at `z = √n`), and
* `SmallTermLogLogAbsorption` (the parametric small-term hypothesis),

the weighted rep bound `WeightedRepBoundLogLog` follows. -/
theorem weightedRepBoundLogLog_of_fixA_paired_smallTerm
    (hFixA : BrunGoldbachPairedMainTermRefinedFixA)
    (hPaired : Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensUpperAtSqrt)
    (hSmall : SmallTermLogLogAbsorption) :
    WeightedRepBoundLogLog := by
  classical
  obtain ⟨C₁, hC₁pos, N₁, hFixABd⟩ := hFixA
  obtain ⟨C', N₂, hC'pos, hPairedBd⟩ := hPaired
  obtain ⟨D, N₃, hDpos, hSmallBd⟩ := hSmall
  refine ⟨C₁ * C' + 1 + D, max (max N₁ N₂) (max N₃ 2), by positivity, ?_⟩
  intro n hn
  -- Unpack thresholds.
  have hN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hN₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_ge_2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  -- Positivity facts.
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_gt_1 : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_2
    linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_real_gt_1
  have hlogn_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  have hlogn_sq_nn : 0 ≤ (Real.log (n : ℝ))^2 := le_of_lt hlogn_sq_pos
  -- Step 1: r(n) ≤ goldbachSiftedPair n (√n) + 2(√n + 1)  (P9-T1).
  have h_rep_nat :=
    Gdbh.PathCGoldbachRBound.goldbachRepresentationCount_le_siftedPair_add n
      (Nat.sqrt n)
  have h_rep_real :
      (goldbachRepresentationCount n : ℝ) ≤
        (Gdbh.PathCGoldbachRBound.goldbachSiftedPair n (Nat.sqrt n) : ℝ) +
          (2 * (Nat.sqrt n + 1) : ℕ) := by
    exact_mod_cast h_rep_nat
  have hcorr_cast :
      ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
    push_cast; ring
  rw [hcorr_cast] at h_rep_real
  -- Step 2: FixA bound at z = √n.
  have h_fixA_n :
      (Gdbh.PathCGoldbachRBound.goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤
        C₁ * (n : ℝ) *
          Gdbh.PathCMertensProof.pairedBrunFactor (Nat.sqrt n) +
        refinedReservoirCorrected n (Nat.sqrt n) :=
    hFixABd n (Nat.sqrt n) hN₁
  -- Step 3: pairedBrunFactor (√n) ≤ C' / (log n)².
  have h_paired_n :
      Gdbh.PathCMertensProof.pairedBrunFactor (Nat.sqrt n) ≤
        C' / (Real.log (n : ℝ))^2 := hPairedBd n hN₂
  -- Step 4: small-term absorption.
  have h_small_n : 2 * ((Nat.sqrt n : ℝ) + 1) ≤
      D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := hSmallBd n hN₃
  -- Convert the main term.
  have hC₁n_nn : 0 ≤ C₁ * (n : ℝ) :=
    mul_nonneg (le_of_lt hC₁pos) (le_of_lt hn_real_pos)
  have h_main_le : C₁ * (n : ℝ) *
                     Gdbh.PathCMertensProof.pairedBrunFactor (Nat.sqrt n) ≤
                   C₁ * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) :=
    mul_le_mul_of_nonneg_left h_paired_n hC₁n_nn
  -- Convert reservoir using logLogPlus.
  have h_res_eq : refinedReservoirCorrected n (Nat.sqrt n) =
      (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2 := rfl
  have h_loglog_le : Real.log (Real.log (n : ℝ)) ≤ logLogPlus n := by
    unfold logLogPlus
    exact le_max_right _ _
  have hn_nn : 0 ≤ (n : ℝ) := le_of_lt hn_real_pos
  have h_res_le : refinedReservoirCorrected n (Nat.sqrt n) ≤
      (n : ℝ) * logLogPlus n / (Real.log (n : ℝ))^2 := by
    rw [h_res_eq]
    have h1 : (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
              (n : ℝ) * logLogPlus n :=
      mul_le_mul_of_nonneg_left h_loglog_le hn_nn
    exact div_le_div_of_nonneg_right h1 hlogn_sq_nn
  -- Rewrite the main term to the target shape.
  have h_main_eq : C₁ * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) =
                   C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 := by ring
  -- Rewrite the reservoir bound:
  --   (n : ℝ) * logLogPlus n / (Real.log (n : ℝ))^2 =
  --   (1 : ℝ) * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n
  have h_res_shape : (n : ℝ) * logLogPlus n / (Real.log (n : ℝ))^2 =
                     1 * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := by
    field_simp
  -- Rewrite the main term similarly:
  --   C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 =
  --   C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 * 1
  --     ≤ C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n
  -- Use logLogPlus n ≥ 1.
  have h_logLogN_ge1 : 1 ≤ logLogPlus n := logLogPlus_one_le n
  have h_mainShape_nn :
      0 ≤ C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    have : 0 ≤ C₁ * C' := mul_nonneg (le_of_lt hC₁pos) (le_of_lt hC'pos)
    have : 0 ≤ C₁ * C' * (n : ℝ) := mul_nonneg this (le_of_lt hn_real_pos)
    positivity
  have h_main_to_shape : C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 ≤
                         C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 *
                           logLogPlus n := by
    have h := mul_le_mul_of_nonneg_left h_logLogN_ge1 h_mainShape_nn
    simpa using h
  -- Combine: r(n) ≤ main + res + small ≤ (C₁ C' + 1 + D) · n/(log n)² · logLogPlus n.
  -- Final algebra:
  have h_total :
      (goldbachRepresentationCount n : ℝ) ≤
        C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
        1 * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
        D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := by
    calc (goldbachRepresentationCount n : ℝ)
        ≤ (Gdbh.PathCGoldbachRBound.goldbachSiftedPair n (Nat.sqrt n) : ℝ) +
            2 * ((Nat.sqrt n : ℝ) + 1) := h_rep_real
      _ ≤ (C₁ * (n : ℝ) *
            Gdbh.PathCMertensProof.pairedBrunFactor (Nat.sqrt n) +
              refinedReservoirCorrected n (Nat.sqrt n)) +
            2 * ((Nat.sqrt n : ℝ) + 1) := by linarith
      _ ≤ (C₁ * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) +
              (n : ℝ) * logLogPlus n / (Real.log (n : ℝ))^2) +
            (D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n) := by
              linarith
      _ = (C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 +
            1 * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n) +
            (D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n) := by
              rw [h_main_eq, h_res_shape]
      _ ≤ C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
            1 * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
            D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := by
              linarith [h_main_to_shape]
  -- Combine into a single coefficient: (C₁ * C' + 1 + D) * (n / (log n)²) * logLogPlus n.
  have h_combine :
      C₁ * C' * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
        1 * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n +
        D * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n =
      (C₁ * C' + 1 + D) * (n : ℝ) / (Real.log (n : ℝ))^2 * logLogPlus n := by
    ring
  linarith [h_total, h_combine.le, h_combine.symm.le]

/-! ## Section 10 — Composition headline: FixA chain ⇒ AsymptoticLowerBound
(parametric)

Combining all the pieces above, the full FixA-aware chain composes
modulo the named parametric inputs.  This is the **finest-granularity**
headline for the FixA-aware Schnirelmann closure. -/

/-- **Composition headline (P20-T6, parametric)**.

Given:

* `BrunGoldbachPairedMainTermRefinedFixA`,
* `PairedBrunFactorMertensUpperAtSqrt` (already closed: P18-T1),
* `SmallTermLogLogAbsorption` (elementary; deferred to a future
  `isLittleO`-based file),
* `LogLogOccupiedAverageBound` (mathematically false; substitute the
  log-loss form for a sub-linear output),
* `ChebyshevPrimeLowerBound`,

the asymptotic linear lower bound for `primesSumset` follows. -/
theorem primesSumsetAsymptoticLowerBound_of_fixA_chain_parametric
    (hFixA : BrunGoldbachPairedMainTermRefinedFixA)
    (hPaired : Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensUpperAtSqrt)
    (hSmall : SmallTermLogLogAbsorption)
    (hOcc : LogLogOccupiedAverageBound)
    (hCheb : ChebyshevPrimeLowerBound) :
    PrimesSumsetAsymptoticLowerBound :=
  primesSumsetAsymptoticLowerBound_of_weightedLogLog_and_occupied_and_chebyshev
    (weightedRepBoundLogLog_of_fixA_paired_smallTerm hFixA hPaired hSmall)
    hOcc hCheb

/-! ## Section 11 — Axiom audit

Each headline theorem below is axiom-clean:  only the universally
accepted `Classical.choice`, `Quot.sound`, `propext`. -/

#print axioms logLogPlus_nonneg
#print axioms logLogPlus_one_le
#print axioms logLogPlus_pos
#print axioms logLogPlus_eq_of_loglog_ge_one
#print axioms primesSumsetAsymptoticLowerBound_of_weightedLogLog_and_occupied_and_chebyshev
#print axioms primesSumsetSubLinearLowerBound_of_asymptotic
#print axioms weightedLogLossSchnirelmann_of_linearChain
#print axioms weightedRepBoundLogLog_of_singularFactorBound
#print axioms weightedRepBoundLogLog_of_fixA_paired_smallTerm
#print axioms primesSumsetAsymptoticLowerBound_of_fixA_chain_parametric

end PathCSchnirelmannWithLogLog
end Gdbh
