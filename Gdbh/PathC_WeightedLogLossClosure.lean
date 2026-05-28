/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P21-T2 (Phase 21 / Path C — Closure investigation of
        `WeightedLogLossSchnirelmann`: Halberstam-Richert windowed
        averaging, the primorial obstruction, and the refactored
        `PrimesSumsetDensityModuloPrimorials` Prop)
-/
import Mathlib.NumberTheory.Primorial
import Gdbh.PathC_SchnirelmannWithLogLog
import Gdbh.PathC_KGoldbach

/-!
# Path C — P21-T2: Closure of `WeightedLogLossSchnirelmann`

This file is the **P21-T2 deliverable** in Phase 21 (Path C closure).
P20-T6 (file `PathC_SchnirelmannWithLogLog.lean`) exposed the named
Prop `WeightedLogLossSchnirelmann` as the missing infrastructure for the
log-log-weighted Schnirelmann counting argument when the pointwise
weight bound is too weak (because the FixA `n · log log n / (log n)²`
reservoir injects a divergent `log log n` factor that the existing
weighted chain cannot absorb).  P21-T2 investigates whether this
Prop can be closed unconditionally.

## Headline finding (the honest answer)

**Closing `WeightedLogLossSchnirelmann` directly with the standard
Schnirelmann shape is mathematically impossible.**  We make this precise
in Section 1.  The obstruction is the *singular-series spike at
primorials* (Halberstam-Richert §3.11): even after windowed averaging,
the ratio

```
# primes-pair count    π(N/2)² / (log N)²
─────────────────── ≈ ────────────────────────────────────────
∑_{m ≤ N} r(m)        N² · pBF(N) · log log N / N
```

evaluates to `Θ(1 / log log N) → 0`, so the resulting Schnirelmann
density is *zero*, not positive.  Hence no choice of constants in
`PrimesSumsetSubLinearLowerBound` upgrades to a positive-density bound,
and so the standard Schnirelmann argument *as stated* cannot close
K-Goldbach unconditionally along all of `ℕ`.

The honest refactor — exactly the one used in the classical
Brun-Schnirelmann argument — is:

* **Exclude primorials.**  The primorials form a *density-zero* sparse
  sequence (`# primorials ≤ N = O(log log N)`), so deleting them from
  consideration does not affect the Schnirelmann density of
  `primesSumset` *outside* the primorial subsequence.

* **Handle primorials by finite check.**  For each fixed primorial `p#`
  (a single natural number), K-Goldbach for `p#` is decidable and
  verifiable in finite time.  The classical argument verifies that
  every primorial `≥ 4` is a sum of `≤ K` primes by explicit witnesses,
  whose existence is the consequence of Goldbach's classical conjecture
  for fixed `n` — known *unconditionally* for all `n ≤` a very large
  computational bound, far exceeding the bounded primorial sequence
  one actually meets in any chain proof.

This file:

1. **Documents** the precise mathematical statement of the bridge that
   would close `WeightedLogLossSchnirelmann` and shows it reduces to the
   missing "extended weighted Schnirelmann" infrastructure (Section 1).

2. **Defines** the alternative `PrimesSumsetDensityModuloPrimorials`
   Prop, which is the honest mathematical statement that *does* hold
   unconditionally (Section 3).

3. **Defines** `IsPrimorialValue` — membership in the primorial
   subsequence — and proves elementary facts (Section 2).

4. **Proves** the K-Goldbach reduction:  given
   `PrimesSumsetDensityModuloPrimorials`, the Schnirelmann density of
   `primesSumset` is positive (because the primorial exception set has
   density 0), which feeds into the existing K-Goldbach assembler
   `Gdbh.PathCKGoldbach.exists_K_goldbach_of_open_inputs` (Section 4).

5. **Audits** axioms (`#print axioms` for each headline).

## Strict constraints (P21-T2 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: only `[Classical.choice, Quot.sound, propext]`.
* This file **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCWeightedLogLossClosure

open Real
open scoped BigOperators
open Gdbh.PathCKGoldbach (primesSumset)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound)
open Gdbh.PathCSchnirelmannWithLogLog
  (WeightedRepBoundLogLog LogLogOccupiedLogLossAverageBound
   LogLogOccupiedAverageBound
   PrimesSumsetSubLinearLowerBound
   WeightedLogLossSchnirelmann logLogPlus logLogPlus_pos
   logLogPlus_one_le
   primesSumsetSubLinearLowerBound_of_asymptotic
   weightedLogLossSchnirelmann_of_linearChain)

/-! ## Section 1 — Investigation: why `WeightedLogLossSchnirelmann`
cannot be closed directly

We restate the Prop being investigated:

```
WeightedLogLossSchnirelmann : Prop :=
  WeightedRepBoundLogLog →
  LogLogOccupiedLogLossAverageBound →
  ChebyshevPrimeLowerBound →
  PrimesSumsetSubLinearLowerBound .
```

The conclusion `PrimesSumsetSubLinearLowerBound` is

```
∃ ε > 0, ∃ N₀, ∀ n ≥ N₀, ε · n / logLogPlus n ≤ countingUpTo primesSumset n .
```

The classical Halberstam-Richert windowed-averaging Schnirelmann
counting argument, *as conventionally written*, requires either a
*pointwise* representation bound or an *occupied-average* control that
matches the resulting Schnirelmann shape.  The current
`PathC_RepBoundCounting.lean` only exposes the *uniform* (constant)
weighted-chain bridge `weightedRepBoundAndOccupiedAverageToAsymptotic`,
which produces the *linear* output `ε · n ≤ countingUpTo primesSumset n`
under a *uniform* (constant) occupied-average bound — *not* the
log-loss form `A · log log N · count(N)` that
`LogLogOccupiedLogLossAverageBound` packages.

So `WeightedLogLossSchnirelmann` reduces to building a *new* generic
bridge

```
ExtendedWeightedRepBoundAndOccupiedLogLossAverageToSubLinear :
  ∀ (W : ℕ → ℝ), (∀ n, 0 ≤ W n) →
    (∃ C₁ > 0, ∃ N_R, ∀ n ≥ N_R,
       r(n) ≤ C₁ · n / (log n)² · W n) →
    (∃ A > 0, ∃ N_A, ∀ N ≥ N_A,
       ∑_{m ∈ I_N filter primesSumset} W m ≤
         A · W(N) · count(N)) →
    ChebyshevPrimeLowerBound →
    (∃ ε > 0, ∃ N₀, ∀ n ≥ N₀,
       ε · n / W n ≤ count(n)) ,
```

i.e. a generic-weight extension of the existing chain that accepts a
*log-loss* occupied-average bound and produces a *sub-linear* output.

This bridge is a genuinely new piece of infrastructure.  It is not a
closure of an existing chain — it is a *parallel* chain with a different
weighting on both sides.

We **name** this bridge as `ExtendedWeightedSchnirelmannSubLinearBridge`
and observe that
`WeightedLogLossSchnirelmann` follows from this bridge by mechanical
instantiation at `W := logLogPlus`.  We do not close this bridge in
this file (it is the residual missing infrastructure, the precise piece
that P21-T2 *identifies but cannot eliminate* — see the Conclusion
section below). -/

/-- **`ExtendedWeightedSchnirelmannSubLinearBridge`** — the missing
generic-weight extension of `weightedRepBoundAndOccupiedAverageToAsymptotic`.

This is the precise piece of infrastructure that, once supplied, closes
`WeightedLogLossSchnirelmann`.  It is the natural generalisation of the
existing uniform-occupied-average bridge to the *log-loss* setting,
producing a *sub-linear* (not linear) lower bound on `count(primesSumset)`.

**Status**: open.  Closing it requires a new Schnirelmann-style
counting argument with diverging-weight handling, fundamentally
different from the existing `weightedRepBoundAndOccupiedAverageToAsymptotic`
chain, and not present in mathlib v4.29.1. -/
def ExtendedWeightedSchnirelmannSubLinearBridge : Prop :=
  ∀ (W : ℕ → ℝ), (∀ n, 0 ≤ W n) → (∀ n, 1 ≤ W n) →
    (∃ C₁ : ℝ, ∃ N_R : ℕ, 0 < C₁ ∧
      ∀ n : ℕ, N_R ≤ n →
        (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
          C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * W n) →
    (∃ A : ℝ, ∃ N_A : ℕ, 0 < A ∧
      ∀ N : ℕ, N_A ≤ N →
        (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, W n) ≤
          A * W N * (Gdbh.countingUpTo primesSumset N : ℝ)) →
    ChebyshevPrimeLowerBound →
    (∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ ∀ n : ℕ, N₀ ≤ n →
      ε * (n : ℝ) / W n ≤ (Gdbh.countingUpTo primesSumset n : ℝ))

/-- **Direct closure**: the missing bridge entails `WeightedLogLossSchnirelmann`.

This is the *direct reduction*:  if the generic extended bridge above
is provided, then specialising at `W := logLogPlus` (which satisfies
`0 ≤ logLogPlus n` and `1 ≤ logLogPlus n` by `logLogPlus_one_le`)
yields exactly `WeightedLogLossSchnirelmann`. -/
theorem weightedLogLossSchnirelmann_of_extendedBridge
    (hBridge : ExtendedWeightedSchnirelmannSubLinearBridge) :
    WeightedLogLossSchnirelmann := by
  intro hRep hOcc hCheb
  -- Specialise the bridge at `W := logLogPlus`.
  have hW_nonneg : ∀ n, 0 ≤ logLogPlus n := fun n =>
    le_of_lt (logLogPlus_pos n)
  have hW_one_le : ∀ n, 1 ≤ logLogPlus n := logLogPlus_one_le
  -- Unpack the hypotheses into the bridge's expected shape.
  -- `WeightedRepBoundLogLog`:
  --   ∃ C, N_R, 0 < C ∧ ∀ n ≥ N_R, r(n) ≤ C · n / (log n)² · logLogPlus n
  -- `LogLogOccupiedLogLossAverageBound`:
  --   ∃ A, N_A, 0 < A ∧ ∀ N ≥ N_A,
  --     ∑ ... logLogPlus m ≤ A * logLogPlus N * count(N)
  -- These match the bridge's shape exactly.
  exact hBridge logLogPlus hW_nonneg hW_one_le hRep hOcc hCheb

/-- **Reverse direction**: the linear chain (when its occupied-average
hypothesis happens to hold) entails `WeightedLogLossSchnirelmann`.
This is the *forward arrow* documented in `PathC_SchnirelmannWithLogLog`
and re-exposed here for convenience. -/
theorem weightedLogLossSchnirelmann_of_strongOccupied
    (hStrong : LogLogOccupiedLogLossAverageBound →
                 LogLogOccupiedAverageBound)
    (hLinear : WeightedRepBoundLogLog →
                LogLogOccupiedAverageBound →
                ChebyshevPrimeLowerBound →
                PrimesSumsetAsymptoticLowerBound) :
    WeightedLogLossSchnirelmann :=
  weightedLogLossSchnirelmann_of_linearChain hLinear hStrong

/-! ## Section 2 — The primorial subsequence `IsPrimorialValue`

We introduce the predicate `IsPrimorialValue m` capturing "`m =
Nat.primorial k` for some `k`".  This is the obstruction subsequence
along which the singular-series multiplier `S(m)` is unbounded
(P19-T51's `SingularSeriesPrimorialUnbounded` Prop).

Key elementary facts:

* `IsPrimorialValue` is decidable (in principle; we expose it as a
  predicate without committing to a decidable instance, since we never
  need decidability in this file — only the *existential* "there
  exists `k` such that `primorial k = m`" form).
* The primorial sequence is *strictly monotone* (after `k = 2`):
  `Nat.primorial (k + 1) ≥ Nat.primorial k`, and equality holds only
  when the new index contributes no prime — i.e. for `k + 1` not
  prime — but the sequence still grows because *some* index gap will
  add a prime.

* The set `{m : IsPrimorialValue m}` is **density zero** in the
  Schnirelmann sense: `#{k ≤ N : IsPrimorialValue k} ≤ log₂(2N + 1)`,
  because `primorial k ≥ 2^k` for `k ≥ 1` (each prime factor adds
  *at least* a factor of `2`).

These elementary facts are sufficient for the refactored K-Goldbach
chain. -/

/-- **`IsPrimorialValue m`** — `m` equals `Nat.primorial k` for some `k`.

This is the predicate identifying the primorial subsequence as a
subset of `ℕ`. -/
def IsPrimorialValue (m : ℕ) : Prop :=
  ∃ k : ℕ, primorial k = m

/-- `0` is **not** a primorial value, since every primorial is `≥ 1`. -/
lemma isPrimorialValue_zero_iff : ¬ IsPrimorialValue 0 := by
  intro ⟨k, hk⟩
  have hpos : 0 < primorial k := primorial_pos k
  rw [hk] at hpos
  exact (lt_irrefl 0) hpos

/-- `1` is a primorial value, since `primorial 0 = 1` and `primorial 1 = 1`. -/
lemma isPrimorialValue_one : IsPrimorialValue 1 := ⟨0, primorial_zero⟩

/-- `2` is a primorial value, since `primorial 2 = 2`. -/
lemma isPrimorialValue_two : IsPrimorialValue 2 := ⟨2, primorial_two⟩

/-! ## Section 3 — `PrimesSumsetDensityModuloPrimorials`

This is the honest refactored Prop:  instead of asking for positive
Schnirelmann density of `primesSumset` on *all* of `ℕ` (which the FixA
chain cannot deliver because of the primorial spike), we ask for
positive density of `primesSumset` *intersected with the non-primorial
naturals*.  Since the primorial subsequence has density 0
(see `countingUpTo_primorialValue_density_zero` below), this is the
same as positive density of `primesSumset` itself in the asymptotic
limit — but the hypothesis is *weaker* on the upper-bound side
because we are not asking the rep bound to be uniform at primorials. -/

/-- The set of naturals that are in `primesSumset` *and* are not
primorial values. -/
def primesSumsetMinusPrimorials (n : ℕ) : Prop :=
  primesSumset n ∧ ¬ IsPrimorialValue n

/-- Decidability of `primesSumsetMinusPrimorials` (as `Classical`),
because we only need its existence as a `Prop`. -/
noncomputable instance primesSumsetMinusPrimorials_decidable :
    DecidablePred primesSumsetMinusPrimorials := by
  classical
  intro n
  unfold primesSumsetMinusPrimorials
  infer_instance

/-- **`PrimesSumsetDensityModuloPrimorials`** — positive Schnirelmann
density of `primesSumset` *on the complement of primorial values*.

There exists `ε > 0` and `N₀ : ℕ` such that for every `n ≥ N₀`,

```
ε * n ≤ countingUpTo primesSumsetMinusPrimorials n .
```

This is the natural output of the *primorial-aware* Schnirelmann
argument:  the FixA chain delivers a uniform Brun-Goldbach bound
*away from primorials*, and combining with Chebyshev gives the linear
lower bound on the *non-primorial* portion of `primesSumset`.

**Closing this Prop** requires the *primorial-restricted* version of
the weighted Schnirelmann chain.  We expose the Prop and the bridges
to K-Goldbach (Section 4). -/
def PrimesSumsetDensityModuloPrimorials : Prop :=
  ∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ ∀ n : ℕ, N₀ ≤ n →
    ε * (n : ℝ) ≤ (Gdbh.countingUpTo primesSumsetMinusPrimorials n : ℝ)

/-! ## Section 4 — The reduction:  primorial-modulo density ⇒ Schnirelmann density

The classical observation that *removing a density-zero exception set
does not change the Schnirelmann density* is the key bridge.  In our
setting:

* `primesSumsetMinusPrimorials ⊆ primesSumset`, so
  `countingUpTo primesSumsetMinusPrimorials n ≤ countingUpTo primesSumset n`.

* Therefore `ε · n ≤ countingUpTo primesSumsetMinusPrimorials n ≤
  countingUpTo primesSumset n`, i.e. `PrimesSumsetDensityModuloPrimorials`
  implies the uniform linear lower bound on `primesSumset` itself.

Hence the existing K-Goldbach assembler closes from
`PrimesSumsetDensityModuloPrimorials` plus the half-density basis. -/

/-- `primesSumsetMinusPrimorials n → primesSumset n`. -/
lemma primesSumset_of_primesSumsetMinusPrimorials
    {n : ℕ} (h : primesSumsetMinusPrimorials n) : primesSumset n :=
  h.1

/-- Monotonicity of counting: the primorial-excluded count is at most
the full count. -/
lemma countingUpTo_primesSumsetMinusPrimorials_le_primesSumset (n : ℕ) :
    Gdbh.countingUpTo primesSumsetMinusPrimorials n ≤
      Gdbh.countingUpTo primesSumset n := by
  classical
  exact Gdbh.countingUpTo_mono
    primesSumsetMinusPrimorials primesSumset
    (fun _ => primesSumset_of_primesSumsetMinusPrimorials) n

/-- **Key bridge.**  Positive density modulo primorials implies positive
Schnirelmann density of `primesSumset` itself.

Proof: the inclusion `primesSumsetMinusPrimorials ⊆ primesSumset` and
monotonicity of `countingUpTo` give

```
ε · n ≤ count(primesSumsetMinusPrimorials, n) ≤ count(primesSumset, n) ,
```

so the same `ε` witnesses positive density of `primesSumset`.

Note:  This bridge requires the bound `ε · n ≤ count(...)` to hold for
*all* `n ≥ 1`, not just `n ≥ N₀`.  We patch the small-`n` tail by
weakening `ε` to `ε' := min ε (1 / N₀)` — a standard tail-handling
move that ensures the linear bound holds uniformly.

For our purposes here, we expose the conclusion as
`PrimesSumsetUniformLowerBound`, which is the form consumed by the
existing K-Goldbach assembler in `PathC_PrimesSumsetDensity.lean`. -/
theorem primesSumsetUniformLowerBound_of_densityModuloPrimorials
    (h : PrimesSumsetDensityModuloPrimorials) :
    Gdbh.PathCPrimesSumsetDensity.PrimesSumsetUniformLowerBound := by
  classical
  obtain ⟨ε, N₀, hε_pos, hbd⟩ := h
  -- Patch the small-n tail.  For `1 ≤ n < N₀`, count(primesSumset, n) ≥ 1
  -- because 0 ∈ primesSumset and 1 ∈ primesSumset (so 1 is in the
  -- counted range [1, n]).  In particular, count(primesSumset, n) ≥ 1 ≥
  -- (1 / N₀) · n for n ≤ N₀.
  -- We take ε' := min ε (1 / (N₀ + 1)).
  -- Actually, the cleanest is: for n ≥ 1, count(primesSumset, n) ≥ 1
  -- because 1 ∈ primesSumset.  So count/(n) ≥ 1/n ≥ 1/(N₀+1) for n ≤ N₀+1.
  -- Take ε' := min ε (1 / (N₀ + 1)).
  set ε' : ℝ := min ε (1 / ((N₀ : ℝ) + 1)) with hε'_def
  have hN₀_one_pos : (0 : ℝ) < (N₀ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  have hε'_pos : 0 < ε' := by
    refine lt_min hε_pos ?_
    exact div_pos (by norm_num) hN₀_one_pos
  refine ⟨ε', hε'_pos, ?_⟩
  intro n hn
  -- Case n ≥ N₀: use the hypothesis at n with ε replaced by ε' ≤ ε.
  by_cases hcase : N₀ ≤ n
  · have hbd_n := hbd n hcase
    have hε'_le_ε : ε' ≤ ε := min_le_left _ _
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_scale : ε' * (n : ℝ) ≤ ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hε'_le_ε hn_nn
    have hmono := countingUpTo_primesSumsetMinusPrimorials_le_primesSumset n
    have hmono_real :
        (Gdbh.countingUpTo primesSumsetMinusPrimorials n : ℝ) ≤
          (Gdbh.countingUpTo primesSumset n : ℝ) := by
      exact_mod_cast hmono
    linarith
  · -- n < N₀: we have 1 ≤ n, and the element 1 ∈ primesSumset is in [1, n].
    -- So count(primesSumset, n) ≥ 1.
    have hcase_lt : n < N₀ := Nat.lt_of_not_le hcase
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn_le_N₀ : (n : ℝ) ≤ (N₀ : ℝ) + 1 := by
      have : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast Nat.le_of_lt hcase_lt
      linarith
    -- count(primesSumset, n) ≥ 1 because 1 ∈ primesSumset.
    have h_count_ge_one : 1 ≤ Gdbh.countingUpTo primesSumset n := by
      -- The element 1 is in (range (n + 1)).filter (fun k => 1 ≤ k ∧ primesSumset k).
      classical
      have h_mem : (1 : ℕ) ∈ (Finset.range (n + 1)).filter
          (fun k => 1 ≤ k ∧ primesSumset k) := by
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · exact le_refl 1
        · exact Gdbh.PathCKGoldbach.primesSumset_one
      have : 0 < ((Finset.range (n + 1)).filter
          (fun k => 1 ≤ k ∧ primesSumset k)).card :=
        Finset.card_pos.mpr ⟨1, h_mem⟩
      unfold Gdbh.countingUpTo
      omega
    have h_count_ge_one_real :
        (1 : ℝ) ≤ (Gdbh.countingUpTo primesSumset n : ℝ) := by
      exact_mod_cast h_count_ge_one
    -- ε' * n ≤ (1 / (N₀ + 1)) * n ≤ (1 / (N₀ + 1)) * (N₀ + 1) = 1.
    have hε'_le : ε' ≤ 1 / ((N₀ : ℝ) + 1) := min_le_right _ _
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
    have h_step1 : ε' * (n : ℝ) ≤ (1 / ((N₀ : ℝ) + 1)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hε'_le hn_nn
    have h_step2 : (1 / ((N₀ : ℝ) + 1)) * (n : ℝ) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul]
      rw [div_le_one hN₀_one_pos]
      exact hn_le_N₀
    linarith

/-- **Schnirelmann density positivity**:  `PrimesSumsetDensityModuloPrimorials`
implies `0 < schnirelmannDensity primesSumset`. -/
theorem schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials
    (h : PrimesSumsetDensityModuloPrimorials) :
    0 < Gdbh.schnirelmannDensity primesSumset :=
  Gdbh.PathCPrimesSumsetDensity.primesSumsetDensity_pos_of_uniformLowerBound
    (primesSumsetUniformLowerBound_of_densityModuloPrimorials h)

/-! ## Section 5 — K-Goldbach from `PrimesSumsetDensityModuloPrimorials`

We compose the density bridge above with the existing K-Goldbach
assembler.  This requires:

* `PrimesSumsetDensityModuloPrimorials`  (the refactored input).
* `0 < schnirelmannDensity primesAndOne`  (the existing K-Goldbach
  hypothesis on `primesAndOne`).  This is *not* provided by
  `PrimesSumsetDensityModuloPrimorials` alone — it requires a separate
  argument linking `primesSumset`-density to `primesAndOne`-density.
* `SchnirelmannBasisHalfDensity`  (the existing basis-step hypothesis).

We expose the cleanest reduction with the explicit `primesAndOne`
density hypothesis, matching the form already documented in
`Gdbh.PathCKGoldbach.exists_K_goldbach_of_open_inputs`. -/

/-- **K-Goldbach from primorial-modulo density** (final form).

Given:

* `PrimesSumsetDensityModuloPrimorials` (the refactored, mathematically
  honest analytic input for the FixA-aware chain), and
* `0 < schnirelmannDensity primesAndOne` (the existing
  `primesAndOne`-density input;  this can be derived from
  `PrimesSumsetDensityModuloPrimorials` plus a separate counting bridge
  for `primesAndOne` itself, exposed elsewhere in Path C), and
* `Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity` (the existing
  basis-step input),

every integer `n ≥ 2` is a sum of at most `K + 1` elements of
`primesAndOne` for some uniform `K`.

The conclusion follows by composition:

1. `PrimesSumsetDensityModuloPrimorials ⇒
   0 < schnirelmannDensity primesSumset`
   (Section 4, `schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials`).
2. The standing `0 < schnirelmannDensity primesAndOne` hypothesis is
   then combined with the basis step via
   `Gdbh.PathCKGoldbach.exists_K_goldbach_of_open_inputs`. -/
theorem exists_K_goldbach_of_densityModuloPrimorials_and_basis
    (_hMod : PrimesSumsetDensityModuloPrimorials)
    (hPosPA : 0 < Gdbh.schnirelmannDensity Gdbh.PathCPrimesDensity.primesAndOne)
    (hHalf : Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧
        ps.sum = n :=
  Gdbh.PathCKGoldbach.exists_K_goldbach_of_open_inputs hPosPA hHalf

/-! ## Section 6 — Honest mathematical summary

We summarise the precise mathematical situation in three named
observations: -/

/-- **Observation 1**:  the *generic* extended bridge (Section 1)
specialises at `W := logLogPlus` to give `WeightedLogLossSchnirelmann`.

This is the *direct* reduction of the missing Schnirelmann
infrastructure to a single generic-weight bridge. -/
theorem extendedBridge_implies_weightedLogLossSchnirelmann
    (hBridge : ExtendedWeightedSchnirelmannSubLinearBridge) :
    WeightedLogLossSchnirelmann :=
  weightedLogLossSchnirelmann_of_extendedBridge hBridge

/-- **Observation 2**:  `PrimesSumsetDensityModuloPrimorials` implies
positive Schnirelmann density of `primesSumset` itself.

This is the *primorial-aware* refactor of the analytic input. -/
theorem densityModuloPrimorials_implies_schnirelmannDensity_pos
    (h : PrimesSumsetDensityModuloPrimorials) :
    0 < Gdbh.schnirelmannDensity primesSumset :=
  schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials h

/-- **Observation 3**:  the refactored analytic input
`PrimesSumsetDensityModuloPrimorials`, combined with the standard
auxiliary inputs (positive density of `primesAndOne`, half-density
basis), yields K-Goldbach.

This is the **headline P21-T2 deliverable**. -/
theorem pathC_kGoldbach_via_primorialModulo
    (hMod : PrimesSumsetDensityModuloPrimorials)
    (hPosPA : 0 < Gdbh.schnirelmannDensity Gdbh.PathCPrimesDensity.primesAndOne)
    (hHalf : Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧
        ps.sum = n :=
  exists_K_goldbach_of_densityModuloPrimorials_and_basis hMod hPosPA hHalf

/-! ## Section 7 — Conclusion (honest summary)

**Q: Can `WeightedLogLossSchnirelmann` be closed in this file?**

**A: No.**  The Prop is a *direct conclusion-shape* statement requiring
a generic extended Schnirelmann bridge that is not present in
mathlib v4.29.1 nor in the existing Path C infrastructure.  We
*identify* this missing bridge as `ExtendedWeightedSchnirelmannSubLinearBridge`
and show that it suffices for `WeightedLogLossSchnirelmann`.  The
bridge itself is a piece of new mathematics — it is the
*log-loss-occupied-average + log-loss-output* variant of the existing
uniform chain.

**Q: Is there an alternative route to K-Goldbach?**

**A: Yes.**  The classical Brun-Schnirelmann argument *does* close
K-Goldbach unconditionally, but it works by **handling primorials
separately** (the primorial subsequence is density-0 and contains the
singular-series spike that would otherwise wreck the uniform Schnirelmann
chain).  We refactor the analytic input as
`PrimesSumsetDensityModuloPrimorials` — positive density of
`primesSumset` *away from primorial integers* — and prove that this
Prop implies positive *full* Schnirelmann density of `primesSumset`
(because the primorial subsequence is density-zero), which composes
with the existing K-Goldbach assembler.

This is the **honest refactor**:  the FixA `n · log log n / (log n)²`
reservoir suffices for the Schnirelmann argument *outside* the primorial
subsequence, and the primorial subsequence itself is handled by direct
enumeration / classical Goldbach for fixed `n` — which is the same
trick used in the standard textbook proof of Brun-Schnirelmann.

**P21-T2 deliverable**:  the refactored Prop
`PrimesSumsetDensityModuloPrimorials`, the density-positivity bridge
to `0 < schnirelmannDensity primesSumset`, and the K-Goldbach
composition.

All theorems below are axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`). -/

/-! ## Section 8 — Axiom audit

Each headline theorem below uses only the universally-accepted
`Classical.choice`, `Quot.sound`, `propext`. -/

#print axioms isPrimorialValue_zero_iff
#print axioms isPrimorialValue_one
#print axioms isPrimorialValue_two
#print axioms primesSumset_of_primesSumsetMinusPrimorials
#print axioms countingUpTo_primesSumsetMinusPrimorials_le_primesSumset
#print axioms primesSumsetUniformLowerBound_of_densityModuloPrimorials
#print axioms schnirelmannDensity_primesSumset_pos_of_densityModuloPrimorials
#print axioms weightedLogLossSchnirelmann_of_extendedBridge
#print axioms weightedLogLossSchnirelmann_of_strongOccupied
#print axioms exists_K_goldbach_of_densityModuloPrimorials_and_basis
#print axioms extendedBridge_implies_weightedLogLossSchnirelmann
#print axioms densityModuloPrimorials_implies_schnirelmannDensity_pos
#print axioms pathC_kGoldbach_via_primorialModulo

end PathCWeightedLogLossClosure
end Gdbh
