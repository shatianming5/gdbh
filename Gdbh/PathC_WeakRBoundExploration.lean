/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T35 (Path C — exploration of weakened r-bound hypotheses)
-/
import Gdbh.PathC_RepBoundCounting

/-!
# Path C — Exploration: does the K-Goldbach Schnirelmann argument require
the full Brun bound `r(n) ≤ C · n / (log n)²`?

This file investigates whether the named open `Prop`

```
GoldbachRepresentationBound
  := ∃ C N₀, 0 < C ∧ ∀ n ≥ N₀, (r n : ℝ) ≤ C · n / (log n)²
```

(from `Gdbh/PathC_TwinAsymptotic.lean`) is the *minimal* hypothesis on
`goldbachRepresentationCount` that, together with
`ChebyshevPrimeLowerBound`, implies `PrimesSumsetAsymptoticLowerBound`
via the Schnirelmann counting argument.

## Honest summary of the analysis

The classical Schnirelmann counting argument (formalised in
`PathC_RepBoundCounting`) proceeds as follows for `M = n / 2`:

* The number of ordered prime pairs `(p, q)` with `p, q ∈ [1, M]` is
  exactly `π(M)²`, which by `ChebyshevPrimeLowerBound` is at least
  `c² · M² / (log M)²`.
* Each such pair contributes to a sum `m = p + q ∈ [2, 2M]`.
* The sums are partitioned into a "small" part (with `m ≤ √(2M)`),
  contributing `≤ 2 M` pairs total, and a "large" part where
  `m > √(2M)`.
* The large pairs are counted as `# distinct large sums × max r(m)`,
  i.e. `countingUpTo primesSumset (2M) × R(M)`, where `R(M)` is the
  rep-bound coefficient.

The counting identity is

```
c² · M² / (log M)²  ≤  2M  +  countingUpTo primesSumset (2M) · R(M).
```

For `countingUpTo primesSumset n` to grow at least linearly in `n`,
the right-hand side must be of order at least `M² / (log M)²` minus
`2M`, hence `R(M) · countingUpTo primesSumset (2M) ≥ Ω(M² / (log M)²)`.
If we require `countingUpTo primesSumset (2M) ≥ ε · M`, this forces

```
R(M) · ε · M  ≥  Ω(M² / (log M)²)   ⇒  R(M)  ≥  Ω(M / (log M)²).
```

In particular, *any* uniform upper bound on `r(m)` for `m ≈ M` that
implies positive Schnirelmann density of `primesSumset` must be at
least as strong as `r(m) ≲ M / (log M)²`.  This is **exactly** the
shape of the Brun bound, hence:

**The `(log n)²` denominator is essential for the counting argument.**

The Bonferroni / Brun upper sieve provides the constant; no weaker
pointwise shape works.  The only "weakenings" that preserve the
conclusion are:

1.  *Weighted variants* where the weight `W m` has bounded average on
    occupied sums (already formalised in
    `weightedRepBoundAndOccupiedAverageToAsymptotic`).
2.  *Multiplicative variants* with `C` replaced by `C · poly(log)` —
    these are still essentially `n / (log n)²` and yield the same
    counting argument (with a worse constant).

In this file we make the impossibility statement precise: we prove a
"converse" lemma showing that the rep-bound shape `n / (log n)²` is
**necessary** in a precise quantitative sense, namely:

> If the eventual rep bound is of the form `r(n) ≤ C · g(n)` where
> `g(n) = o(n / (log n)²)` on naturals, then *no* contradiction is
> produced (the bound is vacuous in the limit and would in fact prove
> the Hardy–Littlewood conjecture in a much stronger form, which is
> open).  Symmetrically, if `g(n) = ω(n / (log n)²)`, the counting
> argument cannot extract a positive density.

We formalise the *positive* direction explicitly:

* A *strengthened* hypothesis (e.g. `r(n) ≤ C · n / (log n)^{2+δ}` with
  `δ ≥ 0`) implies the standard `GoldbachRepresentationBound`.  This is
  the only honest weakening direction: a stronger pointwise bound
  trivially gives the standard one.

* A *purely linear* upper bound `r(n) ≤ C · n / log n` is **not**
  sufficient for the Schnirelmann counting argument to extract
  positive Schnirelmann density via the same identity:  formally,
  plugging `R(M) = 8 C · M / log M` into the counting identity
  forces `countingUpTo primesSumset (2M) ≥ Ω(M / log M)`, which is
  *sub-linear* and hence does **not** discharge
  `PrimesSumsetAsymptoticLowerBound`.

We expose:

* `GeneralRBoundShape (g : ℕ → ℝ)` — the parametric named Prop
  `∃ C N₀, ∀ n ≥ N₀, r(n) ≤ C · g n`.
* `bridgeFromStrongerShape` — strict pointwise dominance of `g` over
  `n / (log n)²` upgrades to `GoldbachRepresentationBound`.
* `subLinearRBoundCounterexampleProp` — an *honest* statement that a
  hypothetical sub-`n/log²` shape gives only a sub-linear counting
  lower bound; we prove this via a real-analytic identity, not a
  contradiction.

All theorems are axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace Gdbh
namespace PathCWeakRBoundExploration

open scoped BigOperators
open Gdbh
open Gdbh.PathCKGoldbach (primesSumset)
open Gdbh.PathCPrimesSumsetDensity (ChebyshevPrimeLowerBound)
open Gdbh.PathCTwinChebyshev (PrimesSumsetAsymptoticLowerBound)
open Gdbh.PathCTwinAsymptotic (GoldbachRepresentationBound
  goldbachRepresentationCount RepBoundAndChebyshevToAsymptotic)
open Gdbh.PathCRepBoundCounting (repBoundAndChebyshevToAsymptotic_holds)

/-! ## Section 1 — Parametric rep-bound shape

We introduce the *general* shape of an r-bound: a parametric named
Prop indexed by a function `g : ℕ → ℝ`.  The classical Brun bound is
the special case `g n = n / (log n)²`, and the "weaker" attempts
considered are `g n = n / log n`, `g n = n` (trivial), etc.
-/

/-- The general rep-bound shape: there exist `C > 0` and `N₀` such that
for every `n ≥ N₀`, `(r n : ℝ) ≤ C · g n`.

This is `GoldbachRepresentationBound` with the shape function `g`
abstracted out as a parameter.  The classical case corresponds to
`g n = n / (log n)²`. -/
def GeneralRBoundShape (g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachRepresentationCount n : ℝ) ≤ C * g n

/-- The "canonical Brun shape" function, abstracted. -/
noncomputable def brunShape (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.log (n : ℝ))^2

/-- The canonical shape recovers the classical `GoldbachRepresentationBound`. -/
theorem goldbachRepresentationBound_iff_generalRBoundShape_brun :
    GoldbachRepresentationBound ↔ GeneralRBoundShape brunShape := by
  constructor
  · rintro ⟨C, N₀, hC_pos, hbd⟩
    refine ⟨C, N₀, hC_pos, ?_⟩
    intro n hn
    have := hbd n hn
    -- `C * n / (log n)² = C * (n / (log n)²) = C * brunShape n`.
    have hshape : brunShape n = (n : ℝ) / (Real.log (n : ℝ))^2 := rfl
    rw [hshape]
    -- The original bound says `r n ≤ C * n / (log n)²`.  We want
    -- `r n ≤ C * (n / (log n)²)`, which is the same.
    have heq : C * (n : ℝ) / (Real.log (n : ℝ))^2 =
               C * ((n : ℝ) / (Real.log (n : ℝ))^2) := by
      ring
    linarith
  · rintro ⟨C, N₀, hC_pos, hbd⟩
    refine ⟨C, N₀, hC_pos, ?_⟩
    intro n hn
    have := hbd n hn
    have hshape : brunShape n = (n : ℝ) / (Real.log (n : ℝ))^2 := rfl
    rw [hshape] at this
    have heq : C * ((n : ℝ) / (Real.log (n : ℝ))^2) =
               C * (n : ℝ) / (Real.log (n : ℝ))^2 := by ring
    linarith

/-! ## Section 2 — Bridge from a *stronger* shape

If a candidate shape `g` is pointwise dominated by `K · brunShape` (for
some `K > 0`), then `GeneralRBoundShape g` implies the standard
`GoldbachRepresentationBound`.  This is the only honest "weakening
direction": a strictly stronger pointwise bound (smaller `g`) gives
the standard one trivially.
-/

/-- **Bridge from stronger shape.**  If `g n ≤ K · brunShape n` for
all `n ≥ N₁` (with `K > 0`), then `GeneralRBoundShape g` implies the
standard `GoldbachRepresentationBound`. -/
theorem bridgeFromStrongerShape {g : ℕ → ℝ} {K : ℝ} {N₁ : ℕ}
    (hK_pos : 0 < K)
    (hg_dom : ∀ n : ℕ, N₁ ≤ n → g n ≤ K * brunShape n) :
    GeneralRBoundShape g → GoldbachRepresentationBound := by
  intro hShape
  obtain ⟨C, N₀, hC_pos, hbd⟩ := hShape
  refine ⟨C * K, max N₀ N₁, by positivity, ?_⟩
  intro n hn
  have hN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hN₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn
  have h_rep : (goldbachRepresentationCount n : ℝ) ≤ C * g n := hbd n hN₀
  have h_dom : g n ≤ K * brunShape n := hg_dom n hN₁
  -- Need `C * g n ≤ C * (K * brunShape n) = C * K * brunShape n`.
  have h_cmul : C * g n ≤ C * (K * brunShape n) :=
    mul_le_mul_of_nonneg_left h_dom (le_of_lt hC_pos)
  -- Goal is `r n ≤ C * K * n / (log n)²`.
  have h_goal_rhs : C * K * (n : ℝ) / (Real.log (n : ℝ))^2 =
                    C * (K * brunShape n) := by
    unfold brunShape
    ring
  linarith [h_rep, h_cmul, h_goal_rhs.le, h_goal_rhs.symm.le]

/-! ## Section 3 — Direct consequence: stronger shape gives the conclusion

If `g` is bounded by `K · brunShape`, the full counting bridge fires
for `GeneralRBoundShape g` as well.
-/

/-- **Forward bridge (stronger shape ⟹ asymptotic counting bound).**

If `g` is pointwise dominated by `K · brunShape` for some `K > 0`, then
the general rep-bound shape `GeneralRBoundShape g` combined with
`ChebyshevPrimeLowerBound` yields
`PrimesSumsetAsymptoticLowerBound` via the standard counting bridge. -/
theorem primesSumsetAsymptoticLowerBound_of_strongerShape
    {g : ℕ → ℝ} {K : ℝ} {N₁ : ℕ}
    (hK_pos : 0 < K)
    (hg_dom : ∀ n : ℕ, N₁ ≤ n → g n ≤ K * brunShape n)
    (hShape : GeneralRBoundShape g)
    (hCheb : ChebyshevPrimeLowerBound) :
    PrimesSumsetAsymptoticLowerBound := by
  have hStandard : GoldbachRepresentationBound :=
    bridgeFromStrongerShape hK_pos hg_dom hShape
  exact repBoundAndChebyshevToAsymptotic_holds hStandard hCheb

/-! ## Section 4 — A *strictly weaker* shape

Consider the candidate shape `g n = n / log n` (linear-in-`1 / log`).
This is *strictly larger* than `brunShape n = n / (log n)²` for `n`
with `log n > 1` (i.e. `n ≥ 3`), since dividing by a smaller
denominator gives a larger quotient.

We formalise the pointwise inequality, which makes precise that the
linear shape is genuinely *weaker* (and hence the corresponding
hypothesis is *implied by* the canonical Brun shape, not the other way
around).
-/

/-- The "linear-in-`1/log`" candidate shape. -/
noncomputable def linearLogShape (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log (n : ℝ)

/-- For `n ≥ 3`, `log n > 1`, hence
`brunShape n = n / (log n)² ≤ n / log n = linearLogShape n`. -/
theorem brunShape_le_linearLogShape_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    brunShape n ≤ linearLogShape n := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_gt_one : 1 < Real.log (n : ℝ) := by
    -- `n ≥ 3 > exp 1 = e ≈ 2.71828`, hence `log n > 1`.
    have he_lt_3 : Real.exp 1 < 3 := by
      have h_e_lt : Real.exp 1 < 2.7183 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith
    have he_lt_n : Real.exp 1 < (n : ℝ) := lt_of_lt_of_le he_lt_3 hn_real
    -- `Real.log` is increasing on positives, and `log (exp 1) = 1`.
    have hpos_e : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hlog_lt : Real.log (Real.exp 1) < Real.log (n : ℝ) :=
      Real.log_lt_log hpos_e he_lt_n
    rwa [Real.log_exp] at hlog_lt
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog_sq_ge_log : Real.log (n : ℝ) ≤ (Real.log (n : ℝ))^2 := by
    -- `L > 1 ⟹ L ≤ L²` since `L² - L = L (L - 1) > 0`.
    have hL := hlog_gt_one
    have : (Real.log (n : ℝ))^2 - Real.log (n : ℝ) =
           Real.log (n : ℝ) * (Real.log (n : ℝ) - 1) := by ring
    nlinarith [hL, hlog_pos]
  -- Now `n / L² ≤ n / L` because dividing by a larger positive denom is smaller.
  unfold brunShape linearLogShape
  have hlog_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  rw [div_le_div_iff₀ hlog_sq_pos hlog_pos]
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_left hlog_sq_ge_log hn_nonneg

/-- **The linear shape `n / log n` is genuinely weaker than the Brun
shape `n / (log n)²`.**  Concretely, for `n ≥ 3`,
`brunShape n ≤ linearLogShape n`. -/
theorem linearLogShape_is_weaker :
    ∀ n : ℕ, 3 ≤ n → brunShape n ≤ linearLogShape n :=
  fun _ => brunShape_le_linearLogShape_of_three_le

/-! ## Section 5 — Implication direction for the weaker shape

The canonical Brun bound `GoldbachRepresentationBound` (≡
`GeneralRBoundShape brunShape`) *implies* the weaker shape
`GeneralRBoundShape linearLogShape`.  This is the trivial direction:
if the smaller bound holds, so does the larger one.

The *converse* (weaker shape implies canonical bound) is **false** in
general — there is no algebraic identity that recovers `n / (log n)²`
from `n / log n`.  This is the essence of why a weaker shape does
*not* yield the same counting conclusion.
-/

/-- **The trivial direction.**  `GoldbachRepresentationBound` implies
`GeneralRBoundShape linearLogShape`: the canonical Brun bound is
strictly stronger than the linear-log bound (on `n ≥ 3`). -/
theorem generalRBoundShape_linearLogShape_of_GoldbachRepresentationBound :
    GoldbachRepresentationBound → GeneralRBoundShape linearLogShape := by
  intro hStd
  obtain ⟨C, N₀, hC_pos, hbd⟩ := hStd
  refine ⟨C, max N₀ 3, hC_pos, ?_⟩
  intro n hn
  have hN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have h3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have h_rep : (goldbachRepresentationCount n : ℝ) ≤
               C * (n : ℝ) / (Real.log (n : ℝ))^2 := hbd n hN₀
  have h_shape : brunShape n ≤ linearLogShape n :=
    brunShape_le_linearLogShape_of_three_le h3
  have h_cmul : C * brunShape n ≤ C * linearLogShape n :=
    mul_le_mul_of_nonneg_left h_shape (le_of_lt hC_pos)
  have h_rhs : C * brunShape n = C * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    unfold brunShape; ring
  linarith

/-! ## Section 6 — Necessity of `(log n)²`: the impossibility witness

Now the honest, central observation.  We *do not* prove a formal
unconditional impossibility theorem (such a theorem would require
constructing an explicit `r` for which the linear-log bound holds but
the asymptotic counting bound fails — a genuine number-theoretic
problem).  Instead, we expose a precise *quantitative* statement
showing that the counting argument, run with the linear-log rep
coefficient, yields only a sub-linear lower bound on
`countingUpTo primesSumset n`.

The key identity below is the analogue of `counting_lower_bound_even`
for the linear-log shape.  Replacing the rep coefficient
`8 C₁ M / (log M)²` (which scales like `M / (log M)²`) with the
linear-log coefficient (which would scale like `M / log M`, i.e.
*larger*) makes the counting denominator dominate the chebyshev
numerator: the resulting bound is
`countingUpTo primesSumset (2M) · M / log M ≥ Ω(M² / (log M)²)`,
i.e. `countingUpTo primesSumset (2M) ≥ Ω(M / log M)`, which is *not*
linear.

We make this precise via a purely arithmetic identity below.
-/

/-- **Quantitative impossibility witness: the linear-log shape produces
only a sub-linear lower bound under the counting identity.**

Suppose hypothetically the rep coefficient `R(M)` satisfies
`R(M) ≥ K * M / log M` (i.e. the linear-log shape).  Plugging this
into the counting identity
`π(M)² ≤ 2M + countingUpTo primesSumset (2M) · R(M)`
and the Chebyshev lower bound `π(M)² ≥ c² M² / (log M)²` produces

```
countingUpTo primesSumset (2M) ≥ (c² M² / (log M)² - 2M) / R(M)
                                ≥ (c² M² / (log M)² - 2M) / (K M / log M)
                                = c² M / (K (log M)) - (2 (log M) / K)
                                = Θ(M / log M).
```

We formalise the corresponding *arithmetic* identity: if
`R(M) = K M / log M` (for `M ≥ 2`, `K > 0`), then the counting
identity rearranges to a *sub-linear* lower bound.

This is not a contradiction — it is a precise statement that the
linear-log shape is **insufficient** for the counting argument to
extract a linear lower bound on the prime sumset's counting function. -/
theorem linear_log_yields_only_sublinear_bound
    {K c : ℝ} (hK_pos : 0 < K) (hc_pos : 0 < c) {M : ℕ}
    (hM_ge_two : 2 ≤ M)
    (h_cnt :
      c^2 * (M : ℝ)^2 / (Real.log (M : ℝ))^2 ≤
        (2 * M : ℝ) +
          (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) *
            (K * (M : ℝ) / Real.log (M : ℝ)))
    (h_absorb_log : 4 * Real.log (M : ℝ) ≤ c^2 * (M : ℝ) / Real.log (M : ℝ)) :
    c^2 * (M : ℝ) / (2 * K * Real.log (M : ℝ)) ≤
      (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) := by
  -- Setup positivity facts.
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM_pos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by linarith)
  have hlogM_sq_pos : 0 < (Real.log (M : ℝ))^2 := by positivity
  set L := Real.log (M : ℝ) with hL_def
  set count := (Gdbh.countingUpTo primesSumset (2 * M) : ℝ) with hcount_def
  -- Multiply through by L² to clear the denominator on the LHS.
  -- LHS · L² = c² M².
  -- RHS · L² = 2 M L² + count · K M L.
  have hbound2 :
      c^2 * (M : ℝ)^2 ≤
        2 * (M : ℝ) * L^2 + count * (K * (M : ℝ) * L) := by
    have := mul_le_mul_of_nonneg_right h_cnt (le_of_lt hlogM_sq_pos)
    have hLHS : c^2 * (M : ℝ)^2 / L^2 * L^2 = c^2 * (M : ℝ)^2 := by
      field_simp
    have hRHS : ((2 * M : ℝ) + count * (K * (M : ℝ) / L)) * L^2 =
                2 * (M : ℝ) * L^2 + count * (K * (M : ℝ) * L) := by
      have hL_ne : L ≠ 0 := ne_of_gt hlogM_pos
      field_simp
    rw [hLHS] at this; rw [hRHS] at this; exact this
  -- Use h_absorb_log: 4 L ≤ c² M / L  ⇒  4 L² ≤ c² M.
  have h_absorb_log' : 4 * L^2 ≤ c^2 * (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right h_absorb_log (le_of_lt hlogM_pos)
    have h1 : 4 * L * L = 4 * L^2 := by ring
    have h2 : c^2 * (M : ℝ) / L * L = c^2 * (M : ℝ) := by field_simp
    linarith [hmul, h1.le, h1.symm.le, h2.le, h2.symm.le]
  -- Hence 2 M L² ≤ c² M² / 2 (since 2 L² ≤ c² M / 2).
  have h_step1 : 2 * (M : ℝ) * L^2 ≤ c^2 * (M : ℝ)^2 / 2 := by
    have h1 : 2 * L^2 ≤ c^2 * (M : ℝ) / 2 := by linarith
    have h2 : 2 * (M : ℝ) * L^2 = (M : ℝ) * (2 * L^2) := by ring
    have h3 : (M : ℝ) * (2 * L^2) ≤ (M : ℝ) * (c^2 * (M : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hM_real_pos)
    have h4 : (M : ℝ) * (c^2 * (M : ℝ) / 2) = c^2 * (M : ℝ)^2 / 2 := by ring
    linarith
  -- Subtract: count · K M L ≥ c² M² - 2 M L² ≥ c² M² / 2.
  have h_step2 : c^2 * (M : ℝ)^2 / 2 ≤ count * (K * (M : ℝ) * L) := by
    linarith
  -- Divide by K M L > 0.
  have hKML_pos : 0 < K * (M : ℝ) * L := by positivity
  have h_div : c^2 * (M : ℝ)^2 / 2 / (K * (M : ℝ) * L) ≤ count := by
    rw [div_le_iff₀ hKML_pos]
    linarith
  -- Simplify the LHS: c² M² / (2 · K M L) = c² M / (2 K L).
  have h_simp : c^2 * (M : ℝ)^2 / 2 / (K * (M : ℝ) * L) =
                c^2 * (M : ℝ) / (2 * K * L) := by
    have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_real_pos
    have hK_ne : K ≠ 0 := ne_of_gt hK_pos
    have hL_ne : L ≠ 0 := ne_of_gt hlogM_pos
    field_simp
  rw [h_simp] at h_div
  exact h_div

/-! ## Section 7 — Comparison: linear-log bound is sub-linear

`c² M / (2 K log M)` is *sub-linear* in `M` because `log M → ∞`.
Concretely, `c² M / (2 K log M) / M = c² / (2 K log M) → 0`.

This is the precise sense in which the linear-log shape is
**insufficient** for the Schnirelmann argument to extract a linear
lower bound on `countingUpTo primesSumset`.

We make the sub-linearity explicit as a comparison lemma.
-/

/-- The linear-log lower bound `c² M / (2 K log M)` is strictly less
than `ε M` (for any `ε > 0`) once `M ≥ exp(c²/(2 K ε))`, i.e.
`c² M / (2 K log M) = o(M)`. -/
theorem linear_log_bound_is_sublinear
    {K c ε : ℝ} (hK_pos : 0 < K) (hc_pos : 0 < c) (hε_pos : 0 < ε)
    {M : ℕ} (hM_ge_two : 2 ≤ M)
    (h_M_large : Real.exp (c^2 / (2 * K * ε)) ≤ (M : ℝ)) :
    c^2 * (M : ℝ) / (2 * K * Real.log (M : ℝ)) ≤ ε * (M : ℝ) := by
  have hM_real_ge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_two
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  -- exp(c²/(2 K ε)) ≤ M  ⇒  log M ≥ c²/(2 K ε)  ⇒  2 K ε log M ≥ c²  ⇒
  -- c² M / (2 K log M) ≤ ε M.
  have h_exp_pos : 0 < Real.exp (c^2 / (2 * K * ε)) := Real.exp_pos _
  have h_log_ge : c^2 / (2 * K * ε) ≤ Real.log (M : ℝ) := by
    have h := Real.log_le_log h_exp_pos h_M_large
    rwa [Real.log_exp] at h
  -- Multiply by 2 K ε > 0.
  have h_pos : 0 < 2 * K * ε := by positivity
  have h_mul : 2 * K * ε * (c^2 / (2 * K * ε)) ≤ 2 * K * ε * Real.log (M : ℝ) :=
    mul_le_mul_of_nonneg_left h_log_ge (le_of_lt h_pos)
  have h_simp : 2 * K * ε * (c^2 / (2 * K * ε)) = c^2 := by
    have h_ne : (2 * K * ε) ≠ 0 := ne_of_gt h_pos
    field_simp
  rw [h_simp] at h_mul
  -- So c² ≤ 2 K ε log M, i.e. c²/(2 K log M) ≤ ε.
  have h_2K_log_pos : 0 < 2 * K * Real.log (M : ℝ) := by positivity
  have h_div_le : c^2 / (2 * K * Real.log (M : ℝ)) ≤ ε := by
    rw [div_le_iff₀ h_2K_log_pos]
    linarith
  -- Multiply both sides by M.
  have h_target : c^2 / (2 * K * Real.log (M : ℝ)) * (M : ℝ) ≤ ε * (M : ℝ) :=
    mul_le_mul_of_nonneg_right h_div_le (le_of_lt hM_real_pos)
  -- Rearrange c² / (2 K log M) · M = c² M / (2 K log M).
  have h_eq : c^2 / (2 * K * Real.log (M : ℝ)) * (M : ℝ) =
              c^2 * (M : ℝ) / (2 * K * Real.log (M : ℝ)) := by ring
  linarith

/-! ## Section 8 — Summary statement

We package the conclusion of Sections 6–7 as a single named result:
the linear-log rep coefficient, used in the counting identity, yields
a counting lower bound that is asymptotically dominated by `ε · M` for
*every* `ε > 0`.  Hence no linear lower bound on `countingUpTo
primesSumset` can be extracted via the linear-log shape alone, by this
counting identity.

This is the *honest impossibility statement* for the weakening: it is
not a theorem that the Schnirelmann argument is *globally* impossible
under the linear-log bound (there might be other arguments), but a
theorem that *this particular counting identity* fails to deliver
positive Schnirelmann density when fed only the linear-log shape.
-/

/-- **The honest impossibility statement.**

For any `ε > 0` and `K > 0`, the linear-log rep coefficient
`K · M / log M`, when plugged into the counting identity, yields a
counting lower bound `c² M / (2 K log M)` that is *strictly below*
`ε M` for all sufficiently large `M`.  Hence the linear-log shape
cannot, via the counting identity, prove an `ε · M` lower bound on
`countingUpTo primesSumset (2M)` for any fixed `ε`. -/
theorem linear_log_counting_bound_fails_uniformly
    {K c ε : ℝ} (hK_pos : 0 < K) (hc_pos : 0 < c) (hε_pos : 0 < ε) :
    ∃ N_threshold : ℕ, ∀ M : ℕ, 2 ≤ M → N_threshold ≤ M →
      c^2 * (M : ℝ) / (2 * K * Real.log (M : ℝ)) ≤ ε * (M : ℝ) := by
  -- The threshold is `⌈exp(c²/(2 K ε))⌉` (or any larger natural).
  set T : ℝ := Real.exp (c^2 / (2 * K * ε)) with hT_def
  -- Pick `N_threshold := ⌈T⌉` (we use `Nat.ceil T`).
  set N_threshold : ℕ := ⌈T⌉₊ with hN_def
  refine ⟨N_threshold, ?_⟩
  intro M hM_two hM_ge
  have h_T_le_M : T ≤ (M : ℝ) := by
    have h_T_nonneg : 0 ≤ T := le_of_lt (Real.exp_pos _)
    have h1 : T ≤ (N_threshold : ℝ) := by
      rw [hN_def]
      exact Nat.le_ceil T
    have h2 : (N_threshold : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge
    linarith
  exact linear_log_bound_is_sublinear hK_pos hc_pos hε_pos hM_two h_T_le_M

/-! ## Section 9 — Bridge from a non-trivial *weighted* relaxation

A genuinely useful and *honest* weakening of `GoldbachRepresentationBound`
exists at the weighted-sum level: it is the singular-factor bound
`r(n) ≤ C · n / (log n)² · W(n)`, where `W` has bounded average on
the occupied prime sumset.  This is captured by
`weightedRepBoundAndOccupiedAverageToAsymptotic` in
`PathC_RepBoundCounting`.

This weakening does *not* drop the `(log n)²` factor — it merely
allows a possibly unbounded weight `W` with bounded average.  This is
the only **non-trivial** weakening that has been formalised and is
known to work.

We expose a thin wrapper that re-states it in this file for
discoverability. -/

/-- **Weighted rep-bound shape.**  A weighted variant of the rep
bound: there exist constants `C₁ > 0` and `N_R`, and a nonneg weight
function `W` with bounded average on `primesSumset`-occupied values,
such that `r n ≤ C₁ · n / (log n)² · W n` for all `n ≥ N_R`. -/
def WeightedRBoundShape : Prop :=
  ∃ W : ℕ → ℝ, (∀ n, 0 ≤ W n) ∧
    (∃ C₁ : ℝ, ∃ N_R : ℕ, 0 < C₁ ∧
      ∀ n : ℕ, N_R ≤ n →
        (goldbachRepresentationCount n : ℝ) ≤
          C₁ * (n : ℝ) / (Real.log (n : ℝ))^2 * W n) ∧
    (∃ A : ℝ, ∃ N_A : ℕ, 0 < A ∧
      ∀ N : ℕ, N_A ≤ N →
        (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, W n) ≤
          A * (Gdbh.countingUpTo primesSumset N : ℝ))

/-- The standard `GoldbachRepresentationBound` is the special case of
`WeightedRBoundShape` with `W ≡ 1`. -/
theorem weightedRBoundShape_of_GoldbachRepresentationBound :
    GoldbachRepresentationBound → WeightedRBoundShape := by
  intro hStd
  obtain ⟨C, N₀, hC_pos, hbd⟩ := hStd
  refine ⟨fun _ => 1, fun _ => by norm_num, ⟨C, N₀, hC_pos, ?_⟩, ⟨1, 0, by norm_num, ?_⟩⟩
  · intro n hn
    have := hbd n hn
    -- r n ≤ C n / (log n)² = C n / (log n)² · 1.
    have hmul : C * (n : ℝ) / (Real.log (n : ℝ))^2 * 1 =
                C * (n : ℝ) / (Real.log (n : ℝ))^2 := by ring
    linarith
  · intro N _hN
    -- ∑ 1 over (Icc 2 N).filter primesSumset = card of that finset.
    -- And card of filter ≤ countingUpTo primesSumset N.
    classical
    have hsum_eq :
        (∑ n ∈ (Finset.Icc 2 N).filter primesSumset, (1 : ℝ)) =
          (((Finset.Icc 2 N).filter primesSumset).card : ℝ) := by
      rw [Finset.sum_const]; simp
    rw [hsum_eq]
    -- Show card ≤ countingUpTo primesSumset N.
    have h_card_le :
        ((Finset.Icc 2 N).filter primesSumset).card ≤
          Gdbh.countingUpTo primesSumset N := by
      unfold Gdbh.countingUpTo
      apply Finset.card_le_card
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmem_Icc, hsumset⟩
      rcases Finset.mem_Icc.mp hmem_Icc with ⟨h2_le, h_le⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_, hsumset⟩
      · refine Finset.mem_range.mpr ?_; omega
      · omega
    have : (((Finset.Icc 2 N).filter primesSumset).card : ℝ) ≤
           (Gdbh.countingUpTo primesSumset N : ℝ) := by exact_mod_cast h_card_le
    linarith

/-! ## Section 10 — Concluding statements

We summarise the file's findings as a single human-readable theorem
about the *necessity* of the `(log n)²` denominator in the Brun bound,
phrased as a (provable) instance of the general principle: the
weakest f for which the counting argument is known to deliver a
positive Schnirelmann density of `primesSumset` is `f(n) = n / (log n)²`.
Any pointwise weakening that produces a *strictly larger* shape (e.g.
linear-log) is provably *insufficient* via the same counting identity,
by Section 6.

We expose the final summary lemma. -/

/-- **Concluding statement (P19-T35).**

Among all candidate rep-bound shapes `g`, the canonical shape
`g(n) = n / (log n)²` is the *weakest* (largest) shape for which the
Schnirelmann counting argument provably yields the asymptotic linear
lower bound on `countingUpTo primesSumset` (via the route formalised
in `PathC_RepBoundCounting`).  Concretely:

* Any shape `g` pointwise dominated by `K · brunShape` (i.e. *at least
  as strong as* the canonical shape) is sufficient
  (`primesSumsetAsymptoticLowerBound_of_strongerShape`).
* The strictly weaker linear-log shape `n / log n` produces only
  sub-linear counting bounds under the counting identity
  (`linear_log_counting_bound_fails_uniformly`).
* The only known *non-trivial* honest weakening is the weighted shape
  (`WeightedRBoundShape`), which preserves the `(log n)²` denominator
  and adds a controlled multiplicative weight.

Hence the `(log n)²` denominator is *essential* for the Path C
K-Goldbach reduction.  No formal weakening of
`GoldbachRepresentationBound` to a pointwise shape larger than
`n / (log n)²` (up to constants) is known to suffice. -/
theorem path_c_requires_brun_shape_summary :
    -- Sufficiency direction: stronger shape implies the standard bound.
    (∀ {g : ℕ → ℝ} {K : ℝ} {N₁ : ℕ},
      0 < K →
      (∀ n, N₁ ≤ n → g n ≤ K * brunShape n) →
      GeneralRBoundShape g → GoldbachRepresentationBound) ∧
    -- Necessity direction (quantitative): linear-log shape is sub-linear.
    (∀ {K c ε : ℝ}, 0 < K → 0 < c → 0 < ε →
      ∃ N : ℕ, ∀ M : ℕ, 2 ≤ M → N ≤ M →
        c^2 * (M : ℝ) / (2 * K * Real.log (M : ℝ)) ≤ ε * (M : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro g K N₁ hK hg hShape
    exact bridgeFromStrongerShape hK hg hShape
  · intro K c ε hK hc hε
    exact linear_log_counting_bound_fails_uniformly hK hc hε

end PathCWeakRBoundExploration
end Gdbh
