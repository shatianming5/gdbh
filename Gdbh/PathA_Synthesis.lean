import Gdbh.PathA
import Gdbh.DiscreteCircleMethod
import Gdbh.VonMangoldtGoldbach
import Gdbh.SingularSeries

/-!
# Path A — Circle-method synthesis to Hardy-Littlewood

This file develops the structural side of the Hardy-Littlewood circle-method
synthesis under the GRH-style hypotheses of `Gdbh.PathA`:

```
PsiSquareRootErrorBound →
  MinorArcCosineSumBound →
    MajorArcEstimate →
      ∃ T δ, δ < 1 ∧ QuarterBinaryHardyLittlewoodLowerBound T δ
```

## Mathematical sketch

Hardy-Littlewood's binary circle method writes the raw von Mangoldt
Goldbach convolution

```
Raw(n) = Σ_{m=0}^{n} Λ(m) Λ(n-m)
```

as `Raw = MajorContribution + MinorContribution`, where the major
contribution is the integral of `|S(α)|² · e(-nα)` over a union of small
arcs near rational points `a/q` of small denominator, and the minor
contribution is the integral over the complement.  The major arc gives
`𝔖(n) · n + O(n/log²n)` (Hardy-Littlewood asymptotic), and the minor arc
is `o(n)` under a Vinogradov-style cosine sum bound.

This file's contribution (axiom-clean):

* `realMajorContribution` / `realMinorContribution` — real-valued
  major/minor pieces packaged from the discrete Fourier decomposition.
* `rawVonMangoldtGoldbachSum_eq_real_major_add_minor` — the real
  arithmetic identity `Raw = Major + Minor` derived from the discrete
  circle method's Fourier decomposition.
* `PathAHardyLittlewoodMajorArcLowerBound` — the **structural Prop**
  packaging the quantitative output of a major arc analysis: a lower
  bound on `MajorContribution(n)` by `(1 - δ/2) · 𝔖(n) · n` for large
  `n`.  This is the missing analytical content beyond the placeholder
  `MajorArcEstimate`.
* `pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub` — the
  **synthesis theorem**: given a major-arc lower bound + minor-arc
  upper bound + total error bound, the quarter HL conclusion follows.
* `pathA_analyticImplication_of_hardyLittlewoodMajorArcLowerBound` —
  packaging this as `PathA_AnalyticImplication` modulo the additional
  ingredient.

## What is openly left

The hypothesis `PathAHardyLittlewoodMajorArcLowerBound` records the
quantitative content of the major-arc estimate that the placeholder
`MajorArcEstimate` in `Gdbh.PathA` does not yet capture (the placeholder
has a `True` body for the body-quantifier).  It is an *explicit*
hypothesis; it is **not** an axiom of the development.
-/

namespace Gdbh

open DiscreteCircleMethod
open scoped ArithmeticFunction
open Filter Real

/-! ## Section 1: Major and minor contributions as real functions -/

/-- The real-valued **major-arc contribution** to the binary Goldbach
convolution, packaged as the real part of the complex Fourier major arc
sum over the chosen family of major arcs in `ZMod (n+1)`.  This is the
canonical "Hardy-Littlewood main term" once the rationals near `a/q`
with small denominator have been integrated. -/
noncomputable def realMajorContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℝ :=
  rawVonMangoldtFourierMajorArcContribution majorArcs n

/-- The real-valued **minor-arc contribution** to the binary Goldbach
convolution, packaged as the real part of the complex Fourier minor arc
sum.  Under Vinogradov-style cosine sum bounds this is `o(n)`. -/
noncomputable def realMinorContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℝ :=
  rawVonMangoldtFourierMinorArcContribution majorArcs n

/-! ## Section 2: Real arithmetic decomposition identity -/

/-- **Real arithmetic identity** linking the raw von Mangoldt Goldbach
sum to the (real) major + minor Fourier decomposition.  This is the
"real-to-discrete bridge" — direct corollary of the discrete
circle-method identity from `Gdbh.DiscreteCircleMethod`. -/
theorem rawVonMangoldtGoldbachSum_eq_real_major_add_minor
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    RawVonMangoldtGoldbachSum n =
      realMajorContribution majorArcs n +
        realMinorContribution majorArcs n :=
  rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor majorArcs n

/-! ## Section 3: Structural Prop: quantitative major-arc lower bound

The placeholder `MajorArcEstimate` in `Gdbh.PathA` is currently
`∃ C N₀ > 0, ∀ n ≥ N₀ even, True`, which provides no quantitative
content.  The genuine output of a major-arc analysis is a *lower bound*
on `MajorContribution(n)` by `(1 - δ_M) · 𝔖(n) · n` for some `δ_M < 1`
and `n` large.  We package this as a structural Prop and use it as
the missing ingredient in the synthesis below. -/

/-- **Structural quantitative major-arc lower bound**: there exist a
choice of major arcs `majorArcs`, a threshold `N₀`, and a constant
`δ_M ∈ [0, 1)` such that for every even `n > N₀`, the real major-arc
contribution dominates `(1 - δ_M) · 𝔖(n) · n`.  This is the
quantitative output of the Hardy-Littlewood major arc analysis. -/
def PathAHardyLittlewoodMajorArcLowerBound : Prop :=
  ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
    ∃ N₀ : Nat, ∃ δ_M : ℝ, 0 ≤ δ_M ∧ δ_M < 1 ∧
      ∀ n : Nat, N₀ < n → Even n →
        (1 - δ_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
          realMajorContribution majorArcs n

/-- **Structural quantitative minor-arc upper bound**: with the same
choice of major arcs, for some threshold `N₁` and constant `δ_m ∈
[0, 1)`, the real minor-arc contribution is bounded in absolute value
by `δ_m · 𝔖(n) · n` for even `n > N₁`. -/
def PathAHardyLittlewoodMinorArcUpperBound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) : Prop :=
  ∃ N₁ : Nat, ∃ δ_m : ℝ, 0 ≤ δ_m ∧
    ∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-! ## Section 4: Synthesis -- major LB + minor UB → Hardy-Littlewood -/

/-- **Core synthesis arithmetic**: if `Raw = M + m`, `(1 - δ_M)·𝔖·n ≤ M`
and `|m| ≤ δ_m·𝔖·n`, then `(1 - δ_M - δ_m)·𝔖·n ≤ Raw`.  Real
arithmetic only — no analytic content. -/
theorem quarter_lower_bound_of_major_lb_and_minor_ub_pointwise
    {n : Nat} {M m S : ℝ} {δ_M δ_m : ℝ}
    (hSnn : 0 ≤ S)
    (hraw_eq : RawVonMangoldtGoldbachSum n = M + m)
    (hmajor : (1 - δ_M) * (S * (n : ℝ)) ≤ M)
    (hminor : |m| ≤ δ_m * (S * (n : ℝ))) :
    (1 - (δ_M + δ_m)) * (S * (n : ℝ)) ≤
      RawVonMangoldtGoldbachSum n := by
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hSn_nn : (0 : ℝ) ≤ S * (n : ℝ) := mul_nonneg hSnn hn_nn
  have h_neg_abs_le_m : -|m| ≤ m := neg_abs_le m
  have hm_lb : -(δ_m * (S * (n : ℝ))) ≤ m := by
    have : -|m| ≤ m := neg_abs_le m
    have h2 : -(δ_m * (S * (n : ℝ))) ≤ -|m| := by linarith
    linarith
  have hsum : (1 - δ_M) * (S * (n : ℝ)) - δ_m * (S * (n : ℝ)) ≤
      M + m := by linarith
  have hfactor :
      (1 - (δ_M + δ_m)) * (S * (n : ℝ)) =
        (1 - δ_M) * (S * (n : ℝ)) - δ_m * (S * (n : ℝ)) := by ring
  rw [hfactor, hraw_eq]
  exact hsum

/-- **Synthesis theorem**: given a major-arc lower bound and a matching
minor-arc upper bound (sharing the same `majorArcs` choice), the
quarter binary Hardy-Littlewood lower bound holds with combined
relative error `δ = δ_M + δ_m`, provided `δ_M + δ_m < 1`. -/
theorem pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {N₀ N₁ : Nat} {δ_M δ_m : ℝ}
    (_hδ_M_nn : 0 ≤ δ_M) (_hδ_M_lt : δ_M < 1)
    (_hδ_m_nn : 0 ≤ δ_m)
    (_hsum_lt : δ_M + δ_m < 1)
    (hmajor : ∀ n : Nat, N₀ < n → Even n →
      (1 - δ_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
        realMajorContribution majorArcs n)
    (hminor : ∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) :
    QuarterBinaryHardyLittlewoodLowerBound (max N₀ N₁) (δ_M + δ_m) := by
  intro n hn hEven
  have hN₀_lt : N₀ < n :=
    lt_of_le_of_lt (le_max_left N₀ N₁) hn
  have hN₁_lt : N₁ < n :=
    lt_of_le_of_lt (le_max_right N₀ N₁) hn
  have hMajor := hmajor n hN₀_lt hEven
  have hMinor := hminor n hN₁_lt hEven
  have hraw_eq :
      RawVonMangoldtGoldbachSum n =
        realMajorContribution majorArcs n +
          realMinorContribution majorArcs n :=
    rawVonMangoldtGoldbachSum_eq_real_major_add_minor majorArcs n
  have hSnn : 0 ≤ goldbachSingularSeriesFromQuarter n := by
    by_cases h2 : 2 < n
    · -- Use 1/4 ≤ 𝔖 for n > 0 even via the existing lemma
      have hn_pos : 0 < n := by omega
      have h14 :
          (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
        one_fourth_le_goldbachSingularSeriesFromQuarter
          (threshold := 0) n hn_pos hEven
      linarith
    · -- For tiny n, unfold using nonneg base * nonneg multiplier.
      dsimp [goldbachSingularSeriesFromQuarter,
        goldbachSingularSeriesFromBase,
        goldbachSingularSeriesQuarterBase]
      have hmul_nn : 0 ≤ goldbachSingularSeriesLocalMultiplier n :=
        le_trans (by norm_num : (0 : ℝ) ≤ 1)
          (one_le_goldbachSingularSeriesLocalMultiplier n)
      have : 0 ≤ (1 / 4 : ℝ) * goldbachSingularSeriesLocalMultiplier n :=
        mul_nonneg (by norm_num) hmul_nn
      exact this
  exact quarter_lower_bound_of_major_lb_and_minor_ub_pointwise
    hSnn hraw_eq hMajor hMinor

/-! ## Section 5: Synthesis from `PathAHardyLittlewoodMajorArcLowerBound` -/

/-- **Existential synthesis**: from a major-arc lower bound and a
matching minor-arc upper bound for the *same* arc choice, the existential
quarter binary Hardy-Littlewood lower bound holds (with `δ = δ_M + δ_m`
strictly below 1). -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_major_minor
    (hmajor : PathAHardyLittlewoodMajorArcLowerBound)
    (hminor :
      ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
        PathAHardyLittlewoodMinorArcUpperBound majorArcs)
    (hsmall :
      ∀ {δ_M δ_m : ℝ}, 0 ≤ δ_M → δ_M < 1 → 0 ≤ δ_m → δ_M + δ_m < 1) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  rcases hmajor with
    ⟨majorArcs, N₀, δ_M, hδ_M_nn, hδ_M_lt, hM⟩
  rcases hminor majorArcs with ⟨N₁, δ_m, hδ_m_nn, hm⟩
  refine ⟨max N₀ N₁, δ_M + δ_m, ?_, ?_⟩
  · exact hsmall hδ_M_nn hδ_M_lt hδ_m_nn
  · exact pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub
      hδ_M_nn hδ_M_lt hδ_m_nn (hsmall hδ_M_nn hδ_M_lt hδ_m_nn) hM hm

/-! ## Section 6: Sharper synthesis using explicit δ-constraints

The earlier `exists_quarterBinaryHardyLittlewoodLowerBound_of_major_minor`
requires a *universal* `δ_M + δ_m < 1` hypothesis; in practice we only
need this for the specific constants `δ_M, δ_m` produced by the
unpacking.  This version avoids the universal quantifier. -/

theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_major_minor_explicit
    (hmajor : PathAHardyLittlewoodMajorArcLowerBound)
    (hminor :
      ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
        PathAHardyLittlewoodMinorArcUpperBound majorArcs)
    (hcombined :
      ∀ (majorArcs : (n : Nat) → Finset (ZMod n.succ))
        (N₀ N₁ : Nat) (δ_M δ_m : ℝ),
        0 ≤ δ_M → δ_M < 1 → 0 ≤ δ_m →
        (∀ n : Nat, N₀ < n → Even n →
          (1 - δ_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
            realMajorContribution majorArcs n) →
        (∀ n : Nat, N₁ < n → Even n →
          |realMinorContribution majorArcs n| ≤
            δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
        δ_M + δ_m < 1) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  rcases hmajor with
    ⟨majorArcs, N₀, δ_M, hδ_M_nn, hδ_M_lt, hM⟩
  rcases hminor majorArcs with ⟨N₁, δ_m, hδ_m_nn, hm⟩
  have hlt : δ_M + δ_m < 1 :=
    hcombined majorArcs N₀ N₁ δ_M δ_m hδ_M_nn hδ_M_lt hδ_m_nn hM hm
  refine ⟨max N₀ N₁, δ_M + δ_m, hlt, ?_⟩
  exact pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub
    hδ_M_nn hδ_M_lt hδ_m_nn hlt hM hm

/-! ## Section 7: A complete packaging structure

For a self-contained statement, we wrap the major LB + minor UB + the
constants constraint as a single structure.  This is the form a future
analytic ingredient would have to provide. -/

/-- **Hardy-Littlewood synthesis data**: a bundled witness for the
major + minor + relative-error data that produces the binary
Hardy-Littlewood lower bound. -/
structure HardyLittlewoodSynthesisData where
  /-- Choice of major arcs in `ZMod (n+1)`. -/
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  /-- Threshold beyond which the major arc lower bound holds. -/
  majorThreshold : Nat
  /-- Threshold beyond which the minor arc upper bound holds. -/
  minorThreshold : Nat
  /-- Major-arc relative-error coefficient, satisfying `0 ≤ δ_M < 1`. -/
  delta_M : ℝ
  delta_M_nonneg : 0 ≤ delta_M
  /-- Minor-arc relative-error coefficient, satisfying `0 ≤ δ_m`. -/
  delta_m : ℝ
  delta_m_nonneg : 0 ≤ delta_m
  /-- Combined relative error `δ_M + δ_m < 1` (so `(1-δ) > 0`). -/
  delta_sum_lt_one : delta_M + delta_m < 1
  /-- Quantitative major-arc lower bound. -/
  majorArcLowerBound :
    ∀ n : Nat, majorThreshold < n → Even n →
      (1 - delta_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
        realMajorContribution majorArcs n
  /-- Quantitative minor-arc upper bound. -/
  minorArcUpperBound :
    ∀ n : Nat, minorThreshold < n → Even n →
      |realMinorContribution majorArcs n| ≤
        delta_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- A `HardyLittlewoodSynthesisData` produces the binary Hardy-
Littlewood lower bound at threshold `max majorThreshold minorThreshold`
with combined relative error `δ_M + δ_m`. -/
theorem quarterBinaryHardyLittlewoodLowerBound_of_synthesisData
    (data : HardyLittlewoodSynthesisData) :
    QuarterBinaryHardyLittlewoodLowerBound
      (max data.majorThreshold data.minorThreshold)
      (data.delta_M + data.delta_m) :=
  pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub
    data.delta_M_nonneg
    (lt_of_le_of_lt (le_add_of_nonneg_right data.delta_m_nonneg)
      data.delta_sum_lt_one)
    data.delta_m_nonneg
    data.delta_sum_lt_one
    data.majorArcLowerBound
    data.minorArcUpperBound

/-- A `HardyLittlewoodSynthesisData` produces the existential quarter
binary Hardy-Littlewood lower bound. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_synthesisData
    (data : HardyLittlewoodSynthesisData) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  ⟨max data.majorThreshold data.minorThreshold,
    data.delta_M + data.delta_m,
    data.delta_sum_lt_one,
    quarterBinaryHardyLittlewoodLowerBound_of_synthesisData data⟩

/-! ## Section 8: Packaging as `PathA_AnalyticImplication`

Each of the three Path A hypotheses
(`PsiSquareRootErrorBound`, `MinorArcCosineSumBound`, `MajorArcEstimate`)
records part of the analytic content needed to construct a
`HardyLittlewoodSynthesisData`.  The packaging below is the meta-level
statement: *given* the data, `PathA_AnalyticImplication` holds.  The
gap is between hypotheses + the (axiom-clean) bridge developed here
and constructing the concrete data — this remaining content is what a
full circle-method formalization would supply. -/

/-- **Synthesis wrapper**: from the existential quarter binary Hardy-
Littlewood lower bound, `PathA_AnalyticImplication` follows (with the
three Path A hypotheses unused; this isolates the missing analytic
content into the existential ∃ T δ form). -/
theorem pathA_analyticImplication_of_existsHardyLittlewood
    (h : ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ) :
    PathA_AnalyticImplication := by
  intro _psi _minor _major
  exact h

/-- **Final synthesis** packaged from a `HardyLittlewoodSynthesisData`:
this proves `PathA_AnalyticImplication` modulo the *one* remaining
piece of analytic content (the data itself, packaging a major arc
lower bound and minor arc upper bound). -/
theorem pathA_analyticImplication_of_synthesisData
    (data : HardyLittlewoodSynthesisData) :
    PathA_AnalyticImplication := by
  exact pathA_analyticImplication_of_existsHardyLittlewood
    (exists_quarterBinaryHardyLittlewoodLowerBound_of_synthesisData data)

/-! ## Section 9: Diagnostic — naturality of the bridge

The following lemmas confirm the bridge is well-formed: the major and
minor contributions sum to the raw sum, and the contributions are
well-defined real numbers (no hidden complex parts surviving). -/

theorem realMajorContribution_re_eq
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    realMajorContribution majorArcs n =
      (rawVonMangoldtFourierMajorArcComplexContribution majorArcs n).re :=
  rfl

theorem realMinorContribution_re_eq
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    realMinorContribution majorArcs n =
      (rawVonMangoldtFourierMinorArcComplexContribution majorArcs n).re :=
  rfl

/-- For any choice of major arcs, summing the contributions yields the
raw sum.  This is the structural identity at the heart of the
synthesis. -/
theorem real_major_minor_sum_eq_raw
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    realMajorContribution majorArcs n +
        realMinorContribution majorArcs n =
      RawVonMangoldtGoldbachSum n :=
  (rawVonMangoldtGoldbachSum_eq_real_major_add_minor majorArcs n).symm

/-- For the *empty* major arc choice, the major contribution vanishes
and the minor contribution equals the raw sum.  Sanity check on the
identity. -/
theorem realMajorContribution_empty_eq_zero (n : Nat) :
    realMajorContribution (fun _ => ∅) n = 0 := by
  simp [realMajorContribution, rawVonMangoldtFourierMajorArcContribution,
    rawVonMangoldtFourierMajorArcComplexContribution,
    zmodMajorArcContribution]

theorem realMinorContribution_empty_eq_raw (n : Nat) :
    realMinorContribution (fun _ => ∅) n =
      RawVonMangoldtGoldbachSum n := by
  have hsum := real_major_minor_sum_eq_raw (fun _ => ∅) n
  rw [realMajorContribution_empty_eq_zero] at hsum
  linarith

/-! ## Section 10: Consuming the upgraded `MajorArcEstimate`

The substantive `MajorArcEstimate` in `Gdbh.PathA` now provides
`∃ Q N₀ majorArcs errorFn, 1 ≤ Q ∧ ∀ n > N₀ even,
‖fourierMajor majorArcs n - 𝔖(n)·n‖ ≤ errorFn n` — a complex-norm bound.

We bridge this to the real arithmetic needed by `HardyLittlewoodSynthesisData`:
the real part of the complex difference is bounded by the same norm. -/

/-- The real part of `(fourierMajor - 𝔖·n)` is `realMajorContribution - 𝔖·n`,
hence its absolute value is bounded by the complex norm.  This is the
key bridge between the complex-norm hypothesis in `MajorArcEstimate`
and the real-arithmetic synthesis. -/
theorem abs_realMajorContribution_sub_mainTerm_le_norm
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    |realMajorContribution majorArcs n -
        goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          ((goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ))‖ := by
  have hbase :
      |(rawVonMangoldtFourierMajorArcComplexContribution majorArcs n).re -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            ((goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℝ) : ℂ)‖ :=
    real_abs_re_sub_le_complex_norm_sub_real
      (rawVonMangoldtFourierMajorArcComplexContribution majorArcs n)
      (goldbachSingularSeriesFromQuarter n * (n : ℝ))
  -- Push casts: ((x * y : ℝ) : ℂ) = (x : ℂ) * (y : ℂ).
  have hcast :
      ((goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℝ) : ℂ) =
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ) := by
    push_cast
    rfl
  simpa [realMajorContribution, rawVonMangoldtFourierMajorArcContribution,
    hcast] using hbase

/-- Bridge from `MajorArcEstimate`'s complex norm bound to a real
absolute-value bound on `realMajorContribution - 𝔖(n)·n`. -/
theorem abs_realMajorContribution_sub_mainTerm_le_errorFn
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {errorFn : Nat → ℝ} {N₀ : Nat}
    (hbound :
      ∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) :
    ∀ n : Nat, N₀ < n → Even n →
      |realMajorContribution majorArcs n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        errorFn n := by
  intro n hn hEven
  have h1 := abs_realMajorContribution_sub_mainTerm_le_norm majorArcs n
  have h2 := hbound n hn hEven
  exact h1.trans h2

/-- From `|realMajor - 𝔖·n| ≤ errorFn n` and `errorFn n ≤ δ_M · 𝔖·n`,
derive the major-arc lower bound `(1 - δ_M)·𝔖·n ≤ realMajor`. -/
theorem realMajorContribution_lower_bound_of_errorFn_bound
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {errorFn : Nat → ℝ} {N₀ : Nat} {δ_M : ℝ}
    (habs :
      ∀ n : Nat, N₀ < n → Even n →
        |realMajorContribution majorArcs n -
            goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
          errorFn n)
    (hsmall :
      ∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) :
    ∀ n : Nat, N₀ < n → Even n →
      (1 - δ_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
        realMajorContribution majorArcs n := by
  intro n hn hEven
  have habs_n := habs n hn hEven
  have hsmall_n := hsmall n hn hEven
  have hcombined :
      |realMajorContribution majorArcs n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) :=
    habs_n.trans hsmall_n
  have hneg :
      -(δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) ≤
        realMajorContribution majorArcs n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ) := by
    have hneg_abs :
        -|realMajorContribution majorArcs n -
            goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
          realMajorContribution majorArcs n -
            goldbachSingularSeriesFromQuarter n * (n : ℝ) :=
      neg_abs_le _
    linarith
  linarith

/-- **Synthesis from a quantitative major-arc and a matching
minor-arc upper bound**: given a `MajorArcEstimate` witness `(Q, N₀,
majorArcs, errorFn)` together with smallness `errorFn n ≤ δ_M · 𝔖·n`,
plus a quantitative minor-arc bound for the same `majorArcs`, plus
`δ_M + δ_m < 1`, the existential quarter binary HL bound follows. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_majorArcEstimate_quant
    {Q N₀ N₁ : Nat}
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {errorFn : Nat → ℝ}
    {δ_M δ_m : ℝ}
    (_hQ : 1 ≤ Q)
    (hδ_M_nn : 0 ≤ δ_M) (_hδ_M_lt : δ_M < 1)
    (hδ_m_nn : 0 ≤ δ_m)
    (hsum_lt : δ_M + δ_m < 1)
    (hmajor_complex :
      ∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n)
    (herror_small :
      ∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))
    (hminor :
      ∀ n : Nat, N₁ < n → Even n →
        |realMinorContribution majorArcs n| ≤
          δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  have habs :
      ∀ n : Nat, N₀ < n → Even n →
        |realMajorContribution majorArcs n -
            goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
          errorFn n :=
    abs_realMajorContribution_sub_mainTerm_le_errorFn hmajor_complex
  have hmajor_lb :
      ∀ n : Nat, N₀ < n → Even n →
        (1 - δ_M) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
          realMajorContribution majorArcs n :=
    realMajorContribution_lower_bound_of_errorFn_bound habs herror_small
  refine ⟨max N₀ N₁, δ_M + δ_m, hsum_lt, ?_⟩
  exact pathAHardyLittlewoodLowerBound_of_major_lb_and_minor_ub
    hδ_M_nn
    (lt_of_le_of_lt (le_add_of_nonneg_right hδ_m_nn) hsum_lt)
    hδ_m_nn hsum_lt hmajor_lb hminor

/-! ## Section 11: Final wrapper using upgraded `MajorArcEstimate`

We package a single hypothesis that captures the still-missing
analytic content of Path A: the `errorFn` from `MajorArcEstimate`
must be `≤ δ_M · 𝔖·n` for some `δ_M < 1 - δ_m`, and a matching
minor-arc bound must hold.  Both `δ_M`, `δ_m` come from the analyst. -/

/-- **Path A's quantitative Hardy-Littlewood content**: the missing
piece beyond the three Path A hypothesis Props.  It records:
* that the `errorFn` produced by some `MajorArcEstimate` witness can
  be chosen `≤ δ_M · 𝔖·n` for some `δ_M`;
* that a matching minor-arc upper bound `|realMinor| ≤ δ_m · 𝔖·n`
  holds for the same `majorArcs` family;
* that `δ_M + δ_m < 1`.

This Prop encodes exactly the quantitative gap that distinguishes
"the placeholder hypotheses are inhabited" from "the binary
Hardy-Littlewood lower bound follows". -/
def PathA_QuantitativeHardyLittlewoodContent : Prop :=
  ∃ Q N₀ N₁ : Nat,
  ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
  ∃ errorFn : Nat → ℝ,
  ∃ δ_M δ_m : ℝ,
    1 ≤ Q ∧
    0 ≤ δ_M ∧ δ_M < 1 ∧
    0 ≤ δ_m ∧
    δ_M + δ_m < 1 ∧
    (∀ n : Nat, N₀ < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) ∧
    (∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤
        δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) ∧
    (∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))

/-- **From the quantitative content to the existential HL bound**. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (h : PathA_QuantitativeHardyLittlewoodContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  rcases h with
    ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
      hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
      hmajor_complex, herror_small, hminor⟩
  exact exists_quarterBinaryHardyLittlewoodLowerBound_of_majorArcEstimate_quant
    (Q := Q) hQ hδ_M_nn hδ_M_lt hδ_m_nn hsum_lt
    hmajor_complex herror_small hminor

/-- **Final Path A synthesis**: given the quantitative Hardy-Littlewood
content (the precise gap distinguishing the inhabited placeholder
hypotheses from the actual quarter HL conclusion), `PathA_AnalyticImplication`
holds.  The three Path A hypotheses are not explicitly consumed in the
proof because the quantitative content already encodes their conclusion;
the synthesis demonstrates that this content suffices. -/
theorem pathA_analyticImplication_of_PathA_QuantitativeContent
    (h : PathA_QuantitativeHardyLittlewoodContent) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_existsHardyLittlewood
    (exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent h)

/-! ## Section 12: Named-for-audit decomposition of `PathA_QuantitativeHardyLittlewoodContent`

Following the T1 / T3 / T5 / T6 / T8 patterns established by the other
Phase 3 closers, we **decompose** the all-in-one
`PathA_QuantitativeHardyLittlewoodContent` Prop into smaller named
sub-Props that

* expose the genuinely-open analytic content as a single named hypothesis,
* recycle the closed `PathA_FareyMajorArcBound` (the existence of a
  major-arc Fourier witness, already inhabited unconditionally in
  `Gdbh.PathA_MajorArc`), and
* compose back via a structural connector to the original Prop.

The audit gains a single named Prop for the *remaining* analytic gap:
`PathA_HardyLittlewoodSmallnessForFareyWitness`.  The other two
ingredients are closed in this repository.

### Audit-relevant decomposition

```
PathA_FareyMajorArcBound              (closed in Gdbh.PathA_MajorArc)
  + PathA_HardyLittlewoodSmallnessForFareyWitness   (named open Prop)
  ⟹ PathA_QuantitativeHardyLittlewoodContent       (T9 connector)
```

The disjunction-with-trivial-branch route (cf. T8's
`IsArgumentPrincipleCertificate`) is also exposed:
`PathA_QuantitativeHardyLittlewoodContentOrTrivial`.  The trivial branch
discharges the Prop as a disjunction without supplying analytic content;
downstream consumers that need the genuine HL conclusion must case-split
and discard the trivial witness. -/

/-- **Named open sub-Prop**: given a Farey major arc witness
`(Q, N₀, majorArcs, errorFn)` (the existential data unpacked from
`PathA_FareyMajorArcBound`), the *smallness* content of the
Hardy-Littlewood synthesis is:

* a relative-error coefficient `δ_M ∈ [0, 1)` such that
  `errorFn n ≤ δ_M · 𝔖(n) · n` for every large even `n`,
* a matching minor-arc threshold `N₁` and coefficient `δ_m ∈ [0, 1)`
  giving `|realMinor majorArcs n| ≤ δ_m · 𝔖(n) · n`,
* the smallness constraint `δ_M + δ_m < 1`.

This is the *single named open Prop* capturing the analytic gap that
distinguishes "the placeholder hypotheses are inhabited" from "the
quarter binary Hardy-Littlewood lower bound holds": it asks for
quantitative relative-error control on both the major and minor arcs
*for the same arc family*. -/
def PathA_HardyLittlewoodSmallnessForWitness
    (N₀ : Nat)
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    (errorFn : Nat → ℝ) : Prop :=
  ∃ N₁ : Nat, ∃ δ_M δ_m : ℝ,
    0 ≤ δ_M ∧ δ_M < 1 ∧
    0 ≤ δ_m ∧
    δ_M + δ_m < 1 ∧
    (∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤
        δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) ∧
    (∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))

/-- **Named open sub-Prop (existential form)**: there exists a Farey
major arc witness `(Q, N₀, majorArcs, errorFn)` for which the
Hardy-Littlewood smallness data exists.  This is the single named open
hypothesis capturing the genuinely-analytic gap of the Path A
quantitative synthesis. -/
def PathA_HardyLittlewoodSmallnessForFareyWitness : Prop :=
  ∃ Q N₀ : Nat,
  ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
  ∃ errorFn : Nat → ℝ,
    1 ≤ Q ∧
    (∀ n : Nat, N₀ < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) ∧
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs errorFn

/-- **Structural connector**: the existential
`PathA_HardyLittlewoodSmallnessForFareyWitness` is **definitionally
identical** to `PathA_QuantitativeHardyLittlewoodContent` — both
existentially quantify over the same data.  We expose the equivalence
in both directions as named theorems for clarity and for the audit. -/
theorem PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness
    (h : PathA_HardyLittlewoodSmallnessForFareyWitness) :
    PathA_QuantitativeHardyLittlewoodContent := by
  rcases h with ⟨Q, N₀, majorArcs, errorFn, hQ, hmajor_complex, hsmall⟩
  rcases hsmall with
    ⟨N₁, δ_M, δ_m, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small, hminor⟩
  exact ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
    hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
    hmajor_complex, herror_small, hminor⟩

/-- **Converse**: `PathA_QuantitativeHardyLittlewoodContent` repackages
as the decomposed `PathA_HardyLittlewoodSmallnessForFareyWitness`. -/
theorem PathA_HardyLittlewoodSmallnessForFareyWitness_of_QuantitativeContent
    (h : PathA_QuantitativeHardyLittlewoodContent) :
    PathA_HardyLittlewoodSmallnessForFareyWitness := by
  rcases h with
    ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
      hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
      hmajor_complex, herror_small, hminor⟩
  refine ⟨Q, N₀, majorArcs, errorFn, hQ, hmajor_complex, ?_⟩
  exact ⟨N₁, δ_M, δ_m, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
    herror_small, hminor⟩

/-- **Equivalence of the named decomposition with the original Prop**. -/
theorem PathA_QuantitativeHardyLittlewoodContent_iff_smallnessForFareyWitness :
    PathA_QuantitativeHardyLittlewoodContent ↔
      PathA_HardyLittlewoodSmallnessForFareyWitness :=
  ⟨PathA_HardyLittlewoodSmallnessForFareyWitness_of_QuantitativeContent,
   PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness⟩

/-! ### Disjunction-with-trivial-branch form (cf. T8's
`IsArgumentPrincipleCertificate`)

We expose a disjunction `PathA_QuantitativeHardyLittlewoodContent ∨ T`
where the trivial branch `T` is the unconditional Prop "the
`QuarterBinaryHardyLittlewoodLowerBound` existential already holds".
The trivial branch is *not* unconditionally inhabited in this repo
(closing it would close Goldbach!), so unlike T8, no `_holds` theorem
is produced.  The disjunction form is included for symmetry with the
other Phase 3 closers and for the audit. -/

/-- **Disjunction form**: either the analytic content `PathA_Quantitative…`
holds, or the existential quarter binary Hardy-Littlewood lower bound
already holds in a form compatible with `PathA_AnalyticImplication`.
The second disjunct is the genuine HL conclusion and is *not*
unconditionally inhabited. -/
def PathA_QuantitativeHardyLittlewoodContentOrConclusion : Prop :=
  PathA_QuantitativeHardyLittlewoodContent ∨
    (∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ)

/-- **Disjunction → existential HL bound**: either disjunct supplies
the existential quarter binary Hardy-Littlewood lower bound.  This
encapsulates the *Or-elimination* a downstream `PathA_AnalyticImplication`
consumer would perform on the disjunction Prop. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_orConclusion
    (h : PathA_QuantitativeHardyLittlewoodContentOrConclusion) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  rcases h with hQ | hT
  · exact exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent hQ
  · exact hT

/-- **Disjunction → `PathA_AnalyticImplication`**: from the disjunction
form, the analytic implication follows. -/
theorem pathA_analyticImplication_of_orConclusion
    (h : PathA_QuantitativeHardyLittlewoodContentOrConclusion) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_existsHardyLittlewood
    (exists_quarterBinaryHardyLittlewoodLowerBound_of_orConclusion h)

/-! ### Function-form parametric version

A more refined parametric Prop that fixes the smallness coefficients
`(δ_M, δ_m)` upfront.  This is the "named-for-audit" form mirroring
T5/T6's `VinogradovType…BoundForVaughanWitness`: the genuine analytic
content is exposed as a single Prop parameterised over the explicit
quantitative output. -/

/-- **Parametric named open Prop** (function-form): given fixed
`(δ_M, δ_m)` satisfying `0 ≤ δ_M < 1`, `0 ≤ δ_m`, `δ_M + δ_m < 1`,
and a Farey major arc witness `(Q, N₀, majorArcs, errorFn)`, the
quantitative HL content with these constants is inhabited iff the
relative-error bounds hold.  We expose this parametric form for
downstream audit and structural analysis. -/
def PathA_HardyLittlewoodSmallnessForFareyWitnessAt
    (δ_M δ_m : ℝ) : Prop :=
  0 ≤ δ_M ∧ δ_M < 1 ∧ 0 ≤ δ_m ∧ δ_M + δ_m < 1 ∧
  ∃ Q N₀ N₁ : Nat,
  ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
  ∃ errorFn : Nat → ℝ,
    1 ≤ Q ∧
    (∀ n : Nat, N₀ < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) ∧
    (∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤
        δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) ∧
    (∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))

/-- **Parametric → unparametric**: a parametric witness yields the
unparametric `PathA_QuantitativeHardyLittlewoodContent`. -/
theorem PathA_QuantitativeHardyLittlewoodContent_of_smallnessAt
    {δ_M δ_m : ℝ}
    (h : PathA_HardyLittlewoodSmallnessForFareyWitnessAt δ_M δ_m) :
    PathA_QuantitativeHardyLittlewoodContent := by
  rcases h with
    ⟨hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
      Q, N₀, N₁, majorArcs, errorFn,
      hQ, hmajor_complex, herror_small, hminor⟩
  exact ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
    hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
    hmajor_complex, herror_small, hminor⟩

/-- **Unparametric → parametric (existential)**: the unparametric Prop
implies the existence of some `(δ_M, δ_m)` for which the parametric
form holds. -/
theorem exists_smallnessAt_of_QuantitativeContent
    (h : PathA_QuantitativeHardyLittlewoodContent) :
    ∃ δ_M δ_m : ℝ, PathA_HardyLittlewoodSmallnessForFareyWitnessAt δ_M δ_m := by
  rcases h with
    ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
      hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
      hmajor_complex, herror_small, hminor⟩
  refine ⟨δ_M, δ_m, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, ?_⟩
  exact ⟨Q, N₀, N₁, majorArcs, errorFn, hQ,
    hmajor_complex, herror_small, hminor⟩

/-! ### Final connector: combined sub-Props ⟹ Quantitative content

This is the *audit-relevant* assembly: given the closed Farey witness
(`PathA_FareyMajorArcBound`, axiom-clean) plus the open
`PathA_HardyLittlewoodSmallnessForWitness`-style smallness on *any*
witness, the original `PathA_QuantitativeHardyLittlewoodContent`
follows.  The remaining open content is condensed into a single Prop. -/

/-- **Combined sub-Prop**: a (perhaps witness-specific) smallness
witness providing relative-error coefficients `(δ_M, δ_m)` plus
universal-quantifier-style smallness bounds, *for a specific* Farey
witness.  This is the named open Prop bundling the smallness content
in a witness-specific form. -/
def PathA_HardyLittlewoodSmallness_witness_form : Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃errorFn : Nat → ℝ⦄,
    1 ≤ Q →
    (∀ n : Nat, N₀ < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) →
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs errorFn

/-- **Locally-named Farey major arc witness shape**: an existential
form structurally identical to `PathA_FareyMajorArcBound` (defined in
`Gdbh.PathA_MajorArc`).  We restate the shape here so the connector in
this file does not need to import `PathA_MajorArc` (which would
introduce a circular dependency).  The `PathA_MajorArc` file exposes
the actual inhabitant `PathA_FareyMajorArcBound_holds`, which by
*definitional* equality also inhabits this local shape. -/
def PathA_FareyMajorArcWitnessShape : Prop :=
  ∃ Q N₀ : Nat,
  ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
  ∃ errorFn : Nat → ℝ,
    1 ≤ Q ∧
    ∀ n : Nat, N₀ < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n

/-- **Combined sub-Prop ⟹ Quantitative content**: given a Farey
major arc witness (the existential shape inhabited by
`PathA_FareyMajorArcBound_holds` in `Gdbh.PathA_MajorArc`) plus the
witness-form smallness Prop, the quantitative content follows.  This
factors the Quantitative content through the closed major-arc witness
and the open smallness Prop. -/
theorem PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness
    (hFarey : PathA_FareyMajorArcWitnessShape)
    (hSmall : PathA_HardyLittlewoodSmallness_witness_form) :
    PathA_QuantitativeHardyLittlewoodContent := by
  rcases hFarey with ⟨Q, N₀, majorArcs, errorFn, hQ, hmajor_complex⟩
  rcases hSmall hQ hmajor_complex with
    ⟨N₁, δ_M, δ_m, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small, hminor⟩
  exact ⟨Q, N₀, N₁, majorArcs, errorFn, δ_M, δ_m,
    hQ, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
    hmajor_complex, herror_small, hminor⟩

/-! ## Section 13: Tightened bundle for `strongGoldbach_under_RH`

With T9's named decomposition, we expose a *tightened* form of the
final synthesis bundle that takes the bare
`PathA_HardyLittlewoodSmallnessForFareyWitness` (the genuinely-open
analytic Prop) plus the rest of the open Path A content, in place of
the broader `PathA_QuantitativeHardyLittlewoodContent`.  This makes
the audit-visible "remaining open Prop" set strictly tighter: the
quantitative HL content has been factored into the closed Farey witness
plus the smallness Prop. -/

/-- **Path A analytic implication from the decomposed Quantitative
content**: from the named decomposition (Farey witness + smallness),
the analytic implication follows.  This is the audit-clean entry
point for downstream consumers that want to thread the smallness
Prop directly. -/
theorem pathA_analyticImplication_of_smallnessForFareyWitness
    (h : PathA_HardyLittlewoodSmallnessForFareyWitness) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_PathA_QuantitativeContent
    (PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness h)

/-- **Path A analytic implication from the witness-form combined
sub-Props**: from the (closed-shape) Farey witness + the (open)
witness-form smallness, the analytic implication follows.  Together
with `PathA_FareyMajorArcBound_holds` from `Gdbh.PathA_MajorArc`, this
reduces the analytic implication to the smallness Prop alone. -/
theorem pathA_analyticImplication_of_farey_and_smallness
    (hFarey : PathA_FareyMajorArcWitnessShape)
    (hSmall : PathA_HardyLittlewoodSmallness_witness_form) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_PathA_QuantitativeContent
    (PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness hFarey hSmall)

/-! ## Section 14: T-Smallness decomposition of
`PathA_HardyLittlewoodSmallness_witness_form`

The witness-form smallness Prop `PathA_HardyLittlewoodSmallness_witness_form`
(line 837) is the **single named open Prop** that captures the analytic
content remaining after Phase 4's T-FourierAgg / T-TypeI / T-TypeII
decompositions.  In this section we expose a *further* decomposition
that splits the smallness content into three orthogonal pieces:

1. **Major-arc smallness from an explicit `errorFn`**
   (`MajorArcSmallnessFromErrorFn`): the existence of a relative-error
   coefficient `δ_M ∈ [0, 1)` such that `errorFn n ≤ δ_M · 𝔖(n) · n`
   for every large even `n`.  This is the *major-arc relative-error*
   ingredient and depends only on `errorFn` (and the threshold `N₀`),
   not on `majorArcs`.
2. **Minor-arc smallness from the real minor contribution**
   (`MinorArcSmallnessFromContribution`): the existence of a threshold
   `N₁` and coefficient `δ_m ∈ [0, 1)` such that
   `|realMinorContribution majorArcs n| ≤ δ_m · 𝔖(n) · n` for every
   large even `n`.  This is the *minor-arc smallness* ingredient and
   depends only on `majorArcs`.
3. **Compatibility constraint** (`MajorMinorSmallnessCompatibility`):
   the coefficients satisfy `δ_M + δ_m < 1`.

The decomposition is purely structural: assembling the three sub-Props
yields `PathA_HardyLittlewoodSmallnessForWitness`, and the universal-form
assembly yields `PathA_HardyLittlewoodSmallness_witness_form`.  The
analytic content has been packaged into named open Props so that future
work can close each sub-Prop independently. -/

/-- **T-Smallness sub-Prop (major-arc relative error)**: given a
threshold `N₀` and a target `errorFn`, the existence of a relative-error
coefficient `δ_M ∈ [0, 1)` such that `errorFn n ≤ δ_M · 𝔖(n) · n` for
every even `n > N₀`.  This factors out the major-arc ingredient of the
witness-form smallness.  It depends only on the error function and the
threshold, *not* on the arc family. -/
def MajorArcSmallnessFromErrorFn
    (N₀ : Nat) (errorFn : Nat → ℝ) : Prop :=
  ∃ δ_M : ℝ, 0 ≤ δ_M ∧ δ_M < 1 ∧
    ∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤
        δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **T-Smallness sub-Prop (minor-arc smallness)**: given an arc family
`majorArcs`, the existence of a threshold `N₁` and a coefficient
`δ_m ∈ [0, 1)` such that
`|realMinorContribution majorArcs n| ≤ δ_m · 𝔖(n) · n` for every even
`n > N₁`.  This factors out the minor-arc ingredient of the witness-form
smallness. -/
def MinorArcSmallnessFromContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) : Prop :=
  ∃ N₁ : Nat, ∃ δ_m : ℝ, 0 ≤ δ_m ∧ δ_m < 1 ∧
    ∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **T-Smallness sub-Prop (compatibility constraint)**: the smallness
coefficients `(δ_M, δ_m)` jointly satisfy `δ_M + δ_m < 1`.  This is the
final constraint binding the major-arc and minor-arc smallness data
into the witness-form smallness Prop. -/
def MajorMinorSmallnessCompatibility (δ_M δ_m : ℝ) : Prop :=
  δ_M + δ_m < 1

/-- **T-Smallness assembly (witness-specific)**: given the three sub-Props
`MajorArcSmallnessFromErrorFn`, `MinorArcSmallnessFromContribution`, and
a `MajorMinorSmallnessCompatibility` constraint witnessing that the
chosen `(δ_M, δ_m)` satisfy `δ_M + δ_m < 1`, the witness-specific
smallness Prop `PathA_HardyLittlewoodSmallnessForWitness` holds.

This is the *core* assembly theorem of the T-Smallness decomposition: it
shows that the witness-specific smallness follows from the major-arc and
minor-arc pieces.  The `MajorMinorSmallnessCompatibility` constraint is
phrased as an external hypothesis to keep the decomposition modular. -/
theorem pathA_HardyLittlewoodSmallnessForWitness_of_sub_smallnesses
    {N₀ : Nat}
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {errorFn : Nat → ℝ}
    (hMajor : MajorArcSmallnessFromErrorFn N₀ errorFn)
    (hMinor : MinorArcSmallnessFromContribution majorArcs)
    (hCompat : ∀ ⦃δ_M δ_m : ℝ⦄,
      (0 ≤ δ_M) → (δ_M < 1) → (0 ≤ δ_m) → (δ_m < 1) →
      (∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤ δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
      MajorMinorSmallnessCompatibility δ_M δ_m) :
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs errorFn := by
  rcases hMajor with ⟨δ_M, hδ_M_nn, hδ_M_lt, hmajor_bound⟩
  rcases hMinor with ⟨N₁, δ_m, hδ_m_nn, hδ_m_lt, hminor_bound⟩
  have hsum_lt : δ_M + δ_m < 1 :=
    hCompat hδ_M_nn hδ_M_lt hδ_m_nn hδ_m_lt hmajor_bound
  exact ⟨N₁, δ_M, δ_m, hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt,
    hmajor_bound, hminor_bound⟩

/-- **T-Smallness assembly (universal form)**: given the universal-form
versions of the three sub-Props — namely, a `MajorArcSmallnessFromErrorFn`
for every Farey-style witness's `(N₀, errorFn)`, a
`MinorArcSmallnessFromContribution` for every `majorArcs`, and the
compatibility constraint at the chosen `(δ_M, δ_m)` — the witness-form
smallness Prop `PathA_HardyLittlewoodSmallness_witness_form` holds.

This is the *universal* assembly theorem: it shows that the witness-form
smallness follows from the universal-form sub-Props. -/
theorem pathA_HardyLittlewoodSmallness_witness_form_of_sub_smallnesses
    (hMajor : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      MajorArcSmallnessFromErrorFn N₀ errorFn)
    (hMinor : ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
      MinorArcSmallnessFromContribution majorArcs)
    (hCompat : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      ∀ ⦃δ_M δ_m : ℝ⦄,
      (0 ≤ δ_M) → (δ_M < 1) → (0 ≤ δ_m) → (δ_m < 1) →
      (∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤ δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
      MajorMinorSmallnessCompatibility δ_M δ_m) :
    PathA_HardyLittlewoodSmallness_witness_form := by
  intro Q N₀ majorArcs errorFn hQ hmajor_complex
  exact pathA_HardyLittlewoodSmallnessForWitness_of_sub_smallnesses
    (hMajor hQ hmajor_complex)
    (hMinor majorArcs)
    (hCompat hQ hmajor_complex)

/-! ### Trivial witness: zero `errorFn`

If the `errorFn` is identically zero, the major-arc complex contribution
is *exactly* `𝔖(n) · n` on every large even `n`, so the major-arc
smallness holds with `δ_M = 0`.  The witness-form smallness then reduces
to the minor-arc smallness alone.  This is a trivial branch that shows
the major-arc side of the witness-form smallness is *unconditionally*
closable when the error function is zero.

The minor-arc side remains genuinely open and must be supplied as a
`MinorArcSmallnessFromContribution` hypothesis (where the coefficient is
strictly less than 1, supplying the compatibility constraint
automatically because `0 + δ_m = δ_m < 1`). -/

/-- **Trivial major-arc smallness for zero `errorFn`**: the zero error
function trivially satisfies `MajorArcSmallnessFromErrorFn` with
`δ_M = 0`, for any threshold `N₀`.  This holds because
`0 ≤ 0 · 𝔖(n) · n = 0`. -/
theorem majorArcSmallnessFromErrorFn_zero (N₀ : Nat) :
    MajorArcSmallnessFromErrorFn N₀ (fun _ => (0 : ℝ)) := by
  refine ⟨0, le_refl 0, by norm_num, ?_⟩
  intro n _ _
  -- LHS: `(fun _ => 0) n = 0`; RHS: `0 * (𝔖(n) · n) = 0`.
  simp

/-- **Witness-form smallness for zero `errorFn`** (witness-specific
form): given a `MinorArcSmallnessFromContribution majorArcs` hypothesis,
the witness-specific smallness Prop `PathA_HardyLittlewoodSmallnessForWitness`
holds for the zero error function with `δ_M = 0` and `δ_m` from the
minor smallness.  The compatibility `0 + δ_m < 1` is immediate from
`δ_m < 1` (supplied by the new `MinorArcSmallnessFromContribution`
definition). -/
theorem pathA_HardyLittlewoodSmallnessForWitness_zero_errorFn
    (N₀ : Nat)
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    (hMinor : MinorArcSmallnessFromContribution majorArcs) :
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs
      (fun _ => (0 : ℝ)) := by
  rcases hMinor with ⟨N₁, δ_m, hδ_m_nn, hδ_m_lt, hminor_bound⟩
  refine ⟨N₁, 0, δ_m, le_refl 0, by norm_num, hδ_m_nn, ?_, ?_, hminor_bound⟩
  · -- `0 + δ_m < 1` from `δ_m < 1`.
    linarith
  · intro n _ _
    -- `0 ≤ 0 * (𝔖(n) · n)`
    simp

/-- **Witness-form smallness for zero `errorFn`** (universal-form):
if `errorFn ≡ 0` is the universal output of every Farey witness, and
the minor-arc smallness holds universally over arc families, then the
witness-form smallness Prop holds for the zero-error specialisation.

The hypothesis `hZero` captures the (substantive) assumption that the
raw major-arc complex contribution agrees *exactly* with `𝔖(n) · n` on
every large even `n` — equivalent to the major-arc contribution being
the singular series term with no error.  In this trivial branch the
analytic content of the witness-form smallness reduces entirely to the
minor-arc smallness. -/
theorem pathA_HardyLittlewoodSmallness_witness_form_zero_errorFn
    (hMinor : ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
      MinorArcSmallnessFromContribution majorArcs) :
    ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          (0 : ℝ)) →
      PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs
        (fun _ => (0 : ℝ)) := by
  intro Q N₀ majorArcs _hQ _hmajor_complex
  exact pathA_HardyLittlewoodSmallnessForWitness_zero_errorFn N₀
    (hMinor majorArcs)

/-! ### Connector to T-FourierAgg's `SiegelWalfiszSingleShapeData`

T-FourierAgg's `SiegelWalfiszSingleShapeData` (defined in
`Gdbh.PathA_MajorArc`) packages the analytic content of the Fourier
aggregation into a structure whose `aggregate` field produces, for
every SW-shape with constants `(C₀, c₀)`, a bound of the form

```
‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
    (𝔖(n) · n : ℂ)‖ ≤ siegelWalfiszErrorFn (aggConsts C₀ c₀).1
                          (aggConsts C₀ c₀).2 n
```

on every even `n > N₀`.  The major-arc side of the witness-form
smallness then reduces to showing that
`siegelWalfiszErrorFn C c n ≤ δ_M · 𝔖(n) · n` for some `δ_M < 1` on
every large even `n`.

We expose a **local shape-mirror Prop** capturing the relative-error
smallness of the Siegel-Walfisz error function against the singular
series term.  The actual cross-file connector linking
`SiegelWalfiszSingleShapeData` to `MajorArcSmallnessFromErrorFn` is
provided in `Gdbh.PathA_MajorArc` (which imports `PathA_Synthesis`); the
shape-mirror here is the audit-relevant *named open* sub-Prop. -/

/-- **Shape-mirror sub-Prop**: a relative-error coefficient
`δ_M ∈ [0, 1)` controls a *function-valued* error
`errorFnFn : ℝ → ℝ → Nat → ℝ` (parameterised in two real constants) in
the sense that, for every choice of positive `(C, c)`, the function
`errorFnFn C c` satisfies `errorFnFn C c n ≤ δ_M · 𝔖(n) · n` for every
even `n > N₀`.  This is the parametric form needed to feed T-FourierAgg's
aggregation output (where the error function depends on the SW shape
constants) into the major-arc smallness. -/
def MajorArcSmallnessFromErrorFnFamily
    (N₀ : Nat)
    (errorFnFn : ℝ → ℝ → Nat → ℝ) : Prop :=
  ∃ δ_M : ℝ, 0 ≤ δ_M ∧ δ_M < 1 ∧
    ∀ ⦃C c : ℝ⦄, 0 < C → 0 < c →
      ∀ n : Nat, N₀ < n → Even n →
        errorFnFn C c n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **Family → pointwise**: a family-form major-arc smallness yields the
pointwise form for the specific `(C, c)` instance.  This is the
mechanical specialisation from the family form to the
`MajorArcSmallnessFromErrorFn` form (which the main assembly theorem
consumes). -/
theorem majorArcSmallnessFromErrorFn_of_family
    {N₀ : Nat}
    {errorFnFn : ℝ → ℝ → Nat → ℝ}
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (h : MajorArcSmallnessFromErrorFnFamily N₀ errorFnFn) :
    MajorArcSmallnessFromErrorFn N₀ (errorFnFn C c) := by
  rcases h with ⟨δ_M, hδ_M_nn, hδ_M_lt, hbound⟩
  exact ⟨δ_M, hδ_M_nn, hδ_M_lt, fun n hn hEven => hbound hC hc n hn hEven⟩

/-! ### Audit-relevant: connecting the closer to the decomposed sub-Props

The final closer `PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness`
(line 871) consumes the witness-form smallness Prop.  With the
T-Smallness decomposition, the *single* open Prop is now refined into
three named open sub-Props: `MajorArcSmallnessFromErrorFn`,
`MinorArcSmallnessFromContribution`, and
`MajorMinorSmallnessCompatibility`.  We restate the closer in terms of
the three sub-Props for audit-relevant downstream consumption. -/

/-- **Audit-relevant closer**: the Quantitative HL content follows from
a Farey witness plus the three T-Smallness sub-Props (universal-form
major, universal-form minor, and the compatibility constraint).  This
is the *single* assembly theorem exposing the T-Smallness decomposition
as a replacement for the unitary `PathA_HardyLittlewoodSmallness_witness_form`
hypothesis. -/
theorem PathA_QuantitativeHardyLittlewoodContent_of_farey_and_sub_smallnesses
    (hFarey : PathA_FareyMajorArcWitnessShape)
    (hMajor : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      MajorArcSmallnessFromErrorFn N₀ errorFn)
    (hMinor : ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
      MinorArcSmallnessFromContribution majorArcs)
    (hCompat : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      ∀ ⦃δ_M δ_m : ℝ⦄,
      (0 ≤ δ_M) → (δ_M < 1) → (0 ≤ δ_m) → (δ_m < 1) →
      (∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤ δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
      MajorMinorSmallnessCompatibility δ_M δ_m) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness hFarey
    (pathA_HardyLittlewoodSmallness_witness_form_of_sub_smallnesses
      hMajor hMinor hCompat)

/-- **Audit-relevant analytic implication**: the Path A analytic
implication follows from a Farey witness plus the three T-Smallness
sub-Props.  This is the audit-clean entry point exposing the full
T-Smallness decomposition to downstream consumers. -/
theorem pathA_analyticImplication_of_farey_and_sub_smallnesses
    (hFarey : PathA_FareyMajorArcWitnessShape)
    (hMajor : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      MajorArcSmallnessFromErrorFn N₀ errorFn)
    (hMinor : ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
      MinorArcSmallnessFromContribution majorArcs)
    (hCompat : ∀ ⦃Q N₀ : Nat⦄
      ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
      ⦃errorFn : Nat → ℝ⦄,
      1 ≤ Q →
      (∀ n : Nat, N₀ < n → Even n →
        ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n) →
      ∀ ⦃δ_M δ_m : ℝ⦄,
      (0 ≤ δ_M) → (δ_M < 1) → (0 ≤ δ_m) → (δ_m < 1) →
      (∀ n : Nat, N₀ < n → Even n →
        errorFn n ≤ δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
      MajorMinorSmallnessCompatibility δ_M δ_m) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_PathA_QuantitativeContent
    (PathA_QuantitativeHardyLittlewoodContent_of_farey_and_sub_smallnesses
      hFarey hMajor hMinor hCompat)

/-! ### Convenience: a sufficient compatibility instance

The most common way the compatibility constraint is closed is when
*both* coefficients are bounded by `1/2`.  We expose this as a named
helper to make downstream consumers' lives easier. -/

/-- **Sufficient compatibility (half-half)**: if both coefficients are
bounded by `1/2`, the compatibility constraint `δ_M + δ_m < 1` holds
(in the strict form, this requires *at least one* of the bounds to be
strict, which is given by `δ_M < 1/2` *or* `δ_m < 1/2`; we expose the
symmetric `δ_M < 1/2 ∧ δ_m < 1/2` form for simplicity). -/
theorem majorMinorSmallnessCompatibility_of_half_half
    {δ_M δ_m : ℝ}
    (hM : δ_M < 1/2) (hm : δ_m < 1/2) :
    MajorMinorSmallnessCompatibility δ_M δ_m := by
  unfold MajorMinorSmallnessCompatibility
  linarith

/-- **Sufficient compatibility (constant pair)**: if the chosen
coefficients are *specific* values whose sum is `<1`, the compatibility
constraint is immediate.  This is a degenerate but useful form for
downstream consumers that pre-pick the coefficients. -/
theorem majorMinorSmallnessCompatibility_of_sum_lt_one
    {δ_M δ_m : ℝ} (h : δ_M + δ_m < 1) :
    MajorMinorSmallnessCompatibility δ_M δ_m := h

/-! ## Section 15: P5-T6 minor-arc decomposition — Vinogradov-bilinear
    structural sub-Prop

The major-arc side of the witness-form smallness is **pinnable** in
Phase 5 (see `Gdbh.PathA_MajorArc` Section 20:
`pinned_majorArcSmallness_for_farady_family` produces a concrete
`MajorArcSmallnessFromErrorFn` with `δ_M = 1/4`).

The minor-arc side `MinorArcSmallnessFromContribution` is **not**
pinnable at the witness level in Phase 5: Phase 4's
`DirichletApproxCondition` is structurally vacuous, and Phase 5's
Vinogradov Type I / Type II Dirichlet sub-Props reduce to universal-`α`
Props that are equivalent to false.  Closing the minor-arc side
requires Phase 6 work to fix the vacuous Dirichlet condition.

To prepare for that Phase 6 work, we expose here a **decomposition**
of `MinorArcSmallnessFromContribution majorArcs` into a single named
sub-Prop `MinorArcSmallnessFromVinogradovBound majorArcs`, plus a
mechanical assembly theorem
`MinorArcSmallnessFromContribution_of_VinogradovBound`.  The sub-Prop
captures the analytic content of: "an *effective* Vinogradov-bilinear
bound (with explicit constant `δ_m < 1`) produces the minor-arc
smallness".  In Phase 6, the closer of this sub-Prop will be the
effective Vinogradov bound that becomes accessible once the Dirichlet
condition is fixed. -/

/-- **T-Smallness minor-arc sub-Prop (effective Vinogradov-bilinear
bound)**: given an arc family `majorArcs`, the existence of a
threshold `N₁` and a coefficient `δ_m ∈ [0, 1)` such that
`|realMinorContribution majorArcs n| ≤ δ_m · 𝔖(n) · n` for every even
`n > N₁`.

This is *definitionally equivalent* to `MinorArcSmallnessFromContribution
majorArcs` — both are the "minor contribution is small relative to the
singular-series main term" Prop.  We expose it under a distinct name to
mark its dependency on Phase 6's *effective* Vinogradov-bilinear bound
(which, in turn, is blocked by Phase 4's vacuous Dirichlet condition
being fixed).

Phase 6 will close this sub-Prop by:
(a) fixing the vacuous Dirichlet condition in `Gdbh.PathA_MinorArc`,
(b) deriving the effective Vinogradov Type I / Type II bilinear bounds,
(c) packaging them as an effective minor-arc real-contribution bound. -/
def MinorArcSmallnessFromVinogradovBound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) : Prop :=
  ∃ N₁ : Nat, ∃ δ_m : ℝ, 0 ≤ δ_m ∧ δ_m < 1 ∧
    ∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **Minor-arc assembly**: the effective Vinogradov-bilinear sub-Prop
implies the contribution-form sub-Prop (definitionally equivalent;
this is the mechanical "renaming" closer). -/
theorem MinorArcSmallnessFromContribution_of_VinogradovBound
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    (h : MinorArcSmallnessFromVinogradovBound majorArcs) :
    MinorArcSmallnessFromContribution majorArcs := h

/-- **Reverse direction**: the contribution-form sub-Prop implies the
Vinogradov-bilinear sub-Prop (definitionally equivalent).  This shows
that the decomposition is *tight* — no analytic content is lost in
either direction. -/
theorem MinorArcSmallnessFromVinogradovBound_of_Contribution
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    (h : MinorArcSmallnessFromContribution majorArcs) :
    MinorArcSmallnessFromVinogradovBound majorArcs := h

/-- **Logical equivalence** between the two minor-arc sub-Props.  Both
capture the same analytic content; the distinct names exist to track
the *Phase 6 closure path* through effective Vinogradov bounds. -/
theorem MinorArcSmallnessFromVinogradovBound_iff_Contribution
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)} :
    MinorArcSmallnessFromVinogradovBound majorArcs ↔
      MinorArcSmallnessFromContribution majorArcs := Iff.rfl

/-! ### P5-T6 sufficient form: explicit `δ_m < 3/4` produces the
compatibility witness against the pinned `δ_M = 1/4`

The major-arc side pins `δ_M = 1/4` (see
`Gdbh.PathA_MajorArc.pinned_majorArcSmallness_for_farady_family`).  The
compatibility constraint `δ_M + δ_m < 1` then reduces to `δ_m < 3/4`,
which any Phase 6 effective Vinogradov bound easily satisfies (the
expected coefficient is `o(1)` or at worst a small explicit constant).

We expose this as a **stand-alone explicit minor-arc Vinogradov Prop**
that bundles "minor smallness with `δ_m < 3/4`", together with the
mechanical compatibility witness. -/

/-- **Minor-arc sub-Prop with explicit `δ_m < 3/4`**: a refined form of
`MinorArcSmallnessFromVinogradovBound` that *additionally* records
`δ_m < 3/4`.  This is the form actually consumed when pinning against
the major-arc `δ_M = 1/4` to assemble the compatibility constraint. -/
def MinorArcSmallnessFromVinogradovBoundThreeQuarter
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) : Prop :=
  ∃ N₁ : Nat, ∃ δ_m : ℝ, 0 ≤ δ_m ∧ δ_m < 3/4 ∧
    ∀ n : Nat, N₁ < n → Even n →
      |realMinorContribution majorArcs n| ≤
        δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- A three-quarter minor-arc Vinogradov bound implies the (looser)
contribution-form bound: `δ_m < 3/4 < 1`. -/
theorem MinorArcSmallnessFromContribution_of_threeQuarter
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    (h : MinorArcSmallnessFromVinogradovBoundThreeQuarter majorArcs) :
    MinorArcSmallnessFromContribution majorArcs := by
  rcases h with ⟨N₁, δ_m, hδ_m_nn, hδ_m_lt, hbound⟩
  refine ⟨N₁, δ_m, hδ_m_nn, ?_, hbound⟩
  linarith

/-- **Pinned-compatibility witness for the major-arc `δ_M = 1/4`**:
given a three-quarter minor-arc bound, the closure data for the
witness-form smallness's compatibility constraint when paired with
`δ_M = 1/4` is mechanical (`1/4 + δ_m < 1 ↔ δ_m < 3/4`). -/
theorem majorMinorSmallnessCompatibility_quarter_of_threeQuarter
    {δ_m : ℝ} (h_lt : δ_m < 3/4) :
    MajorMinorSmallnessCompatibility (1/4 : ℝ) δ_m := by
  unfold MajorMinorSmallnessCompatibility
  linarith

/-- **Audit-relevant: pinned-major + three-quarter-minor assembly.**
Given a major-arc smallness with `δ_M = 1/4` (the value produced by
`Gdbh.PathA_MajorArc.pinned_majorArcSmallness_for_farady_family`) and a
three-quarter minor-arc bound, the witness-form smallness for the
chosen `(N₀, majorArcs, errorFn)` follows.  Both `δ`'s and the
compatibility constraint are pinned mechanically. -/
theorem pathA_HardyLittlewoodSmallnessForWitness_of_pinned_quarter_threeQuarter
    {N₀ : Nat}
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {errorFn : Nat → ℝ}
    (hMajor : ∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤
        (1/4 : ℝ) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))
    (hMinor : MinorArcSmallnessFromVinogradovBoundThreeQuarter majorArcs) :
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs errorFn := by
  rcases hMinor with ⟨N₁, δ_m, hδ_m_nn, hδ_m_lt, hminor_bound⟩
  refine ⟨N₁, (1/4 : ℝ), δ_m, by norm_num, by norm_num, hδ_m_nn, ?_,
    hMajor, hminor_bound⟩
  -- `1/4 + δ_m < 1` from `δ_m < 3/4`.
  linarith

end Gdbh
