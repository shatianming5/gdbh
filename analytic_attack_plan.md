# Analytic Attack Plan

This is the current high-efficiency route toward the remaining target:

```lean
Gdbh.ExplicitGoldbachLowerBound 100
```

The work is not complete until Lean has a no-argument theorem of
`Gdbh.ExplicitGoldbachLowerBound 100`, a no-argument theorem of
`Gdbh.StrongGoldbach`, and the final certificate passes:

```bash
python3 analytic_handoff_certificate.py CERT.json --require-complete --check-lean
lake build
python3 audit_lean_source.py
python3 audit_lean_axioms.py
```

## 1. Singular Series Lower Bound

Target:

```lean
∀ n : Nat, threshold < n → Even n →
  (coefficient : ℝ) ≤ singularSeries n
```

Efficient path:

- Fix one project-level Goldbach singular-series definition.
- Use a conservative rational lower bound such as `1/4` or `1/8`.
- Prove that all local factors for even `n` are at least `1`.
- Prove the remaining absolute constant lower bound once.

Deliverables:

- `Gdbh/SingularSeries.lean`
- A theorem suitable for
  `obligations.singular_series_lower_bound.lean_declaration`
- A certificate using that theorem.

Current formalized progress:

- `goldbachOddPrimeLocalFactor`
- `goldbachSingularSeriesLocalMultiplier`
- `one_le_goldbachOddPrimeLocalFactor`
- `one_le_goldbachSingularSeriesLocalMultiplier`
- `goldbachSingularSeriesFromBase_lower_bound`
- `goldbachSingularSeriesFromQuarter`
- `one_fourth_le_goldbachSingularSeriesFromQuarter`
- `VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate`
- `VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate`
- `VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate`
- `VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound`
- `VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound`
- `VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate`
- `quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model`
- `quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model_ge_two_threshold`

This proves that the finite odd-prime local correction factors do not decrease
a nonnegative base term, and the current example certificates now Lean-check a
quarter-base singular-series lower bound.  The new quarter canonical HL entry
fixes coefficient `1/4` and `goldbachSingularSeriesFromQuarter` inside Lean, so
that route leaves only the normalized raw Λ error and final threshold coverage
to the analytic side.  The quarter explicit-contamination variant is closer to
the listed core mountain: it keeps the normalized raw Λ error obligation and
asks for an explicit canonical contamination domination threshold, so the final
threshold is just the max of two submitted numeric fields.  Its contamination
side now has a sharper reduction theorem: once `contaminationThreshold >= 2`,
Lean proves the needed `1 <= log n`, so the remaining contamination input is the
explicit model inequality
`K * sqrt(n) * log(n)^3 < (1 - relativeError) * (1/4) * n`; from that, Lean
derives the canonical `contamination_dominated` obligation.  The positive-linear
raw canonical entry is an even more
compressed raw Λ shortcut: the analytic side may instead supply only
`coefficient * n <= RawVonMangoldtGoldbachSum n`, while Lean supplies the
canonical non-prime-prime-power weight-sum bound and the linear contamination
threshold.  Its explicit-contamination variant keeps the raw lower-bound
obligation but asks the analytic side to submit an explicit domination
threshold for the canonical contamination budget, avoiding a bound on
`canonicalLinearContaminationThreshold`.  A new quarter lower-bound
explicit-contamination entry sits between these two views: it keeps the
Hardy-Littlewood main term `goldbachSingularSeriesFromQuarter(n) * n`, but asks
only for the one-sided lower estimate
`(1 - relativeError) * goldbachSingularSeriesFromQuarter(n) * n <= Raw(n)`
instead of the full absolute normalized-error inequality.  Lean then applies
`one_fourth_le_goldbachSingularSeriesFromQuarter` and routes through the
positive-linear explicit-contamination bridge.  The split-threshold positive-linear
canonical major/minor entry is the closest non-DFT Lean surface to the hard
minor-arc step: prove a combined major/minor lower bound and a positive linear
net lower bound, and Lean cancels the minor error before applying the same
canonical contamination bridge.  The major/minor explicit-contamination
variant keeps the same two major/minor obligations but asks the analytic side
for an explicit canonical contamination domination threshold; this avoids
proving an upper bound for the noncomputable
`canonicalLinearContaminationThreshold`.  The
certificate-level templates currently exposed here are:

```bash
python3 analytic_handoff_certificate.py \
  analytic_quarter_canonical_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_quarter_explicit_contamination_canonical_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_quarter_lower_bound_explicit_contamination_canonical_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_positive_linear_raw_canonical_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_positive_linear_raw_explicit_contamination_canonical_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_positive_linear_canonical_major_minor_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_positive_linear_explicit_contamination_canonical_major_minor_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_dft_uniform_minor_sq_positive_linear_explicit_contamination_handoff_certificate.example.json

python3 analytic_handoff_certificate.py \
  analytic_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_handoff_certificate.example.json
```

Any alternate singular-series normalization must still
replace the field and lower-bound theorem together.

Gate:

```bash
lake build
python3 audit_lean_source.py
python3 analytic_handoff_certificate.py CERT.json --check-formalized-lean
```

## 2. Explicit Canonical Threshold

Target:

```lean
estimate.toDirectRawWeightSumLowerBound.threshold ≤ B
```

The current canonical route now exposes a named
`canonicalHLContaminationThreshold` and routes the canonical handoff through a
split-threshold direct raw weight-sum bridge.  This is better than a fully
hidden eventual cutoff, but the threshold is still noncomputable and not yet a
concrete number.

Efficient path:

- Replace `canonicalHLContaminationThreshold` with a computable threshold, or
  prove a concrete upper bound for it.
- Prove that above the concrete threshold:

```text
2 * canonical weight-sum budget * log n
  < ((1 - relativeError) * coefficient) * n
```

- Route the direct threshold through a visible `max` of the analytic threshold
  and contamination threshold.
- If the resulting bound is larger than `100`, expand the finite certificate
  to that bound instead of forcing the analytic threshold downward.

Deliverables:

- An explicit threshold theorem for canonical contamination domination.
- A `derivedThresholdBound.lean_term` for the final certificate.
- If needed, a larger `GoldbachUpTo B` certificate.

Current formalized progress:

- `canonicalHLContaminationThreshold`
- `canonicalHLContaminationThreshold_spec`
- `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold`
- `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toSplitThresholdDirectRawWeightSumLowerBound`
- `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq`
- `VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_le`

Gate:

```bash
python3 analytic_handoff_certificate.py CERT.json --require-complete --check-lean
lake build
```

## 3. Raw Estimate Lemma Ledger

Target:

```lean
∀ n : Nat, threshold < n → Even n →
  |(RawVonMangoldtGoldbachSum n - singularSeries n * (n : ℝ)) /
    (singularSeries n * (n : ℝ))| ≤ relativeError
```

This is the main open analytic core. Before formalizing it, every paper
estimate must be converted into a ledger row.

| Row | Needed Claim | Source | Constants | Threshold | Lean Target | Status |
| --- | --- | --- | --- | --- | --- | --- |
| R1 | Project raw sum equals the paper's `sum Λ(m)Λ(n-m)` | local | exact | none | `rawVonMangoldtGoldbachSum_eq_arithmeticFunction_sum` | normalization theorem formalized; keep the endpoint convention as `Finset.range n.succ` |
| R1b | Project raw sum equals a finite `ZMod (n+1)` Fourier major/minor decomposition for any chosen frequency partition | local | exact | none | `DiscreteCircleMethod.rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor` | formalized; use `VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate` to remove `raw_decomposition` as an external analytic obligation |
| R1c | Complex major/minor frequency bounds imply the real raw-decomposition bounds needed by the handoff | local | exact | none | `DiscreteCircleMethod.VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate` | formalized; major/minor arc estimates can now target complex norms of the Fourier sums |
| R1d | Fourier contributions are explicit DFT-square sums, and minor arc norm follows from summed pointwise or square-sum bounds | local | exact | none | `DiscreteCircleMethod.rawVonMangoldtGoldbachSum_complex_eq_dft_square_sum`, `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_square_term_bound`, `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sq`, `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound`, `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sum_sq` | formalized; minor arc ledger rows can now state bounds for `1/(n+1) * e(kn/(n+1)) * S(k)^2`, directly prove `‖S(k)‖ <= M(n)` on minor frequencies and `M(n)^2 <= minorArcError(n)` without a separate nonnegativity declaration on the uniform-minor-square DFT routes, or use an L2 square-sum bound `(1/(n+1))*sum_minor B(k)^2 <= minorArcError(n)` |
| R1e | Major arc complex approximation can be proved termwise against a model sum | local | exact | none | `DiscreteCircleMethod.majorArcComplexApproximationBound_of_dft_square_term_approximation` | formalized; major arc ledger rows can now approximate each DFT-square major frequency by a model term, prove the model sum is close to `goldbachSingularSeriesFromQuarter(n) * n`, and let Lean add the errors |
| R1f | DFT-level model and L2 minor estimates directly instantiate the complex Fourier handoff | local | exact | none | `DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate`, `DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate`, `DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate` | formalized; this packages major termwise model estimates, minor frequency-dependent square-sum bounds, and total linear error into the closest current Lean entry for a literal circle-method proof; the uniform-minor variant reduces the minor L2 field to a uniform DFT bound, a minor-frequency count bound, and one scalar square-error inequality; the uniform-minor-square variant uses the trivial frequency-count bound internally and only asks for the uniform DFT bound plus `minorArcDftBound(n)^2 <= minorArcError(n)` |
| R1g | Positive-linear DFT lower bound directly implies the raw Λ lower-bound handoff | local | exact | none | `DiscreteCircleMethod.VonMangoldtFourierPositiveLinearCanonicalLowerBound`, `DiscreteCircleMethod.VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound` | formalized; if the analytic proof gives `Major(n) >= coefficient*n + minorArcError(n)` and a uniform minor DFT bound with `M(n)^2 <= minorArcError(n)`, Lean bypasses the relative-error/singular-series handoff and routes straight to the positive-linear raw Λ bridge; the DFT positive-linear structures now use the squared-bound bridge directly, so no separate `0 <= M(n)` field is required there; the explicit-contamination variant also accepts a numeric `contaminationThreshold` and pointwise contamination domination theorem instead of a noncomputable canonical threshold coverage proof; the fixed-square-error variant sets `minorArcError := M(n)^2` inside Lean, so the analytic side no longer submits a separate square-error obligation |
| R1h | One-sided quarter Hardy-Littlewood lower bound directly implies the raw Λ lower-bound handoff | local | exact | none | `VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate` | formalized; if the analytic proof gives `(1 - relativeError) * goldbachSingularSeriesFromQuarter(n) * n <= RawVonMangoldtGoldbachSum n`, Lean uses the quarter singular-series lower bound to obtain the positive-linear raw Λ handoff and avoids proving the upper side of a normalized absolute-error estimate |
| R1i | One-sided quarter major/minor bounds imply the one-sided raw Λ lower-bound handoff | local | exact | none | `raw_relative_lower_bound_of_major_minor_lower_bound`, `VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate` | formalized; prove `Raw = Major + Minor`, `Major >= (1-relativeError)*goldbachSingularSeriesFromQuarter(n)*n + minorArcError(n)`, and `Minor >= -minorArcError(n)`, and Lean derives the one-sided raw lower bound before applying explicit canonical contamination subtraction |
| R1j | Fourier/DFT one-sided quarter major/minor bounds imply the same raw Λ lower-bound handoff | local | exact | none | `DiscreteCircleMethod.VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate`, `DiscreteCircleMethod.VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate` | formalized; Lean supplies `Raw = FourierMajor + FourierMinor`, converts a complex minor norm bound into the one-sided real minor lower bound, and the DFT variants reduce minor control to `‖S(k)‖ <= M(n)` plus either `M(n)^2 <= minorArcError(n)` or fixed loss `M(n)^2`; the fixed-error route now also accepts the standard off-major-arcs minor statement via `DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs`, or a global nonzero-frequency DFT bound plus `0 ∈ majorArcs(n)` via `DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs`; the sqrt-log contamination variant replaces direct `contaminationDominated` by `contaminationThreshold >= 2` and the explicit `sqrt(n)*log(n)^3` model inequality |
| R2 | Major arcs produce `singularSeries(n) * n` up to explicit error | paper | explicit | explicit | major-arc theorem | open |
| R3 | Minor arcs are uniformly bounded for every even `n > T` | paper/new proof | explicit | explicit | minor-arc theorem | open |
| R4 | Major/minor errors combine to at most `relativeError * mainTerm` | derived | explicit | explicit | `raw_abs_error_bound_of_major_minor_decomposition`, then `raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound` plus total-error theorem | decomposition and total-error conversions formalized; analytic input open |
| R5 | Final normalized error theorem with `relativeError < 1` | derived | explicit | explicit | `raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound` plus certificate theorem | conversion formalized; analytic input open |

Rows that prove only average, almost-all, heuristic, or ineffective asymptotic
results are insufficient for `Gdbh.ExplicitGoldbachLowerBound 100`.

Current formalized progress:

- `raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound`
- `rawVonMangoldtGoldbachSum_eq_weight_sum`
- `rawVonMangoldtGoldbachSum_eq_arithmeticFunction_sum`
- `DiscreteCircleMethod.zmodDftConvolution_apply`
- `DiscreteCircleMethod.zmodConvolution_eq_fourier_sum`
- `DiscreteCircleMethod.zmodVonMangoldtConvolution_natCast_eq_raw`
- `DiscreteCircleMethod.rawVonMangoldtGoldbachSum_complex_eq_dft_square_sum`
- `DiscreteCircleMethod.rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor`
- `DiscreteCircleMethod.rawVonMangoldtDftSquareFourierTerm_norm`
- `DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution_norm_sub_model_sum_le_of_dft_square_term_approx_bound`
- `DiscreteCircleMethod.majorArcComplexApproximationBound_of_dft_square_term_approximation`
- `DiscreteCircleMethod.majorArcComplexApproximationBound_of_dft_square_term_approximation_exact_model`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_norm_sq`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_bound_sq`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_square_term_bound`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_square_term_bound`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_norm_sq_sum`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sum_sq`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq`
- `DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq_of_uniform_bound`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_and_card_bound`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sq`
- `DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound`
- `DiscreteCircleMethod.VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate`
- `DiscreteCircleMethod.real_abs_re_sub_mul_le_complex_norm_sub_ofReal_mul`
- `DiscreteCircleMethod.real_abs_re_le_complex_norm`
- `DiscreteCircleMethod.VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate`
- `DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate`
- `DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate`
- `DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components`
- `VonMangoldtHardyLittlewoodAbsErrorEstimate`
- `VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate`
- `VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le`
- `raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound`
- `VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate`
- `VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate`
- `VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate`
- `VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components`
- `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate`
- `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components`
- `raw_abs_error_bound_of_major_minor_decomposition`
- `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate`
- `VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components`

This means the major/minor arc package can target the usual absolute
total-error inequality

```lean
|RawVonMangoldtGoldbachSum n - singularSeries n * (n : ℝ)| ≤
  relativeError * (singularSeries n * (n : ℝ))
```

and Lean will convert it to the normalized division-form obligation, provided
the same `singularSeries` has the positive lower bound recorded in the
certificate.

The split-threshold canonical major/minor route can now keep three analytic
cutoffs separate:

```lean
singularSeriesThreshold
majorMinorThreshold
totalAnalyticErrorThreshold
```

Lean takes their maximum, adds the canonical contamination threshold, and
exposes a component-wise final threshold theorem for the finite-certificate
handoff.  If the analytic proof uses the fixed quarter-base normalization, the
quarter split entry removes the separate singular-series threshold and lower
bound fields; R2/R3 then target only the `goldbachSingularSeriesFromQuarter`
main term.  The newer quarter decomposition entry is narrower still: it lets
R2/R3 provide a raw decomposition

```lean
RawVonMangoldtGoldbachSum n =
  majorArcContribution n + minorArcContribution n
```

plus separate bounds on `|majorArcContribution n -
goldbachSingularSeriesFromQuarter n * n|` and
`|minorArcContribution n|`.  Lean then applies the triangle inequality to
obtain the existing `|Raw-main| <= majorArcError + minorArcError` obligation.
If the paper ledger gives total error in the common linear form
`majorArcError n + minorArcError n <= epsilon * n`, the
`total_analytic_error_bound_of_quarter_linear_error_bound` bridge now converts
that into the required main-term-relative total-error bound from
`epsilon <= relativeError / 4`, using the already formalized
`goldbachSingularSeriesFromQuarter n >= 1/4`.
This entry is now also available as a machine-checkable handoff template:

```bash
python3 analytic_handoff_certificate.py \
  analytic_decomposition_handoff_certificate.example.json
```

The template remains incomplete until those four analytic obligations and the
final `derivedThresholdBound` are formalized.

There is now also a Lean-only Fourier decomposition route.  Given any dependent
choice of major frequency sets

```lean
majorArcs : (n : Nat) -> Finset (ZMod n.succ)
```

Lean defines real-valued major and minor contributions as the real parts of the
finite inverse-DFT sums and proves

```lean
RawVonMangoldtGoldbachSum n =
  rawVonMangoldtFourierMajorArcContribution majorArcs n +
  rawVonMangoldtFourierMinorArcContribution majorArcs n
```

for every `n`.  The object
`VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate` uses this
identity automatically, so the remaining analytic work on that route is only:
major arc approximation, minor arc contribution, total linear error
`<= epsilon*n`, and canonical contamination threshold coverage.
The complex variant
`VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate` is the
preferred target for literal circle-method estimates: it asks for bounds on
complex norms of the finite major/minor frequency sums, and Lean converts those
to real-part bounds via `Complex.abs_re_le_norm`.
The DFT/L2 specialization
`DiscreteCircleMethod.VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate`
is now also available as the closest machine-readable certificate target for
this route.  Its JSON template is:

```bash
python3 analytic_handoff_certificate.py \
  analytic_dft_model_l2_handoff_certificate.example.json
```

That template remains incomplete until the termwise major DFT-square model
bounds, model-sum bound, major error summation, minor DFT pointwise bound,
minor L2 square-sum bound, total linear error bound, and final contamination
threshold coverage are all formalized.
For the common minor-arc shape where the paper gives a uniform bound
`‖S(k)‖ <= M(n)` on every minor frequency, the Lean object
`DiscreteCircleMethod.VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate`
now converts this plus a frequency-count bound and
`countBound(n) * |1/(n+1)| * M(n)^2 <= minorArcError(n)` into the DFT/L2
square-sum field.  The certificate-backed
`DiscreteCircleMethod.VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate`
uses the trivial `card(minor) <= n+1` bound internally and accepts the coarser
single condition `M(n)^2 <= minorArcError(n)`.  The JSON template for the
frequency-count version is:

```bash
python3 analytic_handoff_certificate.py \
  analytic_dft_model_uniform_minor_handoff_certificate.example.json
```

The coarser square-only certificate template is:

```bash
python3 analytic_handoff_certificate.py \
  analytic_dft_model_uniform_minor_sq_handoff_certificate.example.json
```

For the direct positive-linear DFT route, the explicit-contamination template
is:

```bash
python3 analytic_handoff_certificate.py \
  analytic_dft_uniform_minor_sq_positive_linear_explicit_contamination_handoff_certificate.example.json
```

It asks for the pointwise major lower bound
`coefficient*n + minorArcError(n) <= Major(n)`, the uniform minor DFT bound
and square domination `M(n)^2 <= minorArcError(n)`, plus explicit domination
of the canonical prime-power contamination budget.  The final threshold is
then built from `majorArcThreshold`, `minorArcThreshold`, and
`contaminationThreshold`.  For `contaminationThreshold >= 2`, the template can
derive the explicit contamination domination from the formalized helper
`canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold`,
so the analytic side may instead submit the scalar model inequality
`C * sqrt(n) * log(n)^3 < coefficient*n`.

The narrower fixed-square-error version is:

```bash
python3 analytic_handoff_certificate.py \
  analytic_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_handoff_certificate.example.json
```

It asks for
`coefficient*n + minorArcDftBound(n)^2 <= Major(n)`, the uniform minor DFT
bound, and the same explicit or derived contamination domination.  Lean sets
the minor error to `minorArcDftBound(n)^2` internally, so there is no separate
`minorArcError` field and no `minor_arc_dft_bound_sq_error_bound` obligation.
For the one-sided quarter major/minor fixed-error route, the same minor DFT
bound may now be supplied in the usual off-major-arcs form
`∀ k, k ∉ majorArcs(n) -> ‖S(k)‖ <= M(n)`; Lean rewrites it to the
`zmodMinorFrequencies` form through
`DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs`.
If the analytic estimate is stated globally for every nonzero frequency,
submit that as `∀ k, k ≠ 0 -> ‖S(k)‖ <= M(n)` together with
`0 ∈ majorArcs(n)`; Lean then uses
`DiscreteCircleMethod.minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs`
to recover the same minor-frequency handoff field.

Gate:

- Every row has a source, quantifier range, constants, threshold, and Lean
  target.
- No row depends on GRH, Hardy-Littlewood conjectures, or random models unless
  the target is explicitly changed to a conditional theorem.

## 4. Major Arc Package

Start this only after the ledger identifies a concrete source and constants.

Deliverables:

- A Lean statement for the main term.
- A `majorArcError` function with explicit constants.
- A theorem feeding the normalized Hardy-Littlewood or major/minor interface.

Gate:

- No asymptotic notation remains in the Lean target.
- The theorem is uniform on the required even range.

## 5. Minor Arc Package

This is the main peak.

Deliverables:

- A `minorArcError` function with explicit constants.
- A pointwise theorem for every even `n > threshold`.
- A final theorem proving the normalized raw error bound with
  `relativeError < 1`.

Gate:

- The theorem is pointwise, not almost-all.
- The threshold is concrete.
- The threshold can be compared with the finite certificate bound.

## 6. Finite Certificate Expansion

Do this only after the analytic threshold is known.

Deliverables:

- A `GoldbachUpTo B` certificate with `B` covering the analytic threshold.
- A manifest tying the generator command and certificate hash together.

Gate:

```bash
python3 verify_goldbach.py B --interval-start 2 --chunk-size CHUNK --export-lean ...
lake build
```

## 7. Final Handoff

Deliverables:

- Complete analytic certificate JSON.
- Generated Lean wrapper.
- No-argument theorem of `Gdbh.ExplicitGoldbachLowerBound 100`.
- No-argument theorem of `Gdbh.StrongGoldbach`.

Gate:

```bash
python3 analytic_handoff_certificate.py CERT.json --require-complete --check-lean --definition-name NAME
python3 analytic_handoff_certificate.py CERT.json --export-lean Gdbh/FinalGoldbach.lean --definition-name NAME
lake build
python3 audit_lean_source.py
python3 audit_lean_axioms.py
```

Only after this gate passes can `proof_status.json` move from
`"complete": false` to `"complete": true`.
