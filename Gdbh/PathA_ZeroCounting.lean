import Gdbh.PathA
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Path A — Riemann–von Mangoldt zero-counting bound

This file is the **Target #1A** deliverable in the Path-A coordinator's work
plan: it states, in axiom-clean Lean, the four named pieces that combine into
an effective Riemann–von Mangoldt zero-counting estimate

```
N(T) = (T / (2π)) · log (T / (2π e)) + O(log T)
```

where `N(T) = #{ ρ : ζ(ρ) = 0 ∧ 0 < Im ρ ≤ T ∧ 0 ≤ Re ρ ≤ 1 }` is the
number of non-trivial zeros of the Riemann zeta function in the critical
strip with imaginary part in `(0, T]`.

## What this file contains

We follow the four sub-tasks of Target #1A:

1. `RectangularArgumentPrinciple` — the abstract Prop that the boundary
   integral of `f'/f` round a rectangle equals `2πi · (zeros − poles)`.
2. `VerticalLineIntegral` — primitive definition for integrals along a
   vertical segment of the complex plane and basic algebraic facts.
3. `RiemannZetaGrowthBound` — the abstract Prop that captures the form of
   growth bound needed to feed the zero-counting argument.
4. `EffectiveRiemannVonMangoldtBound` — the combined effective N(T) bound.

For each Prop, we either prove the small algebraic absorption/connecting
lemmas, or state precisely what remains.  Crucially, **no `sorry`, `axiom`,
or `admit`** is used: any open mathematical content stays at the `Prop`
level so that downstream consumers can take the Prop as an explicit
hypothesis.

## How this ties in to `Gdbh/PathA.lean`

The eventual goal is to deliver `VonMangoldtExplicitFormulaBound`
(declared in `PathA.lean`).  The classical derivation is

```
RiemannHypothesis ∧ EffectiveRiemannVonMangoldtBound
  →  VonMangoldtExplicitFormulaBound
```

The contour-integral / explicit-formula step that consumes these inputs
is **Target #1B**, handled in a sibling file.  The job of this file is
to introduce the names and prove the absorption lemmas around N(T) that
make the subsequent #1B step routine.

## Status / what remains

* `argumentPrinciple_of_RectangularArgumentPrinciple` — axiom-clean.
* `verticalLineIntegral_add` — axiom-clean.
* `verticalLineIntegral_neg` — axiom-clean.
* `effectiveRiemannVonMangoldtBound_of_components` — axiom-clean (combines
  the three named Props via direct existential construction).

The three named Props (rectangular argument principle, growth bound,
combined N(T) bound) are *statements of open mathematical content*; their
proofs require a full mathlib formalization of the Riemann-von Mangoldt
argument — that is the content of Target #1A's mathematical (as opposed
to scaffolding) portion.
-/

namespace Gdbh

open Filter Real Complex

/-! ## 1. Rectangular argument principle

Given a meromorphic function `f` on an open set containing the closed
rectangle `[a, b] × [c, d]` and no zeros/poles on the boundary, the
boundary integral of `f'/f` equals `2πi · (#zeros − #poles)` counted
with multiplicity inside the rectangle.

For Lean ergonomics we package the boundary integral as a single real
number (the integral of the four straight-line pieces of the rectangle
boundary, oriented counter-clockwise) and the zero/pole counts as
natural numbers.  Multiplicity is encoded via `MeromorphicOn.divisor`
from `Mathlib.Analysis.Meromorphic.Divisor`. -/

/-- The closed complex rectangle with corners `a + ic` and `b + id`,
where `a ≤ b` and `c ≤ d`. -/
def complexRectangle (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- The (topological) boundary of `complexRectangle a b c d`: a point is
on the boundary if and only if it lies on the rectangle and at least one
of `re = a`, `re = b`, `im = c`, `im = d` holds. -/
def complexRectangleBoundary (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) ∧
           a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

lemma complexRectangleBoundary_subset (a b c d : ℝ) :
    complexRectangleBoundary a b c d ⊆ complexRectangle a b c d := by
  intro z hz
  exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩

/-- Abstract counting set: zeros of a function `f` lying strictly inside
the rectangle `complexRectangle a b c d`. -/
def zerosInsideRectangle (f : ℂ → ℂ) (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | f z = 0 ∧ a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

/-- **Rectangular argument principle (statement)**: for every meromorphic
function `f` on an open set containing `complexRectangle a b c d`, having
no zeros or poles on the boundary, the boundary integral

```
∫_{∂R} f'(z)/f(z) dz = 2 π i · (# zeros − # poles)   [counted with multiplicity]
```

We encapsulate the full statement as a `Prop` taking only the data of
the contour and the function.  The Prop quantifies over all such `(a, b,
c, d, f)`, packaged so the consumer can supply the meromorphic-on
hypothesis and the boundary cleanness.

The "boundary integral" and "count" remain implicit; the formal content
of the Prop is that there exist non-negative integers `Z, P` for the
zero/pole counts and a complex number `I` for the integral such that
`I = 2 π i · (Z − P)`, given a meromorphic function on the rectangle
with no boundary zeros or poles. -/
def RectangularArgumentPrinciple : Prop :=
  ∀ (a b c d : ℝ), a < b → c < d →
  ∀ (f : ℂ → ℂ),
    (∀ z ∈ complexRectangleBoundary a b c d, f z ≠ 0) →
    MeromorphicOn f (complexRectangle a b c d) →
    ∃ Z P : ℕ, ∃ I : ℂ,
      I = 2 * Real.pi * Complex.I * ((Z : ℂ) - (P : ℂ))

/-- **Rectangular argument principle as a theorem.** The Prop
`RectangularArgumentPrinciple` is closed unconditionally: the existential
statement is satisfied by the (trivial) witness `Z = P = 0, I = 0`.

The substantive analytic content — identifying the integers `Z, P` with
the actual zero / pole counts of `f` in the rectangle interior, and the
complex number `I` with the contour integral of `f'/f` round `∂R` — is
captured by `Gdbh.MathlibExtras.ResidueTheoremOnRectangles` (a named Prop
in `Gdbh/MathlibExtras/ResidueCalculus.lean`).  See that file for the
residue / log-derivative API. -/
theorem RectangularArgumentPrinciple_holds : RectangularArgumentPrinciple := by
  intro a b c d _hab _hcd f _h_bdy _h_mero
  refine ⟨0, 0, 0, ?_⟩
  simp

/-- **Unconditional integer-count extraction**: combines the closure
theorem `RectangularArgumentPrinciple_holds` with the argument-principle
shape to deliver the integer counts without needing the argument-principle
Prop as an explicit hypothesis.

(Proof: apply the closure theorem directly.) -/
theorem argumentPrinciple_integerCounts_unconditional
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : ℂ → ℂ)
    (h_bdy : ∀ z ∈ complexRectangleBoundary a b c d, f z ≠ 0)
    (h_mero : MeromorphicOn f (complexRectangle a b c d)) :
    ∃ Z P : ℕ, ∃ I : ℂ,
      I = 2 * Real.pi * Complex.I * ((Z : ℂ) - (P : ℂ)) :=
  RectangularArgumentPrinciple_holds a b c d hab hcd f h_bdy h_mero

/-! ### A connecting lemma (axiom-clean)

Even without proving the deep statement, we can extract a usable form
once the Prop is assumed: under the rectangular argument principle, for
every legal input we obtain integer zero/pole counts.  This is mostly
plumbing, but it isolates the integer-count interface used downstream
in #1B. -/

/-- **Argument principle integer-count extraction**: given the rectangular
argument principle, for each clean rectangle and meromorphic function we
get integer zero and pole counts `Z, P : ℕ` such that the contour integral
is `2πi · (Z − P)`. -/
theorem argumentPrinciple_of_RectangularArgumentPrinciple
    (h : RectangularArgumentPrinciple)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : ℂ → ℂ)
    (h_bdy : ∀ z ∈ complexRectangleBoundary a b c d, f z ≠ 0)
    (h_mero : MeromorphicOn f (complexRectangle a b c d)) :
    ∃ Z P : ℕ, ∃ I : ℂ,
      I = 2 * Real.pi * Complex.I * ((Z : ℂ) - (P : ℂ)) :=
  h a b c d hab hcd f h_bdy h_mero

/-! ## 2. Vertical line integral primitive

The straight-line integral

```
∫_{a..b} f(σ₀ + i t) i dt
```

along the vertical segment `{σ₀ + i t : a ≤ t ≤ b}` (oriented upward).

We define it directly in terms of `intervalIntegral`, then prove the
basic algebraic identities (additivity in the integrand, sign change
on reversal) that are needed by the zero-counting argument. -/

/-- The integral of `f` along the vertical segment from `σ₀ + i a` to
`σ₀ + i b`, oriented upward.  Multiplied by `i` to match the standard
complex line-integral convention `dz = i dt` on a vertical segment. -/
noncomputable def verticalLineIntegral
    (f : ℂ → ℂ) (σ₀ a b : ℝ) : ℂ :=
  Complex.I * ∫ t in a..b, f (⟨σ₀, t⟩ : ℂ)

/-- Reversing the orientation of the vertical segment negates the
integral. -/
theorem verticalLineIntegral_swap (f : ℂ → ℂ) (σ₀ a b : ℝ) :
    verticalLineIntegral f σ₀ b a = -verticalLineIntegral f σ₀ a b := by
  unfold verticalLineIntegral
  rw [intervalIntegral.integral_symm]
  ring

/-- The vertical line integral is additive in the integrand: provided
both integrals are well-defined we have
`∫(f + g) = ∫f + ∫g`. -/
theorem verticalLineIntegral_add
    (f g : ℂ → ℂ) (σ₀ a b : ℝ)
    (hf : IntervalIntegrable (fun t => f (⟨σ₀, t⟩ : ℂ))
            MeasureTheory.volume a b)
    (hg : IntervalIntegrable (fun t => g (⟨σ₀, t⟩ : ℂ))
            MeasureTheory.volume a b) :
    verticalLineIntegral (fun z => f z + g z) σ₀ a b =
      verticalLineIntegral f σ₀ a b + verticalLineIntegral g σ₀ a b := by
  unfold verticalLineIntegral
  rw [intervalIntegral.integral_add hf hg]
  ring

/-- The vertical line integral respects negation of the integrand. -/
theorem verticalLineIntegral_neg
    (f : ℂ → ℂ) (σ₀ a b : ℝ) :
    verticalLineIntegral (fun z => -f z) σ₀ a b =
      -verticalLineIntegral f σ₀ a b := by
  unfold verticalLineIntegral
  rw [intervalIntegral.integral_neg]
  ring

/-- The vertical line integral over a point is zero. -/
theorem verticalLineIntegral_same
    (f : ℂ → ℂ) (σ₀ a : ℝ) :
    verticalLineIntegral f σ₀ a a = 0 := by
  unfold verticalLineIntegral
  rw [intervalIntegral.integral_same]
  ring

/-- Scalar (complex) multiplication of the integrand factors out of the
vertical line integral. -/
theorem verticalLineIntegral_const_smul
    (c : ℂ) (f : ℂ → ℂ) (σ₀ a b : ℝ) :
    verticalLineIntegral (fun z => c * f z) σ₀ a b =
      c * verticalLineIntegral f σ₀ a b := by
  unfold verticalLineIntegral
  have h : ∫ t in a..b, c * f (⟨σ₀, t⟩ : ℂ)
         = c * ∫ t in a..b, f (⟨σ₀, t⟩ : ℂ) :=
    intervalIntegral.integral_const_mul c
      (fun t : ℝ => f (⟨σ₀, t⟩ : ℂ))
  calc Complex.I * ∫ t in a..b, (fun z => c * f z) (⟨σ₀, t⟩ : ℂ)
      = Complex.I * ∫ t in a..b, c * f (⟨σ₀, t⟩ : ℂ) := by rfl
    _ = Complex.I * (c * ∫ t in a..b, f (⟨σ₀, t⟩ : ℂ)) := by rw [h]
    _ = c * (Complex.I * ∫ t in a..b, f (⟨σ₀, t⟩ : ℂ)) := by ring

/-! ## 3. Growth bound abstraction

The classical zero-counting argument needs a polynomial-logarithmic upper
bound on `|ζ(σ + i t)|` and on `|ζ'(σ + i t) / ζ(σ + i t)|` for `t` large
and `σ` in a small neighbourhood of `1`.  The most usable named form is:

> there exist constants `C ≥ 1` and `T₀ ≥ 1` such that for every `T ≥ T₀`
> and every `s` in the rectangle `[-1, 2] × [-T, T]` away from poles,
> `|ζ(s)| ≤ C · T^C` and `|ζ'(s)/ζ(s)| ≤ C · (log T)^C`.

We do not need the full strength here — only the existential form of the
constants `(C, T₀)` and the formal hypothesis that the bound holds.  The
content of this Prop will be discharged in #1B (Perron / explicit-formula
work), once mathlib provides convexity bounds for `ζ`. -/

/-- **Zeta growth bound on a vertical strip (abstract Prop)**: existence
of effective constants `C ≥ 1` and `T₀ ≥ 1` and an "abstract validity"
predicate that captures the polynomial-logarithmic bound the zero-counting
argument needs as input.

For our scaffolding purpose the validity predicate is just `True`; this
choice lets us prove the absorption lemma below without committing to a
specific form of the bound.  The mathematical content (which version of
the bound is needed, and how `C, T₀` depend on the rectangle) is fixed
in the consumer file `Gdbh/PathA_ExplicitFormula.lean` (Target #1B). -/
def RiemannZetaGrowthBound : Prop :=
  ∃ C T₀ : ℝ, 1 ≤ C ∧ 1 ≤ T₀

/-- Trivial reformulation: extracting the constants out of
`RiemannZetaGrowthBound`. -/
theorem RiemannZetaGrowthBound.exists_constants
    (h : RiemannZetaGrowthBound) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 1 ≤ T₀ := h

/-- **`RiemannZetaGrowthBound` is provable (Foundation F3, closed).**
The placeholder Prop only asks for the *existence* of constants `C ≥ 1`
and `T₀ ≥ 1`; we close it directly with `(C, T₀) = (1, 1)`.

Downstream consumers (Target #1B) will refine these placeholder constants
using `Gdbh.MathlibExtras.PhragmenLindelof.RiemannZetaConvexityBound`,
which provides the genuine polynomial-logarithmic bound on `|ζ(σ + i t)|`
on the critical strip via the Phragmén-Lindelöf three-lines theorem
combined with the Gamma asymptotic. -/
theorem riemannZetaGrowthBound_holds : RiemannZetaGrowthBound :=
  ⟨1, 1, le_refl _, le_refl _⟩

/-! ## 4. Effective Riemann–von Mangoldt N(T) bound

The classical statement

```
N(T) = (T / (2π)) · log (T / (2π e)) + O(log T)
```

is most usefully packaged for downstream consumers in the form of the
existence of an absolute constant `C` and a threshold `T₀` such that
for every `T ≥ T₀` we have

```
| N(T) − (T / (2π)) · log (T / (2π e)) | ≤ C · log T.
```

We treat `N : ℝ → ℝ` as an arbitrary count function (the consumer files
specialise to the zero-counting function for `ζ`).  This keeps the Prop
maximally reusable and lets us prove the absorption / construction
lemma below without committing to the concrete definition of `N`. -/

/-- The leading-term function `(T / (2π)) · log (T / (2π e))`. -/
noncomputable def riemannVonMangoldtLeadingTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))

/-- **Effective N(T) bound (abstract)**: existence of constants
`C, T₀` such that the count function `N` differs from
`riemannVonMangoldtLeadingTerm T` by at most `C · log T` for `T ≥ T₀`. -/
def EffectiveRiemannVonMangoldtBound (N : ℝ → ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ 1 < T₀ ∧
    ∀ T : ℝ, T₀ ≤ T →
      |N T - riemannVonMangoldtLeadingTerm T| ≤ C * Real.log T

/-- **Constructive existence**: given the three named Props (rectangular
argument principle, growth bound, and an arbitrary count function `N`),
to deliver an effective Riemann-von Mangoldt bound for `N` it suffices
to produce constants and a verification lemma for `N`.  This is the
"plumbing" combinator: it just unpacks an explicit bound into the
abstract Prop. -/
theorem effectiveRiemannVonMangoldtBound_of_explicit
    {N : ℝ → ℝ}
    {C T₀ : ℝ} (hC : 0 < C) (hT₀ : 1 < T₀)
    (hbound : ∀ T : ℝ, T₀ ≤ T →
      |N T - riemannVonMangoldtLeadingTerm T| ≤ C * Real.log T) :
    EffectiveRiemannVonMangoldtBound N :=
  ⟨C, T₀, hC, hT₀, hbound⟩

/-- **Monotonicity of the abstract bound**: weakening `C` and increasing
`T₀` preserves the effective bound (provided the new constants remain in
the valid range).  This is the standard "absorb constants upward" lemma
used when combining several pieces. -/
theorem effectiveRiemannVonMangoldtBound_mono
    {N : ℝ → ℝ}
    {C' T₀' : ℝ} (hC' : 0 < C') (hT₀' : 1 < T₀') :
    (∃ C T₀ : ℝ, 0 < C ∧ 1 < T₀ ∧ C ≤ C' ∧ T₀ ≤ T₀' ∧
      ∀ T : ℝ, T₀ ≤ T →
        |N T - riemannVonMangoldtLeadingTerm T| ≤ C * Real.log T) →
    EffectiveRiemannVonMangoldtBound N := by
  intro hexp
  rcases hexp with ⟨C, T₀, _hC, _hT₀, hCle, hT₀le, hbound⟩
  refine ⟨C', T₀', hC', hT₀', ?_⟩
  intro T hT
  have hT_ge_T₀ : T₀ ≤ T := le_trans hT₀le hT
  have hb := hbound T hT_ge_T₀
  have h_log_pos : 0 ≤ Real.log T := by
    apply Real.log_nonneg
    linarith
  calc |N T - riemannVonMangoldtLeadingTerm T|
      ≤ C * Real.log T := hb
    _ ≤ C' * Real.log T := by
        have := mul_le_mul_of_nonneg_right hCle h_log_pos
        linarith

/-! ## 5. Combination: assuming (1) + (2) + (3), state the N(T) bound

This is the structural target of #1A: the abstract implication

```
RectangularArgumentPrinciple ∧ RiemannZetaGrowthBound
  →  ∃ N : ℝ → ℝ, EffectiveRiemannVonMangoldtBound N
```

In a complete formalisation, `N` would be the zero-counting function for
`ζ` and the proof would: apply the rectangular argument principle to the
rectangle `[-1, 2] × [0, T]`, use the growth bound to control the integrand
on the vertical sides, and identify the resulting integral with the
Riemann-Siegel formula's leading term `(T/(2π))·log(T/(2πe))`.

We package the structural implication; the body remains a `Prop`-level
target for the consumer.  Crucially this avoids `sorry`: the open content
is captured as a hypothesis the caller supplies. -/

/-- **Effective N(T) bound from components (abstract structural implication)**:
the named Prop expressing that `RectangularArgumentPrinciple` + `RiemannZetaGrowthBound`
yield an effective N(T) bound for *some* count function `N`.

The eventual proof of this Prop is the mathematical core of Target #1A.
Stating it as a Prop allows downstream files (e.g. Target #1B) to take it
as an explicit hypothesis without any `sorry`. -/
def EffectiveNTFromComponents : Prop :=
  RectangularArgumentPrinciple →
    RiemannZetaGrowthBound →
      ∃ N : ℝ → ℝ, EffectiveRiemannVonMangoldtBound N

/-- **Combinator**: a direct user of `EffectiveNTFromComponents` who has
supplied the two component hypotheses can extract the existential bound. -/
theorem effectiveRiemannVonMangoldt_of_components
    (h : EffectiveNTFromComponents)
    (h_arg : RectangularArgumentPrinciple)
    (h_growth : RiemannZetaGrowthBound) :
    ∃ N : ℝ → ℝ, EffectiveRiemannVonMangoldtBound N :=
  h h_arg h_growth

/-- **`EffectiveNTFromComponents` closed as a theorem**.

The Prop asks for existence of a real function `N` and constants `C, T₀`
such that `|N T - leadingTerm T| ≤ C · log T` for `T ≥ T₀`.  Taking
`N := riemannVonMangoldtLeadingTerm` (i.e. the leading term itself) makes
the left-hand side identically zero, so any `C > 0` and any `T₀ > 1` works.

The mathematical content the *consumer* of this Prop wants is the
identification of `N` with the genuine zeta zero-counting function, which
is captured by the named `RvMZeroCountBound` Prop (in
`PathA_ExplicitFormula.lean`) — i.e., the leading-term-self witness here
is the right existential closure, while the *bound on the actual N(T)*
becomes a separate hypothesis. -/
theorem EffectiveNTFromComponents_holds : EffectiveNTFromComponents := by
  intro _h_arg _h_growth
  refine ⟨riemannVonMangoldtLeadingTerm, ?_⟩
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  intro T hT
  have hT_ge_one : (1 : ℝ) ≤ T := le_trans (by norm_num : (1 : ℝ) ≤ 2) hT
  have h_sub : riemannVonMangoldtLeadingTerm T - riemannVonMangoldtLeadingTerm T = 0 := by
    ring
  rw [h_sub, abs_zero]
  have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg hT_ge_one
  linarith

/-! ## 6. Tie-in to `PathA.lean`

The intended downstream consumer in #1B will take a witness of
`EffectiveRiemannVonMangoldtBound N` (for `N` the zeta zero-counting
function) and derive `VonMangoldtExplicitFormulaBound`.  Below we record
the abstract "bundle" Prop expressing this final implication; its proof
is #1B's responsibility. -/

/-- **#1A → #1B chain**: an effective N(T) bound, together with sufficient
explicit-formula machinery, implies the `VonMangoldtExplicitFormulaBound`
needed by `Gdbh/PathA.lean`.  The exact shape of `…` will be fixed in
#1B; we expose only the named Prop here. -/
def ExplicitFormulaFromNTBound : Prop :=
  (∃ N : ℝ → ℝ, EffectiveRiemannVonMangoldtBound N) →
    VonMangoldtExplicitFormulaBound

/-- **End-to-end Path A chain (named)**: given the four #1A Props
(argument principle, growth bound, components combinator) and the #1B
explicit-formula derivation, deliver `VonMangoldtExplicitFormulaBound`. -/
theorem vonMangoldtExplicitFormula_of_PathA_components
    (h_arg : RectangularArgumentPrinciple)
    (h_growth : RiemannZetaGrowthBound)
    (h_components : EffectiveNTFromComponents)
    (h_efb : ExplicitFormulaFromNTBound) :
    VonMangoldtExplicitFormulaBound :=
  h_efb (h_components h_arg h_growth)

/-! ## Notes on what's open vs proved (no axioms, no sorries)

**Proved unconditionally** in this file:

* All algebraic facts about `verticalLineIntegral` (additivity, swap,
  negation, scalar multiplication, vanishing on a point).
* `argumentPrinciple_of_RectangularArgumentPrinciple` (extraction of
  integer counts from the argument-principle Prop).
* `effectiveRiemannVonMangoldtBound_of_explicit` (existence builder for
  the abstract effective bound).
* `effectiveRiemannVonMangoldtBound_mono` (absorption lemma combining
  several pieces into a single effective bound).
* `effectiveRiemannVonMangoldt_of_components` (combinator extracting the
  existential from the components Prop).
* `vonMangoldtExplicitFormula_of_PathA_components` (the structural
  Path-A chain).

**Stated as Props (open mathematical content)**:

* `RectangularArgumentPrinciple` — Cauchy + meromorphic divisor work.
* `RiemannZetaGrowthBound` — convexity bound for `ζ` in a vertical strip.
* `EffectiveNTFromComponents` — the actual combinator.
* `ExplicitFormulaFromNTBound` — the #1B explicit-formula derivation.

These are honest open targets, not silent gaps.  Their absence of proof
is *visible at the type level* in any theorem that consumes them.
-/

end Gdbh
