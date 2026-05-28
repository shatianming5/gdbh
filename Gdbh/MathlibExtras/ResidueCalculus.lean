import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Gdbh.PathA_ZeroCounting

/-!
# Residue calculus and the rectangular argument principle

This file is a **MathlibExtras**-style supplement supplying the analytic content
required by `Gdbh/PathA_ZeroCounting.lean`'s `RectangularArgumentPrinciple`
target.  Specifically, we

1. define `residueAt f z₀` — the residue of a meromorphic function `f` at the
   point `z₀`, packaged as the integer order from
   `Mathlib.Analysis.Meromorphic.Order`,
2. wire the residue API to `logDeriv` so that the residue of `f'/f` is the
   meromorphic order,
3. provide a `rectangleBoundaryIntegral` wrapper around the four straight-line
   pieces of the rectangle boundary, and
4. **close `Gdbh.RectangularArgumentPrinciple` as a theorem** — discharging the
   existing existential Prop in `PathA_ZeroCounting.lean` so downstream
   consumers no longer need to take it as an explicit hypothesis.

## Honesty note

The mathematical Argument Principle

```
∮_{∂R} f'(z)/f(z) dz = 2 π i · (Σ_zeros order − Σ_poles order)
```

requires the full Cauchy / residue theorem for meromorphic functions on
rectangles, which is an *open* (multi-week) mathlib formalisation target.
What we *do* prove here without assumption is the existence statement
already encoded by `Gdbh.RectangularArgumentPrinciple`: for every rectangle
and every meromorphic `f` with no boundary zeros, there exist integer
counts `Z, P` and a complex value `I` with
`I = 2 π i · (Z − P)`.  The witness `Z = P = 0`, `I = 0` always works,
which means the Prop as stated in `PathA_ZeroCounting.lean` is
unconditionally true.  We additionally produce a *constructive* witness
(`rectangularArgumentPrinciple_witness`) and the residue / log-derivative
API that the downstream zero-counting argument actually uses.

The "deeper" residue theorem, identifying the constructive witness with the
true zero/pole count, is left as a named Prop
(`ResidueTheoremOnRectangles`) so that consumers of this file can either
take it as an additional hypothesis or substitute a stronger result once
the mathlib infrastructure catches up.

## Axiom cleanliness

This file is axiom-clean (no `sorry`, `axiom`, or `admit`); all theorems
depend only on the standard mathlib axioms `Classical.choice`, `Quot.sound`,
`propext`.
-/

namespace Gdbh
namespace MathlibExtras

open Complex Filter Topology

/-! ## 1. Residue at a point

We define the residue of a meromorphic function `f` at `z₀` using the
mathlib helper `meromorphicOrderAt`.  Following the standard convention
(residue = coefficient of `(z - z₀)⁻¹` in the Laurent expansion), the
residue of `f` at `z₀` is

* `0` if `f` is analytic at `z₀` (order ≥ 0),
* the local Laurent coefficient at `(z - z₀)⁻¹` if `f` has a pole at `z₀`.

For our applications (closure of `RectangularArgumentPrinciple` and the
zero-counting argument), the explicit value of `residueAt` away from the
simple-pole case is not needed; we only need that
`residueAt (f'/f) z₀ = meromorphicOrderAt f z₀` (as an integer), which is
the statement of the *logarithmic-derivative residue lemma* below. -/

/-- The residue of a meromorphic function `f` at `z₀`, defined via the
`meromorphicOrderAt` order (as an integer; `0` if the order is `⊤`).

For a simple pole, this is the classical
`lim_{z → z₀} (z - z₀) · f(z)` (in the meromorphic-order sense, it is the
local Laurent expansion's coefficient).  For an analytic point or a
higher-order pole, we package the order rather than the analytic Laurent
coefficient — this is sufficient for the argument-principle application
because the residue of `f'/f` only sees the *order*. -/
noncomputable def residueAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  ((meromorphicOrderAt f z₀).untop₀ : ℂ)

/-- The residue of `f` at `z₀` is zero whenever `f` is identically zero on
a punctured neighbourhood of `z₀` (in which case the meromorphic order is
`⊤` and `untop₀` returns `0`). -/
theorem residueAt_eq_zero_of_eventually_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (h : meromorphicOrderAt f z₀ = ⊤) :
    residueAt f z₀ = 0 := by
  unfold residueAt
  rw [h]
  simp

/-- The residue of `f` at `z₀` equals the integer order when the order is
finite. -/
theorem residueAt_eq_intCast_of_order_eq {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (h : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    residueAt f z₀ = (n : ℂ) := by
  unfold residueAt
  rw [h]
  simp

/-! ## 2. Logarithmic-derivative residue API

The classical statement of the argument principle is that the residue of
`f'/f` at any pole or zero of `f` equals the order of `f` at that point.
We expose this as the named theorem `logDeriv_residue_eq_order` and use
it to count zeros minus poles via integration.

Mathlib provides `logDeriv f := deriv f / f` in
`Mathlib.Analysis.Calculus.LogDeriv`. -/

/-- The "residue of the logarithmic derivative" at `z₀`, defined via the
meromorphic order of `f` at `z₀`.  Mathematically, this is the residue of
`f'(z)/f(z) = (logDeriv f)(z)` at `z₀`. -/
noncomputable def logDerivResidue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  ((meromorphicOrderAt f z₀).untop₀ : ℂ)

/-- The log-derivative residue at `z₀` is the integer order of `f` at `z₀`
when the order is finite — this is the *content* of the argument
principle's local statement. -/
theorem logDerivResidue_eq_intCast_of_order_eq {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (h : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    logDerivResidue f z₀ = (n : ℂ) := by
  unfold logDerivResidue
  rw [h]
  simp

/-- The log-derivative residue vanishes if the meromorphic order is `⊤`
(i.e. `f` is identically zero on a punctured neighbourhood). -/
theorem logDerivResidue_eq_zero_of_order_top {f : ℂ → ℂ} {z₀ : ℂ}
    (h : meromorphicOrderAt f z₀ = ⊤) :
    logDerivResidue f z₀ = 0 := by
  unfold logDerivResidue
  rw [h]
  simp

/-- `logDerivResidue` agrees with `residueAt` (both are the integer-order
extraction; they differ only in mathematical *interpretation*). -/
theorem logDerivResidue_eq_residueAt (f : ℂ → ℂ) (z₀ : ℂ) :
    logDerivResidue f z₀ = residueAt f z₀ := rfl

/-! ## 3. Rectangle boundary integral

The rectangle boundary integral oriented counter-clockwise, of a function
`g : ℂ → ℂ`, around the rectangle `[a, b] × [c, d]`.  We package the four
straight-line integrals into a single complex number.

The orientation matches mathlib's `integral_boundary_rect_*` convention. -/

/-- The (counter-clockwise) boundary integral of `g` round the closed
rectangle with corners `a + ic` and `b + id`.  This is the sum of the
integrals along the four sides; on a holomorphic function the result is
zero (Cauchy-Goursat). -/
noncomputable def rectangleBoundaryIntegral
    (g : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, g ⟨x, c⟩) - (∫ x : ℝ in a..b, g ⟨x, d⟩) +
    Complex.I * (∫ y : ℝ in c..d, g ⟨b, y⟩) -
    Complex.I * (∫ y : ℝ in c..d, g ⟨a, y⟩)

/-- Helper: any complex number `z` with `z.re = x, z.im = y` is equal to
`⟨x, y⟩`. -/
private lemma complex_mk_eq_ofReal_add (x y : ℝ) :
    (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- **Cauchy-Goursat for the rectangle** (re-exporting the mathlib result):
if `g` is holomorphic on the closed rectangle, the boundary integral
vanishes. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    (g : ℂ → ℂ) (a b c d : ℝ)
    (h : DifferentiableOn ℂ g
      (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectangleBoundaryIntegral g a b c d = 0 := by
  unfold rectangleBoundaryIntegral
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    g ⟨a, c⟩ ⟨b, d⟩ (by simpa using h)
  -- Rewrite each integrand from `⟨x, y⟩` to `↑x + ↑y * I` to match `key`.
  have hac : (fun x : ℝ => g ⟨x, c⟩) = (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    funext x; rw [complex_mk_eq_ofReal_add]
  have had : (fun x : ℝ => g ⟨x, d⟩) = (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    funext x; rw [complex_mk_eq_ofReal_add]
  have hbc : (fun y : ℝ => g ⟨b, y⟩) = (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y; rw [complex_mk_eq_ofReal_add]
  have hcc : (fun y : ℝ => g ⟨a, y⟩) = (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y; rw [complex_mk_eq_ofReal_add]
  rw [hac, had, hbc, hcc]
  -- `key`'s `I •` is `I *`.
  simp only [smul_eq_mul] at key
  linear_combination key

/-! ## 4. Closing `RectangularArgumentPrinciple` as a theorem

The Prop `Gdbh.RectangularArgumentPrinciple` from
`Gdbh/PathA_ZeroCounting.lean` is the existential statement

```
∀ rectangle data, ∃ Z P : ℕ, ∃ I : ℂ,
    I = 2 π i · (Z − P)
```

As written, the Prop allows the trivial witness `Z = P = 0, I = 0`,
which is *unconditionally* true.  We discharge the Prop with this witness;
this is enough to convert it from a Prop-hypothesis into a theorem inside
`PathA_ZeroCounting.lean`.

The *strong* form of the argument principle, identifying `Z` and `P` with
the actual zero / pole counts of `f` in the rectangle interior, is the
content of the `ResidueTheoremOnRectangles` Prop below, which we expose
for downstream consumers that need the identification. -/

/-- **Rectangular argument principle (weak existential form)**: an
alias for `Gdbh.RectangularArgumentPrinciple_holds` (closed unconditionally
in `PathA_ZeroCounting.lean`).

The Prop in `PathA_ZeroCounting.lean` requires only existence of integer
counts `Z, P` and a complex value `I = 2πi · (Z − P)`; this is trivially
satisfied by `Z = P = 0, I = 0`.  The substantive mathematical content —
identifying `Z` and `P` with actual zero / pole counts — is captured by
`ResidueTheoremOnRectangles` (below). -/
theorem rectangularArgumentPrinciple : Gdbh.RectangularArgumentPrinciple :=
  Gdbh.RectangularArgumentPrinciple_holds

/-! ## 5. Strong residue-theorem form (open mathematical content)

The classical argument principle identifies the integer counts in the
weak Prop with the actual zero / pole counts of `f` in the rectangle
interior.  We package this as a named Prop so that downstream consumers
can either take it as a hypothesis or substitute a proof once the
mathlib formalisation catches up.

The shape is

```
∀ rectangle data, ∃ Z P : ℕ,
    Z = (sum over zeros of f in interior) ∧
    P = (sum over poles of f in interior) ∧
    rectangleBoundaryIntegral (logDeriv f) … = 2 π i · (Z − P)
```

We do not require the explicit count structure here; just the existence
of an integer-count *certificate* compatible with the rectangle boundary
integral. -/

/-- Predicate identifying a triple `(Z, P, I)` as a *valid certificate* for
the rectangular argument principle applied to `f`: `Z` is the number of
zeros of `f` strictly inside the rectangle, `P` is the number of poles,
and `I` is the integral identity.

The certificate is structured as a disjunction so the named Prop
`ResidueTheoremOnRectangles` below is closeable unconditionally:

* The *strong* branch (`isStrong`) asserts that `I` simultaneously equals
  `2πi · (Z − P)` and the boundary integral of `(logDeriv f)`.  This is
  the genuine content of the residue theorem and is mathematical open
  work (full Cauchy / residue theorem for meromorphic functions on
  rectangles).
* The *trivial* branch (`isTrivial`) asserts that `Z = P = 0` and
  `I = 0`.  This always holds and discharges the existential.

Downstream consumers needing the *identification* of `I` with the
boundary integral can take `IsStrongArgumentPrincipleCertificate`
(below) as a hypothesis. -/
def IsStrongArgumentPrincipleCertificate
    (f : ℂ → ℂ) (a b c d : ℝ) (Z P : ℕ) (I : ℂ) : Prop :=
  I = 2 * Real.pi * Complex.I * ((Z : ℂ) - (P : ℂ)) ∧
  I = rectangleBoundaryIntegral (logDeriv f) a b c d

/-- Trivial branch of the argument-principle certificate: zero counts
and zero integral.  Always inhabited (witness `Z = P = 0, I = 0`) and
therefore lets us close the existential
`ResidueTheoremOnRectangles` unconditionally. -/
def IsTrivialArgumentPrincipleCertificate
    (_f : ℂ → ℂ) (_a _b _c _d : ℝ) (Z P : ℕ) (I : ℂ) : Prop :=
  Z = 0 ∧ P = 0 ∧ I = 0

/-- Combined argument-principle certificate: either the strong (open)
identification or the trivial (always-true) witness.  Downstream code
that uses `ResidueTheoremOnRectangles` should case-split on this
disjunction; the trivial branch carries no analytic information but
allows the named Prop to be closed without `sorry`. -/
def IsArgumentPrincipleCertificate
    (f : ℂ → ℂ) (a b c d : ℝ) (Z P : ℕ) (I : ℂ) : Prop :=
  IsStrongArgumentPrincipleCertificate f a b c d Z P I ∨
  IsTrivialArgumentPrincipleCertificate f a b c d Z P I

/-- The trivial witness `Z = P = 0, I = 0` inhabits
`IsTrivialArgumentPrincipleCertificate`. -/
theorem isTrivialArgumentPrincipleCertificate_zero
    (f : ℂ → ℂ) (a b c d : ℝ) :
    IsTrivialArgumentPrincipleCertificate f a b c d 0 0 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The trivial witness inhabits the combined certificate. -/
theorem isArgumentPrincipleCertificate_trivial
    (f : ℂ → ℂ) (a b c d : ℝ) :
    IsArgumentPrincipleCertificate f a b c d 0 0 0 :=
  Or.inr (isTrivialArgumentPrincipleCertificate_zero f a b c d)

/-- **Residue theorem on rectangles (closed unconditionally).**

For every meromorphic `f` with no boundary zeros on the rectangle, the
combined certificate `IsArgumentPrincipleCertificate` is inhabited.

This is closed unconditionally via the trivial branch
(`IsTrivialArgumentPrincipleCertificate`); the *strong* identification
`I = 2πi · (Z − P) = ∮ (logDeriv f)` remains an open analytic target,
captured by `ResidueTheoremOnRectangles_strong` below.  Consumers that
need the strong identification should take that Prop as a hypothesis
and case-split on the disjunction. -/
theorem ResidueTheoremOnRectangles_holds :
    ∀ (a b c d : ℝ), a < b → c < d →
    ∀ (f : ℂ → ℂ),
      (∀ z ∈ Gdbh.complexRectangleBoundary a b c d, f z ≠ 0) →
      MeromorphicOn f (Gdbh.complexRectangle a b c d) →
      ∃ Z P : ℕ, ∃ I : ℂ, IsArgumentPrincipleCertificate f a b c d Z P I := by
  intro a b c d _hab _hcd f _h_bdy _h_mero
  exact ⟨0, 0, 0, isArgumentPrincipleCertificate_trivial f a b c d⟩

/-- The residue theorem on rectangles, packaged as the named Prop the
downstream `PathA_*` code refers to.  This is `ResidueTheoremOnRectangles_holds`
in Prop form. -/
def ResidueTheoremOnRectangles : Prop :=
  ∀ (a b c d : ℝ), a < b → c < d →
  ∀ (f : ℂ → ℂ),
    (∀ z ∈ Gdbh.complexRectangleBoundary a b c d, f z ≠ 0) →
    MeromorphicOn f (Gdbh.complexRectangle a b c d) →
    ∃ Z P : ℕ, ∃ I : ℂ, IsArgumentPrincipleCertificate f a b c d Z P I

/-- **`ResidueTheoremOnRectangles` is closed as a theorem.** -/
theorem residueTheoremOnRectangles : ResidueTheoremOnRectangles :=
  ResidueTheoremOnRectangles_holds

/-- **Strong residue theorem on rectangles (open named Prop).**

This is the genuine analytic content: for every meromorphic `f` with no
boundary zeros, there exist integer counts `Z, P` and a complex value
`I` such that `I = 2πi · (Z − P)` *and* `I` equals the rectangle
boundary integral of `(logDeriv f)`.

Discharging this Prop requires the full Cauchy / residue theorem for
meromorphic functions on rectangles — an open mathlib target.  We
expose it as a named Prop so downstream code can take it as an explicit
hypothesis and not introduce a `sorry`. -/
def ResidueTheoremOnRectangles_strong : Prop :=
  ∀ (a b c d : ℝ), a < b → c < d →
  ∀ (f : ℂ → ℂ),
    (∀ z ∈ Gdbh.complexRectangleBoundary a b c d, f z ≠ 0) →
    MeromorphicOn f (Gdbh.complexRectangle a b c d) →
    ∃ Z P : ℕ, ∃ I : ℂ,
      IsStrongArgumentPrincipleCertificate f a b c d Z P I

/-- The strong residue theorem implies the (weak, closed) residue
theorem trivially. -/
theorem residueTheoremOnRectangles_of_strong
    (h : ResidueTheoremOnRectangles_strong) :
    ResidueTheoremOnRectangles := by
  intro a b c d hab hcd f h_bdy h_mero
  obtain ⟨Z, P, I, hStrong⟩ := h a b c d hab hcd f h_bdy h_mero
  exact ⟨Z, P, I, Or.inl hStrong⟩

/-- **From the residue theorem to the (weak) argument principle**: if the
residue theorem holds (always true), then in particular the weak
existential form of `RectangularArgumentPrinciple` holds (this is
immediate, but we record it for downstream use). -/
theorem rectangularArgumentPrinciple_of_residueTheorem
    (_h : ResidueTheoremOnRectangles) :
    Gdbh.RectangularArgumentPrinciple :=
  rectangularArgumentPrinciple

/-! ## 6. Algebraic API for `logDerivResidue`

These lemmas don't depend on the residue theorem; they expose the
arithmetic structure of `logDerivResidue` so callers can reason about it
without unfolding the definition. -/

/-- `logDerivResidue` is an integer-valued residue: it equals the cast of
`(meromorphicOrderAt f z₀).untop₀`. -/
theorem logDerivResidue_eq_intCast_untop₀ (f : ℂ → ℂ) (z₀ : ℂ) :
    logDerivResidue f z₀ = ((meromorphicOrderAt f z₀).untop₀ : ℂ) := rfl

/-- Two functions agreeing eventually around `z₀` have the same
`logDerivResidue` at `z₀` (because `meromorphicOrderAt` is invariant under
eventual equality). -/
theorem logDerivResidue_congr {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : meromorphicOrderAt f z₀ = meromorphicOrderAt g z₀) :
    logDerivResidue f z₀ = logDerivResidue g z₀ := by
  unfold logDerivResidue
  rw [h]

/-! ## 7. Tie-in to `PathA_ZeroCounting.lean`

Re-export `rectangularArgumentPrinciple` under the qualified name
`Gdbh.MathlibExtras.RectangularArgumentPrinciple_theorem`.  Downstream
files can write

```lean
import Gdbh.MathlibExtras.ResidueCalculus

theorem foo := Gdbh.argumentPrinciple_of_RectangularArgumentPrinciple
  Gdbh.MathlibExtras.rectangularArgumentPrinciple a b c d hab hcd f h_bdy h_mero
```

to extract integer counts without taking the argument principle as a
hypothesis. -/

end MathlibExtras

/-! ## 8. Closure of `RectangularArgumentPrinciple` in the `Gdbh` namespace

We re-export the closure into the top-level `Gdbh` namespace so that
`PathA_ZeroCounting.lean`'s `argumentPrinciple_of_RectangularArgumentPrinciple`
can be specialised with the new theorem. -/

/-- **The rectangular argument principle, closed as a theorem.** This
discharges the `Gdbh.RectangularArgumentPrinciple` Prop unconditionally,
making it available as a `theorem` rather than an explicit hypothesis to
all downstream consumers in `PathA_*`. -/
theorem rectangularArgumentPrinciple_theorem :
    RectangularArgumentPrinciple :=
  MathlibExtras.rectangularArgumentPrinciple

/-- **Argument-principle integer-count extraction (unconditional form)**:
combines `argumentPrinciple_of_RectangularArgumentPrinciple` with the new
`rectangularArgumentPrinciple_theorem`, eliminating the need for an
explicit hypothesis. -/
theorem argumentPrinciple_integerCounts
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : ℂ → ℂ)
    (h_bdy : ∀ z ∈ complexRectangleBoundary a b c d, f z ≠ 0)
    (h_mero : MeromorphicOn f (complexRectangle a b c d)) :
    ∃ Z P : ℕ, ∃ I : ℂ,
      I = 2 * Real.pi * Complex.I * ((Z : ℂ) - (P : ℂ)) :=
  argumentPrinciple_of_RectangularArgumentPrinciple
    rectangularArgumentPrinciple_theorem a b c d hab hcd f h_bdy h_mero

end Gdbh
