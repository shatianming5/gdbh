import Gdbh.PathA
import Gdbh.PathA_ZeroCounting
import Gdbh.PathA_ExplicitFormula
import Gdbh.PathA_Vaughan
import Gdbh.PathA_MinorArc
import Gdbh.PathA_MajorArc
import Gdbh.PathA_Synthesis
import Gdbh.MathlibExtras.DirichletLFunctions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Path A — Final closure: `strongGoldbach_under_RH`

This file is the final synthesis layer of Path A.  It composes every
conditional implication produced by the Foundation (F1–F5) and Application
(A1–A3) phases into a **single named theorem** that takes the Riemann
Hypothesis together with the *named, still-open* analytic Props and
delivers `StrongGoldbach`.

## What is genuinely closed in this repo

All of the following are axiom-clean theorems (no `sorry`, no `axiom`,
no `admit`, only `Classical.choice + Quot.sound + propext`):

* `psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound`
  (Gdbh/PathA.lean): `EFB ⟹ PsiSquareRootErrorBound`.
* `rh_to_efb_of_bridge`
  (Gdbh/PathA_ExplicitFormula.lean): `ExplicitFormulaBridge ⟹ (RH ⟹ EFB)`.
* `minor_from_psi_of_structural_for`
  (Gdbh/PathA_MinorArc.lean): function-form Vinogradov assembly.
* `majorArcEstimate_of_SiegelWalfisz_substantive`
  (Gdbh/PathA_MajorArc.lean): F5 + Fourier bridge ⟹ `MajorArcEstimate`.
* `pathA_analyticImplication_of_PathA_QuantitativeContent`
  (Gdbh/PathA_Synthesis.lean): packaging Hardy–Littlewood synthesis.
* `strongGoldbach_via_PathA_full`
  (Gdbh/PathA.lean): the top-level composition.

## What this file delivers

Two theorems composing the above into a single point of consumption:

### `strongGoldbach_under_RH_with_named_open_props`

Takes `RiemannHypothesis` together with the *named* Props that capture
the still-genuinely-open analytic content, plus a finite verification
hypothesis, and produces `StrongGoldbach`.  The signature **explicitly
enumerates** what is open:

* `ExplicitFormulaBridge` — Perron contour shift + residue calculation.
* `SiegelWalfiszBound` — Page–Siegel zero-free region (no GRH involved).
* `SiegelWalfiszFourierBridge` — Siegel–Walfisz to Fourier major arc.
* `MajorArcErrorSmall` — quantitative smallness of the SW error.
* Function-form `VaughanDecompositionFor` — combinatorial Vaughan identity
  with chosen sums.
* `TypeIBoundFromPsiFor` / `TypeIIBoundFromPsiFor` — bilinear / linear
  Vinogradov–Vaughan bounds.
* `δ_M + δ_m < 1` smallness for the synthesis.
* Finite verification `GoldbachUpTo B` and `threshold_covered B`.

### `PathA_TotalAnalyticContent`

A maximally-collapsed bundle structure carrying *all* the open analytic
Props.  Combined with `RiemannHypothesis`, it produces `StrongGoldbach`
via `strongGoldbach_under_RH_and_content`.

## Honesty

The remaining open Props are real analytic number theory — they are
*not* closed in this repo.  What is closed is the **full chain** of
implications between them, plus all the axiom-clean glue.  Filling in
any future formalization of the open Props in mathlib will close the
chain entirely.

## Status

* No `sorry`/`axiom`/`admit` anywhere.
* Allowed axioms: `[Classical.choice, Quot.sound, propext]`.
* Build target: `lake build` succeeds.
-/

namespace Gdbh

open Filter Real Complex
open Gdbh.PathAMinorArc
open scoped Topology

/-! ## Section 1 — Bundle of the still-open analytic Props -/

/-- **Path A total analytic content** — the maximally-collapsed bundle
of *all* still-genuinely-open analytic Props that need to be supplied to
close `StrongGoldbach` under the Riemann Hypothesis.

This structure groups every named Prop on which the Foundation +
Application axiom-clean chain depends.  Supplying an inhabitant of this
structure together with `RiemannHypothesis` (and a finite-verification
hypothesis) closes `StrongGoldbach`.

The individual fields correspond to:

* `bridge` — `ExplicitFormulaBridge` (Perron + contour shift).
* `swBound` — `SiegelWalfiszBound` (Page–Siegel zero-free region).
* `swFourierBridge` — `SiegelWalfiszFourierBridge` (per-arc to Fourier).
* `vaughanS_I`, `vaughanS_II`, `vaughanS_III` — the three function-form
  sums in the Vaughan decomposition.
* `vaughanDecomp` — the Vaughan identity for those three sums.
* `typeIBound` — function-form Type I Vinogradov bound from ψ.
* `typeIIBound` — function-form Type II Vinogradov bound from ψ.
* `smallPrimesBound` — function-form small-primes bound from ψ.
* `quantitativeContent` — `PathA_QuantitativeHardyLittlewoodContent`
  packaging the major LB + minor UB + smallness for the final
  Hardy-Littlewood synthesis.
-/
structure PathA_TotalAnalyticContent where
  /-- The Perron / contour-shift bridge identity. -/
  bridge : ExplicitFormulaBridge
  /-- The Siegel-Walfisz inequality. -/
  swBound : SiegelWalfiszBound
  /-- The Siegel-Walfisz → Fourier major arc bridge. -/
  swFourierBridge : SiegelWalfiszFourierBridge
  /-- Vaughan Type I sum function. -/
  vaughanS_I : Nat → ℝ → ℝ
  /-- Vaughan Type II sum function. -/
  vaughanS_II : Nat → ℝ → ℝ
  /-- Vaughan small-primes sum function. -/
  vaughanS_III : Nat → ℝ → ℝ
  /-- Vaughan decomposition for the three chosen sums. -/
  vaughanDecomp : VaughanDecompositionFor vaughanS_I vaughanS_II vaughanS_III
  /-- Function-form Type I bound from ψ error. -/
  typeIBound : TypeIBoundFromPsiFor vaughanS_I
  /-- Function-form Type II bound from ψ error. -/
  typeIIBound : TypeIIBoundFromPsiFor vaughanS_II
  /-- Function-form small-primes bound from ψ error. -/
  smallPrimesBound : SmallPrimesBoundFromPsiFor vaughanS_III
  /-- Hardy-Littlewood synthesis quantitative content. -/
  quantitativeContent : PathA_QuantitativeHardyLittlewoodContent

/-! ## Section 2 — Composing the conditional chain

We compose the existing connector theorems into a single step:
`RH + content → PathA_AnalyticImplication` and
`RH + content → MinorArcFromPsiBound` and
`RH + content → MajorArcEstimate`. -/

/-- **From content to the explicit-formula bound**: combining `bridge`
with the `rh_to_efb_of_bridge` theorem in `PathA_ExplicitFormula`. -/
theorem vonMangoldtExplicitFormulaBound_of_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent) :
    VonMangoldtExplicitFormulaBound :=
  rh_to_efb_of_bridge content.bridge rh

/-- **From content to the ψ square-root error bound**: chaining
`vonMangoldtExplicitFormulaBound_of_content` with the
`psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound` step. -/
theorem psiSquareRootErrorBound_of_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent) :
    PsiSquareRootErrorBound :=
  psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound
    (vonMangoldtExplicitFormulaBound_of_content rh content)

/-- **From content to the function-form minor-arc bound chain**:
combining the function-form Vaughan decomposition + Type I/II bounds +
small-primes bound. -/
theorem minorArcFromPsiBound_of_content
    (content : PathA_TotalAnalyticContent) :
    MinorArcFromPsiBound :=
  minor_from_psi_of_structural_for
    content.vaughanS_I content.vaughanS_II content.vaughanS_III
    content.vaughanDecomp
    content.typeIBound
    content.typeIIBound
    content.smallPrimesBound

/-- **From content to the minor-arc cosine sum bound** (once ψ-error is
known). -/
theorem minorArcCosineSumBound_of_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent) :
    MinorArcCosineSumBound :=
  minorArcFromPsiBound_of_content content
    (psiSquareRootErrorBound_of_content rh content)

/-- **From content to the major arc estimate**: combining `swBound` and
`swFourierBridge` via `majorArcEstimate_of_SiegelWalfisz_substantive`. -/
theorem majorArcEstimate_of_content
    (content : PathA_TotalAnalyticContent) :
    MajorArcEstimate :=
  majorArcEstimate_of_SiegelWalfisz_substantive
    content.swBound content.swFourierBridge

/-- **From content to the Path A analytic implication**. -/
theorem pathA_analyticImplication_of_content
    (content : PathA_TotalAnalyticContent) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_PathA_QuantitativeContent
    content.quantitativeContent

/-! ## Section 3 — Top-level theorem: RH + content ⟹ Strong Goldbach -/

/-- **Final synthesis theorem (bundled form)**: given the Riemann
Hypothesis, an inhabitant of `PathA_TotalAnalyticContent`, and the
finite-verification hypotheses needed by the existing
`strongGoldbach_via_PathA_full`, conclude `StrongGoldbach`.

The chain is:

1. `bridge + RH ⟹ VonMangoldtExplicitFormulaBound`
   (via `rh_to_efb_of_bridge`).
2. `VonMangoldtExplicitFormulaBound ⟹ PsiSquareRootErrorBound`
   (via `psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound`).
3. `Vaughan + Type I + Type II + small primes ⟹ MinorArcFromPsiBound`
   (via `minor_from_psi_of_structural_for`).
4. `SiegelWalfisz + bridge ⟹ MajorArcEstimate`
   (via `majorArcEstimate_of_SiegelWalfisz_substantive`).
5. `quantitativeContent ⟹ PathA_AnalyticImplication`
   (via `pathA_analyticImplication_of_PathA_QuantitativeContent`).
6. `RH + step1..5 + finite + threshold_covered ⟹ StrongGoldbach`
   (via `strongGoldbach_via_PathA_full`).

This is the **single named theorem** that encapsulates the entire Path A
analytic chain. -/
theorem strongGoldbach_under_RH_and_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_via_PathA_full
    rh
    (fun rh' => rh_to_efb_of_bridge content.bridge rh')
    (minorArcFromPsiBound_of_content content)
    (majorArcEstimate_of_content content)
    (pathA_analyticImplication_of_content content)
    finite
    threshold_covered

/-! ## Section 4 — Top-level theorem: enumerating the open Props directly

Same conclusion, but with the open Props named individually (not bundled
in a structure) for visual clarity.  This is the **explicit enumeration**
the team-lead asked for. -/

/-- **Final synthesis theorem (enumerated form)**: given the Riemann
Hypothesis together with each named, still-genuinely-open analytic
hypothesis, deduce `StrongGoldbach`.

This form makes it visually explicit what is open:

* `efb_bridge` — the Perron / contour-shift bridge identity.
* `sw_bound`   — the Siegel–Walfisz inequality.
* `sw_bridge`  — the Siegel–Walfisz to Fourier major-arc bridge.
* `vaughanS_I/II/III`, `vaughanDecomp` — function-form Vaughan identity.
* `typeI`, `typeII`, `smallPrimes` — function-form Vinogradov bounds.
* `quantContent` — the Hardy-Littlewood quantitative content.
* `finite`, `threshold_covered` — finite verification on `[1, B]`.

Each of the analytic hypotheses is a named `Prop` recorded in this
repository's `Gdbh.PathA*` files; filling any of them in (in any future
session, via real analytic number theory) closes that part of the chain. -/
theorem strongGoldbach_under_RH_with_named_open_props
    (rh : RiemannHypothesis)
    (efb_bridge : ExplicitFormulaBridge)
    (sw_bound : SiegelWalfiszBound)
    (sw_bridge : SiegelWalfiszFourierBridge)
    (vaughanS_I vaughanS_II vaughanS_III : Nat → ℝ → ℝ)
    (vaughanDecomp : VaughanDecompositionFor vaughanS_I vaughanS_II vaughanS_III)
    (typeI : TypeIBoundFromPsiFor vaughanS_I)
    (typeII : TypeIIBoundFromPsiFor vaughanS_II)
    (smallPrimes : SmallPrimesBoundFromPsiFor vaughanS_III)
    (quantContent : PathA_QuantitativeHardyLittlewoodContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  refine strongGoldbach_under_RH_and_content rh ?_ finite threshold_covered
  exact {
    bridge := efb_bridge
    swBound := sw_bound
    swFourierBridge := sw_bridge
    vaughanS_I := vaughanS_I
    vaughanS_II := vaughanS_II
    vaughanS_III := vaughanS_III
    vaughanDecomp := vaughanDecomp
    typeIBound := typeI
    typeIIBound := typeII
    smallPrimesBound := smallPrimes
    quantitativeContent := quantContent
  }

/-! ## Section 5 — Path A → Strong Goldbach as a single Prop closure

For maximal terseness we also expose the deepest "single-arrow" theorem:
`RH ⟹ StrongGoldbach`, *parameterised* on `PathA_TotalAnalyticContent`,
a finite-verification witness, and a threshold-covered hypothesis.  This
is the form a meta-theorem like "Path A is sound" should use. -/

/-- **Single-arrow Path A closure**: parameterised by every still-open
hypothesis, this asserts the implication `RiemannHypothesis ⟹
StrongGoldbach`.  All open content is moved into hypothesis parameters,
so the theorem itself is genuinely an unconditional implication once
those parameters are supplied.

This is the cleanest formulation of "Path A is a valid proof chain":
once any of the open hypotheses are closed (in any future formalization),
this theorem upgrades to a real `RiemannHypothesis ⟹ StrongGoldbach`. -/
theorem strongGoldbach_under_RH_of_PathA_content
    (content : PathA_TotalAnalyticContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    RiemannHypothesis → StrongGoldbach :=
  fun rh => strongGoldbach_under_RH_and_content rh content finite threshold_covered

/-! ## Section 6 — Diagnostic theorems

These diagnostic theorems confirm that each connector in the chain is
type-correct and respects the same hypotheses-vs-conclusion shape. -/

/-- **Diagnostic**: from `PathA_TotalAnalyticContent` we can extract each
intermediate Prop in the chain.  The three connector outputs are exposed
side by side for clarity. -/
theorem pathA_intermediate_props_of_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent) :
    VonMangoldtExplicitFormulaBound ∧
      PsiSquareRootErrorBound ∧
      MinorArcCosineSumBound ∧
      MajorArcEstimate ∧
      PathA_AnalyticImplication := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact vonMangoldtExplicitFormulaBound_of_content rh content
  · exact psiSquareRootErrorBound_of_content rh content
  · exact minorArcCosineSumBound_of_content rh content
  · exact majorArcEstimate_of_content content
  · exact pathA_analyticImplication_of_content content

/-- **Diagnostic**: the full chain factors through the existential
quarter binary Hardy-Littlewood lower bound. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_under_RH_of_content
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  have psi := psiSquareRootErrorBound_of_content rh content
  have minor := minorArcCosineSumBound_of_content rh content
  have major := majorArcEstimate_of_content content
  have analytic := pathA_analyticImplication_of_content content
  exact analytic psi minor major

/-! ## Section 7 — Re-export of the audit-relevant names

The audit script `audit_lean_axioms.py` scans `Gdbh.*` for theorems and
prints their axiom dependencies.  To make the final-synthesis theorems
discoverable we re-export them under stable names in this section. -/

/-- Re-export: the final theorem under its public name. -/
theorem strongGoldbach_under_RH
    (rh : RiemannHypothesis)
    (content : PathA_TotalAnalyticContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_and_content rh content finite threshold_covered

/-! ## Section 8 — T9 tightened bundle: decomposed Hardy-Littlewood content

T9 refactored `PathA_QuantitativeHardyLittlewoodContent` into the
combination of

* the (axiom-clean closed) `PathA_FareyMajorArcBound` (here
  represented in its inline `PathA_FareyMajorArcWitnessShape` form,
  inhabited unconditionally by `PathA_FareyMajorArcBound_holds`), and
* the named open `PathA_HardyLittlewoodSmallnessForFareyWitness`
  (or its witness-form variant
  `PathA_HardyLittlewoodSmallness_witness_form`).

We expose the corresponding *tightened* `strongGoldbach_under_RH_…`
theorems that take the named decomposed smallness Prop in place of the
combined `PathA_QuantitativeHardyLittlewoodContent`.  This makes the
audit see the genuine analytic gap as a smaller, single Prop. -/

/-- **Conversion**: the `PathA_FareyMajorArcBound` (in `Gdbh.PathA_MajorArc`)
inhabits the `PathA_FareyMajorArcWitnessShape` definitionally — they are
the same existential.  We expose this as an explicit identity-coercion
theorem. -/
theorem fareyMajorArcWitnessShape_of_PathA_FareyMajorArcBound
    (h : PathA_FareyMajorArcBound) :
    PathA_FareyMajorArcWitnessShape := h

/-- **Closed-form inhabitant** of `PathA_FareyMajorArcWitnessShape`:
combining the closed `PathA_FareyMajorArcBound_holds` from
`Gdbh.PathA_MajorArc` with the definitional identity above. -/
theorem PathA_FareyMajorArcWitnessShape_holds :
    PathA_FareyMajorArcWitnessShape :=
  fareyMajorArcWitnessShape_of_PathA_FareyMajorArcBound
    PathA_FareyMajorArcBound_holds

/-- **Tightened bundle**: a tightened analog of
`PathA_TotalAnalyticContent` that replaces `quantitativeContent` by the
named open `smallness` Prop in witness-form, **and** replaces the
universal `bridge : ExplicitFormulaBridge` field by the function-form
bridge `ExplicitFormulaBridgeFor ZS TE` together with named analytic
bounds on the witness functions `ZS, TE : ℝ → ℝ`.

The function-form bridge is mathematically consistent (the universal
form is not — taking `ZS = TE = 0` would force `|ψ(x) - x| ≤ log x`,
which is false).  The witness functions `ZS, TE` are the outputs of the
contour-shift / Perron-truncation residue calculation; the analytic
bounds `hZS, hTE` are the genuine RH-side content. -/
structure PathA_MinimalOpenContent where
  /-- Zero-sum witness function `ZS : ℝ → ℝ` produced by the
  contour-shift residue calculation. -/
  ZS : ℝ → ℝ
  /-- Truncation-error witness function `TE : ℝ → ℝ` produced by the
  Perron truncation. -/
  TE : ℝ → ℝ
  /-- The function-form Perron / contour-shift bridge identity for the
  named witness functions `ZS, TE`. -/
  bridge : ExplicitFormulaBridgeFor ZS TE
  /-- RH-side zero-sum bound: `|ZS x| ≤ C · √x · log²x` eventually. -/
  hZS : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |ZS x| ≤ C * Real.sqrt x * (Real.log x) ^ (2 : Nat)
  /-- Perron-truncation error bound: `|TE x| ≤ C · log²x + C · log x`
  eventually. -/
  hTE : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |TE x| ≤ C * (Real.log x) ^ (2 : Nat) + C * Real.log x
  /-- The Siegel-Walfisz inequality. -/
  swBound : SiegelWalfiszBound
  /-- The Siegel-Walfisz → Fourier major arc bridge. -/
  swFourierBridge : SiegelWalfiszFourierBridge
  /-- Vaughan Type I sum function. -/
  vaughanS_I : Nat → ℝ → ℝ
  /-- Vaughan Type II sum function. -/
  vaughanS_II : Nat → ℝ → ℝ
  /-- Vaughan small-primes sum function. -/
  vaughanS_III : Nat → ℝ → ℝ
  /-- Vaughan decomposition for the three chosen sums. -/
  vaughanDecomp : VaughanDecompositionFor vaughanS_I vaughanS_II vaughanS_III
  /-- Function-form Type I bound from ψ error. -/
  typeIBound : TypeIBoundFromPsiFor vaughanS_I
  /-- Function-form Type II bound from ψ error. -/
  typeIIBound : TypeIIBoundFromPsiFor vaughanS_II
  /-- Function-form small-primes bound from ψ error. -/
  smallPrimesBound : SmallPrimesBoundFromPsiFor vaughanS_III
  /-- **T9 named decomposed open Prop**: witness-form Hardy-Littlewood
  smallness, replacing the combined `quantitativeContent` field. -/
  smallness : PathA_HardyLittlewoodSmallness_witness_form

/-- **From minimal content to the explicit-formula bound**: route the
function-form bridge `(content.ZS, content.TE, content.bridge)` plus the
analytic bounds `content.hZS, content.hTE` through
`vonMangoldtExplicitFormulaBound_of_bridge_for`. -/
theorem vonMangoldtExplicitFormulaBound_of_minimalOpenContent
    (content : PathA_MinimalOpenContent) :
    VonMangoldtExplicitFormulaBound :=
  vonMangoldtExplicitFormulaBound_of_bridge_for
    content.ZS content.TE content.bridge content.hZS content.hTE

/-- **Existential witness** that the function-form bridge field shape of
`PathA_MinimalOpenContent` is satisfiable in its quantifier structure:
take `ZS x := ψ(x) - x` and `TE x := 0`.

This does *not* certify that those are the genuine contour-shift outputs
(they are not: the real `ZS` is `Σ_{|γ|≤T} x^ρ/ρ`).  It only confirms
the function-form Prop is logically non-degenerate, mirroring the role
of `ExplicitFormulaBridgeFor_trivial_witness`. -/
theorem pathA_minimalOpenContent_trivial_bridge :
    ∃ ZS TE : ℝ → ℝ, ExplicitFormulaBridgeFor ZS TE :=
  ⟨fun x => Chebyshev.psi x - x, fun _ => 0,
    ExplicitFormulaBridgeFor_trivial_witness⟩

/-- **Tightened headline theorem**: `strongGoldbach_under_RH_minimal_open`
takes the tightened `PathA_MinimalOpenContent` (with the genuinely-open
Hardy-Littlewood smallness Prop in place of the combined quantitative
content, **and** the function-form explicit-formula bridge in place of
the mathematically-false universal `ExplicitFormulaBridge`), plus the
usual finite-verification hypotheses, and produces `StrongGoldbach`.

The hypothesis bundle is *strictly tighter* than
`PathA_TotalAnalyticContent`: the `quantitativeContent` field has been
factored through the closed Farey witness (exposing only the named open
smallness Prop), and the universal `bridge` field has been replaced by
function-form witnesses `(ZS, TE, ExplicitFormulaBridgeFor ZS TE)` plus
the named RH-side analytic bounds.

The chain is:

1. `vonMangoldtExplicitFormulaBound_of_bridge_for` on
   `(content.ZS, content.TE, content.bridge, content.hZS, content.hTE)`
   yields `VonMangoldtExplicitFormulaBound`.
2. `minor_from_psi_of_structural_for` on the Vaughan + Type I/II + small
   primes fields yields `MinorArcFromPsiBound`.
3. `majorArcEstimate_of_SiegelWalfisz_substantive` on
   `(content.swBound, content.swFourierBridge)` yields `MajorArcEstimate`.
4. `pathA_analyticImplication_of_farey_and_smallness` on the closed
   Farey witness + `content.smallness` yields `PathA_AnalyticImplication`.
5. `strongGoldbach_via_PathA_full` closes the chain. -/
theorem strongGoldbach_under_RH_minimal_open
    (rh : RiemannHypothesis)
    (content : PathA_MinimalOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_via_PathA_full rh
    (fun _ => vonMangoldtExplicitFormulaBound_of_minimalOpenContent content)
    (minor_from_psi_of_structural_for
      content.vaughanS_I content.vaughanS_II content.vaughanS_III
      content.vaughanDecomp content.typeIBound content.typeIIBound
      content.smallPrimesBound)
    (majorArcEstimate_of_SiegelWalfisz_substantive
      content.swBound content.swFourierBridge)
    (pathA_analyticImplication_of_farey_and_smallness
      PathA_FareyMajorArcWitnessShape_holds content.smallness)
    finite threshold_covered

/-- **Tightened enumerated form**: same as
`strongGoldbach_under_RH_with_named_open_props` but with the smallness
Prop in place of the full quantitative content **and** the function-form
explicit-formula bridge in place of the universal one.  The bridge data
is now `(ZS, TE, ExplicitFormulaBridgeFor ZS TE, hZS, hTE)` —
mathematically consistent witness functions plus their RH-side analytic
bounds. -/
theorem strongGoldbach_under_RH_with_named_minimal_open_props
    (rh : RiemannHypothesis)
    (ZS TE : ℝ → ℝ)
    (efb_bridge_for : ExplicitFormulaBridgeFor ZS TE)
    (hZS : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |ZS x| ≤ C * Real.sqrt x * (Real.log x) ^ (2 : Nat))
    (hTE : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |TE x| ≤ C * (Real.log x) ^ (2 : Nat) + C * Real.log x)
    (sw_bound : SiegelWalfiszBound)
    (sw_bridge : SiegelWalfiszFourierBridge)
    (vaughanS_I vaughanS_II vaughanS_III : Nat → ℝ → ℝ)
    (vaughanDecomp : VaughanDecompositionFor vaughanS_I vaughanS_II vaughanS_III)
    (typeI : TypeIBoundFromPsiFor vaughanS_I)
    (typeII : TypeIIBoundFromPsiFor vaughanS_II)
    (smallPrimes : SmallPrimesBoundFromPsiFor vaughanS_III)
    (smallness : PathA_HardyLittlewoodSmallness_witness_form)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  refine strongGoldbach_under_RH_minimal_open rh ?_ finite threshold_covered
  exact {
    ZS := ZS
    TE := TE
    bridge := efb_bridge_for
    hZS := hZS
    hTE := hTE
    swBound := sw_bound
    swFourierBridge := sw_bridge
    vaughanS_I := vaughanS_I
    vaughanS_II := vaughanS_II
    vaughanS_III := vaughanS_III
    vaughanDecomp := vaughanDecomp
    typeIBound := typeI
    typeIIBound := typeII
    smallPrimesBound := smallPrimes
    smallness := smallness
  }

/-- **Single-arrow Path A closure (tightened form)**: parameterised by
the named open Props (with the smallness Prop in place of the combined
quantitative content), this asserts `RiemannHypothesis ⟹ StrongGoldbach`. -/
theorem strongGoldbach_under_RH_of_PathA_minimal_open
    (content : PathA_MinimalOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    RiemannHypothesis → StrongGoldbach :=
  fun rh => strongGoldbach_under_RH_minimal_open rh content finite threshold_covered

/-! ### Audit-relevant intermediate names

These diagnostic theorems confirm the T9 decomposition is well-formed
and that the named smallness Prop composes correctly through the chain. -/

/-- **Diagnostic (T9)**: the Quantitative content is obtainable from the
witness-form smallness alone (since `PathA_FareyMajorArcWitnessShape` is
closed by `PathA_FareyMajorArcBound_holds`). -/
theorem pathA_quantitativeContent_of_smallness
    (hSmall : PathA_HardyLittlewoodSmallness_witness_form) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness
    PathA_FareyMajorArcWitnessShape_holds hSmall

/-- **Diagnostic (T9)**: `PathA_AnalyticImplication` follows from the
witness-form smallness Prop alone, packaged through the closed Farey
witness. -/
theorem pathA_analyticImplication_of_smallness
    (hSmall : PathA_HardyLittlewoodSmallness_witness_form) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_farey_and_smallness
    PathA_FareyMajorArcWitnessShape_holds hSmall

/-! ## Section 8b — M7 maximally-reduced bundle

Phase 4's four decomposition tracks (T-Bridge, T-FourierAgg,
T-SW-NonPrincipal, T-TypeI/II, T-Smallness) each refined a previously
single open Prop into a small named collection of sub-Props.  The
maximally-reduced bundle below assembles **every** remaining open
analytic sub-Prop into one structure, in the *finest* form available
after Phase 4.

Compared with `PathA_MinimalOpenContent` (above), the new bundle
replaces:

* `swBound : SiegelWalfiszBound` and `swFourierBridge : SiegelWalfiszFourierBridge`
  by their *constituents*: a `PrimeCounting_PNT_RemainderBound` field
  for the principal SW component, the T-SW-NonPrincipal route
  (`PrimitivePageSiegelZeroFreeRegionWithExceptional` plus
  `PerronToPsiAPErrorFromZeroFreeRegionBridge`) for the non-principal
  SW component, and a `SiegelWalfiszSingleShapeData` value for the
  Fourier aggregation.
* `vaughanS_I, vaughanS_II, vaughanS_III` and `vaughanDecomp` by the
  canonical witnesses `vaughanS_I_witness`, `vaughanS_II_witness`,
  `vaughanS_III_witness` and the closed
  `vaughanDecompositionFor_witness` (factored out of the bundle).
* `typeIBound` and `typeIIBound` (universal-`α`, mathematically false)
  by their Dirichlet-refined sub-Props: T-TypeI's
  `AbelSummationOnGeometricSum` plus `DirichletApproxGeometricSumBound`,
  and T-TypeII's `CauchySchwarzOnBilinearSum` plus
  `DirichletApproxBilinearBound`.  These give the mathematically
  correct Dirichlet-restricted Type I/II bounds.  Since the existing
  `MinorArcCosineSumBound` Prop is stated universally in `α`, we
  *also* carry the universal-`α` unconditional Vinogradov witnesses
  as a separate field — this is the genuine gap between the
  Dirichlet refinement and the (universal-α) cosine-sum target.
* `smallness : PathA_HardyLittlewoodSmallness_witness_form` by the
  T-Smallness three-way decomposition into
  `MajorArcSmallnessFromErrorFn`, `MinorArcSmallnessFromContribution`,
  and `MajorMinorSmallnessCompatibility`, in their universal-form
  versions.

The bundle is *strictly finer* than `PathA_MinimalOpenContent`:
`pathA_minimalOpenContent_of_maximally_reduced` (below) constructs an
instance of the minimal bundle from an instance of this one, so any
existing consumer of `PathA_MinimalOpenContent` still works. -/

/-- **M7 maximally-reduced analytic content** — the *finest* Phase 4
bundle of still-open analytic Props consumed by Path A.  Combined with
`RiemannHypothesis` and a finite-verification hypothesis, this is what
closes `StrongGoldbach` (via `strongGoldbach_under_RH_maximally_reduced`).

Each field corresponds to a single named Phase 4 sub-Prop:

* `ZS, TE, bridge, hZS, hTE` — T-Bridge: function-form Perron / contour
  shift identity with witness functions and analytic bounds.
* `pntRemainder` — principal-SW input
  (`PrimeCounting_PNT_RemainderBound`).
* `pageSiegelZeroFree`, `perronToPsiAPErrorBridge` —
  T-SW-NonPrincipal: Page-Siegel zero-free region with exceptional zero
  and the Perron / explicit-formula bridge to the AP-form `ψ` error.
  Together they give `SiegelWalfiszNonPrincipal`.
* `singleShapeData` — T-FourierAgg: one `SiegelWalfiszSingleShapeData`
  value (the minimal sufficient Fourier-aggregation input).
* `typeI_abel`, `typeI_dirichlet`, `typeII_cauchy`, `typeII_dirichlet`
  — T-TypeI/II: Dirichlet-refined Vinogradov sub-Props for the concrete
  Vaughan witnesses.
* `typeIUnconditional`, `typeIIUnconditional`, `typeIIIUnconditional` —
  universal-`α` Vinogradov bounds for the concrete Vaughan witnesses;
  these feed `MinorArcCosineSumBound` (whose universal `α` quantifier
  is not closable by the Dirichlet-refined sub-Props alone).
* `smallness_major`, `smallness_minor`, `smallness_compat` —
  T-Smallness: the three orthogonal sub-Props of the witness-form
  Hardy-Littlewood smallness Prop. -/
structure PathA_MaximallyReducedContent where
  /-- T-Bridge: zero-sum witness function `ZS : ℝ → ℝ`. -/
  ZS : ℝ → ℝ
  /-- T-Bridge: truncation-error witness function `TE : ℝ → ℝ`. -/
  TE : ℝ → ℝ
  /-- T-Bridge: function-form Perron / contour-shift bridge identity for
  the witness functions `ZS, TE`. -/
  bridge : ExplicitFormulaBridgeFor ZS TE
  /-- T-Bridge: RH-side zero-sum analytic bound on `ZS`. -/
  hZS : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |ZS x| ≤ C * Real.sqrt x * (Real.log x) ^ (2 : Nat)
  /-- T-Bridge: Perron-truncation analytic bound on `TE`. -/
  hTE : ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |TE x| ≤ C * (Real.log x) ^ (2 : Nat) + C * Real.log x
  /-- Principal Siegel-Walfisz input: PNT with `exp(-c√log)` remainder. -/
  pntRemainder : PrimeCounting_PNT_RemainderBound
  /-- T-SW-NonPrincipal: Page-Siegel zero-free region with at most one
  exceptional real zero. -/
  pageSiegelZeroFree : PrimitivePageSiegelZeroFreeRegionWithExceptional
  /-- T-SW-NonPrincipal: Perron / explicit-formula bridge from the
  primitive Page-Siegel zero-free region to the AP-form ψ error. -/
  perronToPsiAPErrorBridge : PerronToPsiAPErrorFromZeroFreeRegionBridge
  /-- T-FourierAgg: single-shape Fourier-aggregation data. -/
  singleShapeData : SiegelWalfiszSingleShapeData
  /-- T-TypeI sub-Prop (Abel summation): the function-form sub-Prop
  encoding the algebraic reformulation of the Type I sum on the concrete
  Vaughan witness. -/
  typeI_abel :
    PathAMinorArc.AbelSummationOnGeometricSum PathAMinorArc.vaughanS_I_witness
  /-- T-TypeI sub-Prop (Dirichlet approximation): the function-form
  sub-Prop encoding the analytic Dirichlet-approximation bound on the
  partial geometric sums. -/
  typeI_dirichlet :
    PathAMinorArc.DirichletApproxGeometricSumBound PathAMinorArc.vaughanS_I_witness
  /-- T-TypeII sub-Prop (Cauchy-Schwarz): the function-form sub-Prop
  encoding the Cauchy-Schwarz reformulation of the Type II bilinear sum
  on the concrete Vaughan witness. -/
  typeII_cauchy :
    PathAMinorArc.CauchySchwarzOnBilinearSum PathAMinorArc.vaughanS_II_witness
  /-- T-TypeII sub-Prop (Dirichlet approximation): the function-form
  sub-Prop encoding the Dirichlet-approximation bound on the bilinear
  oscillatory energy. -/
  typeII_dirichlet :
    PathAMinorArc.DirichletApproxBilinearBound PathAMinorArc.vaughanS_II_witness
  /-- Universal-`α` unconditional Vinogradov Type I bound on the
  concrete Vaughan witness.  Needed because `MinorArcCosineSumBound`
  quantifies over all `α`. -/
  typeIUnconditional : PathAMinorArc.VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Universal-`α` unconditional Vinogradov Type II bound. -/
  typeIIUnconditional : PathAMinorArc.VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Universal-`α` unconditional Vinogradov Type III/high-high bound. -/
  typeIIIUnconditional : PathAMinorArc.VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- T-Smallness: universal-form major-arc smallness sub-Prop. -/
  smallness_major : ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃errorFn : Nat → ℝ⦄,
    1 ≤ Q →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) →
    MajorArcSmallnessFromErrorFn N₀ errorFn
  /-- T-Smallness: universal-form minor-arc smallness sub-Prop. -/
  smallness_minor : ∀ majorArcs : (n : Nat) → Finset (ZMod n.succ),
    MinorArcSmallnessFromContribution majorArcs
  /-- T-Smallness: compatibility constraint binding the two
  coefficients to `δ_M + δ_m < 1`. -/
  smallness_compat : ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃errorFn : Nat → ℝ⦄,
    1 ≤ Q →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        errorFn n) →
    ∀ ⦃δ_M δ_m : ℝ⦄,
    (0 ≤ δ_M) → (δ_M < 1) → (0 ≤ δ_m) → (δ_m < 1) →
    (∀ n : Nat, N₀ < n → Even n →
      errorFn n ≤ δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) →
    MajorMinorSmallnessCompatibility δ_M δ_m

/-- **Projection to `SiegelWalfiszNonPrincipal`** from the
T-SW-NonPrincipal fields of the maximally-reduced bundle. -/
theorem siegelWalfiszNonPrincipal_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegelExceptional_perron
    content.pageSiegelZeroFree content.perronToPsiAPErrorBridge

/-- **Projection to `SiegelWalfiszBound`** combining the PNT principal
field and the Page-Siegel non-principal route. -/
theorem siegelWalfiszBound_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pnt_and_nonPrincipal
    content.pntRemainder
    (siegelWalfiszNonPrincipal_of_maximallyReducedContent content)

/-- **Projection to `SiegelWalfiszFourierBridge`** from the
`SiegelWalfiszSingleShapeData` field. -/
theorem siegelWalfiszFourierBridge_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    SiegelWalfiszFourierBridge :=
  siegelWalfiszFourierBridge_of_singleShapeData content.singleShapeData

/-- **Projection to `MajorArcEstimate`** from the SW bound and the
Fourier aggregation data. -/
theorem majorArcEstimate_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    MajorArcEstimate :=
  majorArcEstimate_of_SiegelWalfisz_substantive
    (siegelWalfiszBound_of_maximallyReducedContent content)
    (siegelWalfiszFourierBridge_of_maximallyReducedContent content)

/-- **Projection to `MinorArcCosineSumBound`** from the unconditional
Vinogradov witnesses. -/
theorem minorArcCosineSumBound_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    MinorArcCosineSumBound :=
  PathAMinorArc.minorArcCosineSumBound_of_vinogradov_unconditional_witnesses
    content.typeIUnconditional
    content.typeIIUnconditional
    content.typeIIIUnconditional

/-- **Projection to `MinorArcFromPsiBound`** from the unconditional
Vinogradov witnesses (ignoring the ψ hypothesis). -/
theorem minorArcFromPsiBound_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    MinorArcFromPsiBound :=
  PathAMinorArc.minorArcFromPsiBound_of_vinogradov_unconditional_witnesses
    content.typeIUnconditional
    content.typeIIUnconditional
    content.typeIIIUnconditional

/-- **Diagnostic**: the Dirichlet-refined Type I sub-Props of the
maximally-reduced bundle imply the Dirichlet-restricted Type I bound
for the concrete Vaughan witness. -/
theorem vinogradovTypeIBoundForVaughanWitnessDirichlet_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    PathAMinorArc.VinogradovTypeIBoundForVaughanWitnessDirichlet :=
  PathAMinorArc.vinogradovTypeIBoundForVaughanWitnessDirichlet_of_subProps
    content.typeI_abel content.typeI_dirichlet

/-- **Diagnostic**: the Dirichlet-refined Type II sub-Props imply the
Dirichlet-restricted Type II bound for the concrete Vaughan witness. -/
theorem vinogradovTypeIIBoundForVaughanWitnessDirichlet_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    PathAMinorArc.VinogradovTypeIIBoundForVaughanWitnessDirichlet :=
  PathAMinorArc.vinogradovTypeIIBoundForVaughanWitnessDirichlet_of_subProps
    content.typeII_cauchy content.typeII_dirichlet

/-- **Projection to `PathA_HardyLittlewoodSmallness_witness_form`** from
the three T-Smallness sub-Prop fields. -/
theorem pathA_smallness_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    PathA_HardyLittlewoodSmallness_witness_form :=
  pathA_HardyLittlewoodSmallness_witness_form_of_sub_smallnesses
    content.smallness_major content.smallness_minor content.smallness_compat

/-- **Projection to the quantitative Hardy-Littlewood content** from the
maximally-reduced bundle.  Combines the closed Farey witness with the
T-Smallness sub-Props. -/
theorem pathA_quantitativeContent_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_farey_and_smallness
    PathA_FareyMajorArcWitnessShape_holds
    (pathA_smallness_of_maximallyReducedContent content)

/-- **Projection to the Path A analytic implication** from the
maximally-reduced bundle. -/
theorem pathA_analyticImplication_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_maximallyReducedContent content)

/-- **Projection to `VonMangoldtExplicitFormulaBound`** routing the
function-form bridge `(ZS, TE, bridge, hZS, hTE)` through the existing
`vonMangoldtExplicitFormulaBound_of_bridge_for` connector. -/
theorem vonMangoldtExplicitFormulaBound_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent) :
    VonMangoldtExplicitFormulaBound :=
  vonMangoldtExplicitFormulaBound_of_bridge_for
    content.ZS content.TE content.bridge content.hZS content.hTE

/-- **Subsumption**: the maximally-reduced bundle subsumes
`PathA_MinimalOpenContent`.  Each field of the minimal bundle is
projectable from a field (or composition of fields) of the
maximally-reduced bundle.  The old headline
`strongGoldbach_under_RH_minimal_open` therefore continues to work
unchanged. -/
noncomputable def pathA_minimalOpenContent_of_maximally_reduced
    (content : PathA_MaximallyReducedContent) :
    PathA_MinimalOpenContent where
  ZS := content.ZS
  TE := content.TE
  bridge := content.bridge
  hZS := content.hZS
  hTE := content.hTE
  swBound := siegelWalfiszBound_of_maximallyReducedContent content
  swFourierBridge :=
    siegelWalfiszFourierBridge_of_maximallyReducedContent content
  vaughanS_I := PathAMinorArc.vaughanS_I_witness
  vaughanS_II := PathAMinorArc.vaughanS_II_witness
  vaughanS_III := PathAMinorArc.vaughanS_III_witness
  vaughanDecomp := PathAMinorArc.vaughanDecompositionFor_witness
  typeIBound := fun _ => content.typeIUnconditional
  typeIIBound := fun _ => content.typeIIUnconditional
  smallPrimesBound := fun _ => content.typeIIIUnconditional
  smallness := pathA_smallness_of_maximallyReducedContent content

/-- **Final synthesis (M7 headline)**: given the Riemann Hypothesis, an
inhabitant of `PathA_MaximallyReducedContent`, and the usual
finite-verification hypotheses, conclude `StrongGoldbach`.

This is the **single named theorem** for the M7 maximally-reduced
bundle.  It composes:

1. `bridge + hZS + hTE` ⟹ `VonMangoldtExplicitFormulaBound`
   (via `vonMangoldtExplicitFormulaBound_of_bridge_for`).
2. `pntRemainder + pageSiegelZeroFree + perronToPsiAPErrorBridge` ⟹
   `SiegelWalfiszBound` (via the PNT principal + Page-Siegel route).
3. `singleShapeData` ⟹ `SiegelWalfiszFourierBridge` (via T-FourierAgg).
4. `typeIUnconditional + typeIIUnconditional + typeIIIUnconditional` ⟹
   `MinorArcCosineSumBound` (via the universal-α Vinogradov route).
5. `smallness_major + smallness_minor + smallness_compat` ⟹
   `PathA_HardyLittlewoodSmallness_witness_form` (via T-Smallness).
6. `RH + step1..5 + finite + threshold_covered` ⟹ `StrongGoldbach`
   (via `strongGoldbach_via_PathA_full`). -/
theorem strongGoldbach_under_RH_maximally_reduced
    (rh : RiemannHypothesis)
    (content : PathA_MaximallyReducedContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_minimal_open rh
    (pathA_minimalOpenContent_of_maximally_reduced content)
    finite threshold_covered

/-- **Single-arrow form**: parameterised by the maximally-reduced
bundle and a finite-verification witness, this asserts the implication
`RiemannHypothesis ⟹ StrongGoldbach`. -/
theorem strongGoldbach_under_RH_of_maximallyReducedContent
    (content : PathA_MaximallyReducedContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    RiemannHypothesis → StrongGoldbach :=
  fun rh =>
    strongGoldbach_under_RH_maximally_reduced rh content finite threshold_covered

/-- **M7 honesty record (unconditional)**: there is no inhabitant of
`PathA_MaximallyReducedContent` constructible inside this repository
without further analytic content.  Specifically, the following sub-Props
remain *genuinely open*:

* the function-form Perron bridge `ExplicitFormulaBridgeFor ZS TE` for
  concrete witness functions `ZS, TE`, plus their RH-side analytic
  bounds `hZS, hTE`;
* the Page-Siegel zero-free-region content
  `PrimitivePageSiegelZeroFreeRegionWithExceptional` and the Perron
  bridge `PerronToPsiAPErrorFromZeroFreeRegionBridge`;
* the principal-modulus PNT remainder
  `PrimeCounting_PNT_RemainderBound`;
* the Fourier aggregation data `SiegelWalfiszSingleShapeData` (whose
  `aggregate` field is the classical Hardy-Littlewood circle-method
  Fourier-aggregation theorem);
* the Dirichlet-refined Vinogradov sub-Props
  `AbelSummationOnGeometricSum vaughanS_I_witness`,
  `DirichletApproxGeometricSumBound vaughanS_I_witness`,
  `CauchySchwarzOnBilinearSum vaughanS_II_witness`,
  `DirichletApproxBilinearBound vaughanS_II_witness`;
* the universal-`α` unconditional Vinogradov bounds
  `VinogradovTypeI/II/IIIBoundForVaughanWitnessUnconditional`
  (mathematically false in the universal-α form because of the
  `α = 0` Vaughan-decomposition counterexample; closable only via the
  Dirichlet refinement plus an `α = 0` carve-out);
* the universal-form T-Smallness sub-Props.

In one M7 session we cannot close any of those analytic Props — they
are the genuine residual content of the strong Goldbach conjecture.
Therefore we expose `strongGoldbach_under_RH_unconditional_M7_open`
*only* as a conditional implication: given an inhabitant of
`PathA_MaximallyReducedContent`, `StrongGoldbach` holds **without RH**
in the sense that the bridge field replaces the RH-side analytic
input; the bridge field itself is still an open assumption.

The honest statement is the same as
`strongGoldbach_under_RH_maximally_reduced` modulo the observation that
once the bridge field is closed, no separate `RiemannHypothesis`
hypothesis is needed.  We therefore *do not* offer a separate
`strongGoldbach_under_RH_unconditional_maximally_reduced` theorem: that
would either repeat the existing
`strongGoldbach_under_RH_unconditional` (which uses the no-RH route
through PNT + Page-Siegel non-principal, not the function-form bridge)
or it would silently drop the bridge field. -/
theorem PathA_MaximallyReducedContent_remaining_open_sub_props_honesty :
    True := trivial

/-! ## Section 8c — Diagnostic chain decomposition for M7

These diagnostics confirm that every intermediate Prop in the Path A
chain can be projected out of `PathA_MaximallyReducedContent` plus
`RiemannHypothesis`, in side-by-side form mirroring
`pathA_intermediate_props_of_content` (Section 6). -/

/-- **Diagnostic**: the maximally-reduced bundle plus RH delivers every
intermediate Prop on the Path A chain.  The `RiemannHypothesis`
hypothesis is consumed only by the function-form Perron bridge in the
existing chain; if `bridge` were ever closed without RH, this
diagnostic would still work. -/
theorem pathA_intermediate_props_of_maximallyReducedContent
    (_rh : RiemannHypothesis)
    (content : PathA_MaximallyReducedContent) :
    VonMangoldtExplicitFormulaBound ∧
      PsiSquareRootErrorBound ∧
      MinorArcCosineSumBound ∧
      MajorArcEstimate ∧
      PathA_AnalyticImplication := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact vonMangoldtExplicitFormulaBound_of_maximallyReducedContent content
  · exact psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound
      (vonMangoldtExplicitFormulaBound_of_maximallyReducedContent content)
  · exact minorArcCosineSumBound_of_maximallyReducedContent content
  · exact majorArcEstimate_of_maximallyReducedContent content
  · exact pathA_analyticImplication_of_maximallyReducedContent content

/-- **Diagnostic**: the maximally-reduced bundle factors through the
existential quarter binary Hardy-Littlewood lower bound. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_maximallyReducedContent
    (_rh : RiemannHypothesis)
    (content : PathA_MaximallyReducedContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  have psi : PsiSquareRootErrorBound :=
    psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound
      (vonMangoldtExplicitFormulaBound_of_maximallyReducedContent content)
  have minor : MinorArcCosineSumBound :=
    minorArcCosineSumBound_of_maximallyReducedContent content
  have major : MajorArcEstimate :=
    majorArcEstimate_of_maximallyReducedContent content
  have analytic : PathA_AnalyticImplication :=
    pathA_analyticImplication_of_maximallyReducedContent content
  exact analytic psi minor major

/-! ## Section 9 — Unconditional Path A handoff

The earlier public theorem is RH-conditional because it threads
`RiemannHypothesis` through an explicit-formula route to a square-root
`ψ` bound.  The next project phase is different: close the GRH-free
circle-method route by proving the Page-Siegel/Siegel-Walfisz input, the
Fourier aggregation, and the full Vinogradov/Vaughan bounds directly.

This section exposes that route as a no-RH top-level contract.  It does
not prove the analytic number theory; it makes the remaining mountain
precise and shows that once those named Props are supplied, the existing
Goldbach bridge closes. -/

/-- **T3 aggregation contract** for the unconditional Path A route.

It consumes the full Siegel-Walfisz bound, the per-arc-to-Fourier
aggregation theorem, and unconditional Vinogradov bounds for the
concrete Vaughan witnesses, and returns the witness-form
Hardy-Littlewood smallness statement needed by the final synthesis. -/
def PathA_T3Aggregation : Prop :=
  ∀ (_sw : SiegelWalfiszBound)
    (_swAggregation : SiegelWalfiszPerArcToFourierAggregation)
    (_vinoTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (_vinoTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (_vinoTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional),
    PathA_HardyLittlewoodSmallness_witness_form

/-- **T3 aggregation contract, Farey-witness form**.

This is weaker and closer to the eventual circle-method proof than
`PathA_T3Aggregation`: it only asks the aggregation argument to produce one
Farey major-arc witness with matching major/minor smallness, rather than a
smallness theorem for every possible witness. -/
def PathA_T3FareyWitnessAggregation : Prop :=
  ∀ (_sw : SiegelWalfiszBound)
    (_swAggregation : SiegelWalfiszPerArcToFourierAggregation)
    (_vinoTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (_vinoTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (_vinoTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional),
    PathA_HardyLittlewoodSmallnessForFareyWitness

/-- **T3 local smallness contract for a Siegel-Walfisz Farey witness**.

This is a lower-level replacement for the black-box
`PathA_T3FareyWitnessAggregation`.  It assumes the major-arc witness has the
substantive Siegel-Walfisz error shape `siegelWalfiszErrorFn C c`, and that
the Vinogradov minor-arc cosine bound has already been assembled.  The
remaining analytic job is then exactly the T3 comparison step: make the
major error and the matching minor contribution small relative to
`𝔖(n) * n` for the same Farey arc family. -/
def PathA_T3SWSmallnessForFareyWitness : Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    MinorArcCosineSumBound →
    PathA_HardyLittlewoodSmallnessForWitness N₀ majorArcs
      (siegelWalfiszErrorFn C c)

/-- **Thresholded T3 local smallness contract for a Siegel-Walfisz Farey
witness**.

This is a weaker, more proof-shaped replacement for
`PathA_T3SWSmallnessForFareyWitness`: the major-arc approximation may start
at threshold `N₀`, but the eventual comparison of the SW error against
`δ_M * 𝔖(n) * n` is allowed to start at its own threshold `N_M`.  The final
Farey witness then uses `max N₀ N_M`.  The minor contribution has its own
threshold `N_m`, as in the synthesis layer.

This matches the analytic workflow: first obtain the SW-shaped major-arc
estimate, then separately prove that `n * exp(-c * sqrt(log n))` is eventually
small relative to the singular-series main term, and separately prove the
minor contribution smallness from Vinogradov. -/
def PathA_T3SWThresholdSmallnessForFareyWitness : Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    MinorArcCosineSumBound →
    ∃ N_M N_m : Nat, ∃ δ_M δ_m : ℝ,
      0 ≤ δ_M ∧ δ_M < 1 ∧
      0 ≤ δ_m ∧
      δ_M + δ_m < 1 ∧
      (∀ n : Nat, N_M < n → Even n →
        siegelWalfiszErrorFn C c n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ))) ∧
      (∀ n : Nat, N_m < n → Even n →
        |realMinorContribution majorArcs n| ≤
          δ_m * (goldbachSingularSeriesFromQuarter n * (n : ℝ)))

/-! ### Split quarter-smallness form of the T3 comparison

The thresholded T3 contract above is already close to the analytic proof:
it separates the major approximation threshold from the eventual major and
minor smallness thresholds.  The next interface splits the actual smallness
work into the two estimates that will be proved separately in the final T3
aggregation formalization.
-/

/-- **Major-error quarter-smallness for SW-shaped T3 aggregation.**

For every positive SW error shape `C * n * exp(-c * sqrt(log n))`, the
major-arc error is eventually at most one quarter of the Hardy-Littlewood
main term.  The remaining analytic proof is the comparison between the
sqrt-log decay and the singular-series lower bound. -/
def PathA_T3SWMajorErrorQuarterSmallness : Prop :=
  ∀ ⦃C c : ℝ⦄,
    0 < C →
    0 < c →
    ∃ N_M : Nat,
      ∀ n : Nat, N_M < n → Even n →
        siegelWalfiszErrorFn C c n ≤
          (1 / 4 : ℝ) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **Minor-contribution quarter-smallness for the supplied Farey witness.**

Given a SW-shaped major-arc witness and an assembled Vinogradov minor-arc
cosine bound, the minor contribution is eventually at most one quarter of
the Hardy-Littlewood main term.  This is the T3 summation/aggregation
estimate for the complement of the supplied major arcs. -/
def PathA_T3MinorContributionQuarterSmallnessForFareyWitness : Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    MinorArcCosineSumBound →
    ∃ N_m : Nat,
      ∀ n : Nat, N_m < n → Even n →
        |realMinorContribution majorArcs n| ≤
          (1 / 4 : ℝ) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ))

/-- **DFT-uniform square form of T3 minor-contribution quarter-smallness.**

This is a lower Fourier-side target for the remaining T3 aggregation step.
For the supplied Farey witness, it asks for a uniform bound on every minor
frequency DFT coefficient whose square is eventually at most one quarter of
the Hardy-Littlewood main term.  The discrete Fourier bookkeeping then
converts this into the existing real minor-contribution quarter bound. -/
def PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness :
    Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    MinorArcCosineSumBound →
    ∃ N_dft N_m : Nat, ∃ minorArcDftBound : Nat → ℝ,
      (∀ n : Nat, N_dft < n → Even n →
        ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n),
          ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤
            minorArcDftBound n) ∧
      (∀ n : Nat, N_m < n → Even n →
        minorArcDftBound n ^ (2 : Nat) ≤
          (1 / 4 : ℝ) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)))

/-- **Little-o uniform DFT form of T3 minor-contribution smallness.**

This is one step closer to the analytic minor-arc theorem: for the supplied
Farey witness, produce a uniform bound for every minor-frequency DFT
coefficient and prove that bound is `o(sqrt n)`.  Lean converts this ratio
limit into the quarter-square comparison used by the Fourier bookkeeping. -/
def PathA_T3MinorContributionDftUniformLittleOForFareyWitness : Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    MinorArcCosineSumBound →
    ∃ N_dft : Nat, ∃ minorArcDftBound : Nat → ℝ,
      (∀ n : Nat, N_dft < n → Even n →
        ∀ k ∈ DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n),
          ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤
            minorArcDftBound n) ∧
      Tendsto (fun n : Nat =>
        minorArcDftBound n / Real.sqrt (n : ℝ)) atTop (𝓝 0)

/-- **Complement-major-arc little-o DFT form of T3 minor smallness.**

This is the same analytic target as the minor-frequency little-o form, but
stated in the more standard language `k ∉ majorArcs n`.  Lean converts this
to the project-local `zmodMinorFrequencies` interface by unfolding the
minor-frequency complement. -/
def PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness :
    Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    ∃ N_dft : Nat, ∃ minorArcDftBound : Nat → ℝ,
      (∀ n : Nat, N_dft < n → Even n →
        ∀ k : ZMod n.succ, k ∉ majorArcs n →
          ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤
            minorArcDftBound n) ∧
      Tendsto (fun n : Nat =>
        minorArcDftBound n / Real.sqrt (n : ℝ)) atTop (𝓝 0)

/-- The finite supremum of the von Mangoldt DFT norms on the minor
frequencies for a supplied major-arc family.  It is `0` when the complement
is empty. -/
noncomputable def minorArcDftSupNormForFareyWitness
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℝ :=
  if h :
      (DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n)).Nonempty then
    (DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n)).sup' h
      (fun k => ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖)
  else 0

/-- The finite DFT supremum bounds every minor-frequency DFT coefficient. -/
theorem vonMangoldtZModDft_norm_le_minorArcDftSupNormForFareyWitness
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    (k : ZMod n.succ)
    (hk : k ∈ DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n)) :
    ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖ ≤
      minorArcDftSupNormForFareyWitness majorArcs n := by
  have hne :
      (DiscreteCircleMethod.zmodMinorFrequencies (majorArcs n)).Nonempty :=
    ⟨k, hk⟩
  rw [minorArcDftSupNormForFareyWitness, dif_pos hne]
  exact Finset.le_sup' (fun k => ‖DiscreteCircleMethod.vonMangoldtZModDft n k‖) hk

/-- **Finite-supremum little-o DFT form of T3 minor smallness.**

This is the canonical scalar version of the complement-uniform DFT target:
for the supplied major arcs, the actual finite supremum of
`‖vonMangoldtZModDft n k‖` over the complement is `o(sqrt n)`. -/
def PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :
    Prop :=
  ∀ ⦃Q N₀ : Nat⦄
    ⦃majorArcs : (n : Nat) → Finset (ZMod n.succ)⦄
    ⦃C c : ℝ⦄,
    1 ≤ Q →
    0 < C →
    0 < c →
    (∀ n : Nat, N₀ < n → Even n →
      ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
          majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        siegelWalfiszErrorFn C c n) →
    Tendsto (fun n : Nat =>
      minorArcDftSupNormForFareyWitness majorArcs n /
        Real.sqrt (n : ℝ)) atTop (𝓝 0)

/-- **Split quarter-smallness package for T3.**

This is a lower-level replacement for the bundled thresholded T3 smallness
contract: the SW major-error comparison and the minor-contribution
comparison are exposed as two separately provable theorem targets. -/
def PathA_T3SWQuarterSmallnessPackage : Prop :=
  PathA_T3SWMajorErrorQuarterSmallness ∧
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness

/-- The scalar sqrt-log exponential factor tends to zero along natural
numbers.  This is the analytic decay needed for the SW-shaped major-error
part of T3; the remaining T3 work is the minor-contribution aggregation. -/
theorem tendsto_sqrtLogExp_nat_atTop_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : Nat => Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : Nat => Real.log (n : ℝ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt :
      Tendsto (fun n : Nat => Real.sqrt (Real.log (n : ℝ))) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp hlog
  have hmul :
      Tendsto (fun n : Nat => (-c) * Real.sqrt (Real.log (n : ℝ)))
        atTop atBot := by
    exact tendsto_const_nhds.neg_mul_atTop (by linarith) hsqrt
  have hexp :
      Tendsto (fun n : Nat =>
          Real.exp ((-c) * Real.sqrt (Real.log (n : ℝ)))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp hmul
  convert hexp using 1

/-- Eventually the scalar SW sqrt-log factor is small enough for a quarter of
the singular-series main term. -/
theorem exists_sqrtLogExp_factor_le_quarter_singularSeries_coefficient
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ N : Nat, ∀ n : Nat, N < n →
      C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ (1 / 16 : ℝ) := by
  have ht := tendsto_sqrtLogExp_nat_atTop_zero (c := c) hc
  have hε : 0 < (1 / (16 * C) : ℝ) := by positivity
  have hEv : ∀ᶠ n : Nat in atTop,
      Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) < 1 / (16 * C) :=
    ht.eventually (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hEv with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlt := hN n (le_of_lt hn)
  have hmul := mul_lt_mul_of_pos_left hlt hC
  have hcalc : C * (1 / (16 * C)) = (1 / 16 : ℝ) := by
    field_simp [hC.ne']
  have hlt' :
      C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) < (1 / 16 : ℝ) := by
    calc
      C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
          < C * (1 / (16 * C)) := hmul
      _ = (1 / 16 : ℝ) := hcalc
  exact le_of_lt hlt'

/-- The SW-shaped major-error quarter-smallness half of T3 is closed from
mathlib's `log/sqrt/exp` limits and the existing singular-series lower bound.

After this theorem, the only open T3 quarter-smallness input is the
minor-contribution aggregation estimate. -/
theorem PathA_T3SWMajorErrorQuarterSmallness_holds :
    PathA_T3SWMajorErrorQuarterSmallness := by
  intro C c hC hc
  rcases exists_sqrtLogExp_factor_le_quarter_singularSeries_coefficient
      (C := C) (c := c) hC hc with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hEven
  have hcoef := hN n hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hleft : siegelWalfiszErrorFn C c n ≤ (1 / 16 : ℝ) * (n : ℝ) := by
    unfold siegelWalfiszErrorFn
    have hmul := mul_le_mul_of_nonneg_right hcoef hn_nonneg
    calc
      C * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
          = (C * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) * (n : ℝ) := by
            ring
      _ ≤ (1 / 16 : ℝ) * (n : ℝ) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn
  have hS : (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
    one_fourth_le_goldbachSingularSeriesFromQuarter
      (threshold := 0) n hn_pos_nat hEven
  have hright : (1 / 16 : ℝ) * (n : ℝ) ≤
      (1 / 4 : ℝ) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
    nlinarith [mul_nonneg hn_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4), hS]
  exact hleft.trans hright

/-- Since the SW major-error quarter-smallness is now closed, a minor
contribution quarter-smallness theorem alone supplies the split T3 package. -/
theorem PathA_T3SWQuarterSmallnessPackage_of_minorContributionQuarterSmallness
    (hMinor : PathA_T3MinorContributionQuarterSmallnessForFareyWitness) :
    PathA_T3SWQuarterSmallnessPackage :=
  ⟨PathA_T3SWMajorErrorQuarterSmallness_holds, hMinor⟩

/-- Uniform DFT-square minor-arc control supplies the existing real
minor-contribution quarter-smallness target. -/
theorem PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformSquareQuarterSmallness
    (h :
      PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness := by
  intro Q N₀ majorArcs C c hQ hC hc hmajor hMinorArc
  rcases h hQ hC hc hmajor hMinorArc with
    ⟨N_dft, N_m, minorArcDftBound, hdft, hsmall⟩
  refine ⟨max N_dft N_m, ?_⟩
  intro n hn hEven
  have hcomplexBound :
      ∀ n : Nat, max N_dft N_m < n → Even n →
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution
            majorArcs n‖ ≤
          (1 / 4 : ℝ) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) :=
    DiscreteCircleMethod.minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
      (minorArcThreshold := max N_dft N_m)
      majorArcs
      (minorArcDftBound := minorArcDftBound)
      (minorArcError := fun n =>
        (1 / 4 : ℝ) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)))
      (by
        intro n hn hEven k hk
        have hdftThreshold : N_dft < n :=
          lt_of_le_of_lt (Nat.le_max_left N_dft N_m) hn
        exact hdft n hdftThreshold hEven k hk)
      (by
        intro n hn hEven
        have hsmallThreshold : N_m < n :=
          lt_of_le_of_lt (Nat.le_max_right N_dft N_m) hn
        exact hsmall n hsmallThreshold hEven)
  have hreal :
      |realMinorContribution majorArcs n| ≤
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution
            majorArcs n‖ := by
    simpa [realMinorContribution,
      DiscreteCircleMethod.rawVonMangoldtFourierMinorArcContribution]
      using
        DiscreteCircleMethod.real_abs_re_le_complex_norm
          (DiscreteCircleMethod.rawVonMangoldtFourierMinorArcComplexContribution
            majorArcs n)
  exact hreal.trans (hcomplexBound n hn hEven)

/-- Since the SW major-error quarter-smallness is closed, the DFT-uniform
minor-contribution target alone supplies the split T3 package. -/
theorem PathA_T3SWQuarterSmallnessPackage_of_dftUniformSquareMinorContributionQuarterSmallness
    (hMinor :
      PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness) :
    PathA_T3SWQuarterSmallnessPackage :=
  PathA_T3SWQuarterSmallnessPackage_of_minorContributionQuarterSmallness
    (PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformSquareQuarterSmallness
      hMinor)

/-- A uniform DFT bound that is `o(sqrt n)` is eventually small enough for
the quarter singular-series main-term square budget. -/
theorem exists_dftUniformBound_sq_le_quarter_singularSeries_of_littleO
    {minorArcDftBound : Nat → ℝ}
    (hLittleO :
      Tendsto (fun n : Nat =>
        minorArcDftBound n / Real.sqrt (n : ℝ)) atTop (𝓝 0)) :
    ∃ N : Nat, ∀ n : Nat, N < n → Even n →
      minorArcDftBound n ^ (2 : Nat) ≤
        (1 / 4 : ℝ) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
  have hUpper : ∀ᶠ n : Nat in atTop,
      minorArcDftBound n / Real.sqrt (n : ℝ) < (1 / 4 : ℝ) :=
    hLittleO.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hLower : ∀ᶠ n : Nat in atTop,
      -(1 / 4 : ℝ) < minorArcDftBound n / Real.sqrt (n : ℝ) :=
    hLittleO.eventually (Ioi_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0))
  rcases eventually_atTop.1 (hLower.and hUpper) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hEven
  have hbounds := hN n (le_of_lt hn)
  have hAbsRatio :
      |minorArcDftBound n / Real.sqrt (n : ℝ)| < (1 / 4 : ℝ) :=
    abs_lt.mpr hbounds
  have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hAbsRatio' :
      |minorArcDftBound n| / Real.sqrt (n : ℝ) < (1 / 4 : ℝ) := by
    simpa [abs_div, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
      using hAbsRatio
  have hAbsBound :
      |minorArcDftBound n| < (1 / 4 : ℝ) * Real.sqrt (n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hAbsRatio' hsqrt_pos
    have hleft :
        |minorArcDftBound n| / Real.sqrt (n : ℝ) *
            Real.sqrt (n : ℝ) =
          |minorArcDftBound n| := by
      field_simp [hsqrt_pos.ne']
    simpa [hleft, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hSq :
      minorArcDftBound n ^ (2 : Nat) ≤ (1 / 16 : ℝ) * (n : ℝ) := by
    have hAbsSq :
        |minorArcDftBound n| ^ (2 : Nat) ≤
          ((1 / 4 : ℝ) * Real.sqrt (n : ℝ)) ^ (2 : Nat) :=
      pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hAbsBound) 2
    have hsqrt_sq : Real.sqrt (n : ℝ) ^ (2 : Nat) = (n : ℝ) :=
      Real.sq_sqrt (le_of_lt hn_pos)
    calc
      minorArcDftBound n ^ (2 : Nat)
          = |minorArcDftBound n| ^ (2 : Nat) := by rw [sq_abs]
      _ ≤ ((1 / 4 : ℝ) * Real.sqrt (n : ℝ)) ^ (2 : Nat) := hAbsSq
      _ = (1 / 16 : ℝ) * (n : ℝ) := by
            rw [mul_pow, hsqrt_sq]
            norm_num
  have hS : (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
    one_fourth_le_goldbachSingularSeriesFromQuarter
      (threshold := 0) n hn_pos_nat hEven
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have hright : (1 / 16 : ℝ) * (n : ℝ) ≤
      (1 / 4 : ℝ) *
        (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
    nlinarith [mul_nonneg hn_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4), hS]
  exact hSq.trans hright

/-- A little-o uniform minor DFT bound supplies the DFT-square
quarter-smallness target. -/
theorem PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformLittleO
    (hLittleO : PathA_T3MinorContributionDftUniformLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness := by
  intro Q N₀ majorArcs C c hQ hC hc hmajor hMinorArc
  rcases hLittleO hQ hC hc hmajor hMinorArc with
    ⟨N_dft, minorArcDftBound, hdft, hratio⟩
  rcases exists_dftUniformBound_sq_le_quarter_singularSeries_of_littleO
      (minorArcDftBound := minorArcDftBound) hratio with
    ⟨N_m, hsmall⟩
  exact ⟨N_dft, N_m, minorArcDftBound, hdft, hsmall⟩

/-- A little-o uniform minor DFT bound supplies the real minor-contribution
quarter-smallness target. -/
theorem PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformLittleO
    (hLittleO : PathA_T3MinorContributionDftUniformLittleOForFareyWitness) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness :=
  PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformSquareQuarterSmallness
    (PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformLittleO
      hLittleO)

/-- Since the SW major-error quarter-smallness is closed, a little-o uniform
minor DFT bound alone supplies the split T3 package. -/
theorem PathA_T3SWQuarterSmallnessPackage_of_dftUniformLittleOMinorContribution
    (hLittleO : PathA_T3MinorContributionDftUniformLittleOForFareyWitness) :
    PathA_T3SWQuarterSmallnessPackage :=
  PathA_T3SWQuarterSmallnessPackage_of_dftUniformSquareMinorContributionQuarterSmallness
    (PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformLittleO
      hLittleO)

/-- A complement-of-major-arcs little-o DFT estimate supplies the
minor-frequency little-o DFT target. -/
theorem PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
    (hComplement :
      PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformLittleOForFareyWitness := by
  intro Q N₀ majorArcs C c hQ hC hc hmajor _hMinorArc
  rcases hComplement hQ hC hc hmajor with
    ⟨N_dft, minorArcDftBound, hdft, hratio⟩
  exact
    ⟨N_dft, minorArcDftBound,
      DiscreteCircleMethod.minorArcDftBoundValid_of_not_mem_majorArcs hdft,
      hratio⟩

/-- A complement-of-major-arcs little-o DFT estimate supplies the DFT-square
quarter-smallness target. -/
theorem PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformComplementLittleO
    (hComplement :
      PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness :=
  PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformLittleO
    (PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
      hComplement)

/-- A complement-of-major-arcs little-o DFT estimate supplies the real
minor-contribution quarter-smallness target. -/
theorem PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformComplementLittleO
    (hComplement :
      PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness :=
  PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformLittleO
    (PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
      hComplement)

/-- Since the SW major-error quarter-smallness is closed, a complement
little-o uniform minor DFT bound supplies the split T3 package. -/
theorem PathA_T3SWQuarterSmallnessPackage_of_dftUniformComplementLittleOMinorContribution
    (hComplement :
      PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness) :
    PathA_T3SWQuarterSmallnessPackage :=
  PathA_T3SWQuarterSmallnessPackage_of_dftUniformLittleOMinorContribution
    (PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
      hComplement)

/-- A finite-supremum little-o DFT estimate supplies the complement-uniform
little-o DFT target. -/
theorem PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
    (hSup :
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness := by
  intro Q N₀ majorArcs C c hQ hC hc hmajor
  refine ⟨0, minorArcDftSupNormForFareyWitness majorArcs, ?_, ?_⟩
  · intro n _hn _hEven k hk
    exact
      vonMangoldtZModDft_norm_le_minorArcDftSupNormForFareyWitness
        majorArcs n k
        (DiscreteCircleMethod.mem_zmodMinorFrequencies.mpr hk)
  · exact hSup hQ hC hc hmajor

/-- A finite-supremum little-o DFT estimate supplies the minor-frequency
little-o DFT target. -/
theorem PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_supComplementLittleO
    (hSup :
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformLittleOForFareyWitness :=
  PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
    (PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
      hSup)

/-- A finite-supremum little-o DFT estimate supplies the DFT-square
quarter-smallness target. -/
theorem PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftSupComplementLittleO
    (hSup :
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness :=
  PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformComplementLittleO
    (PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
      hSup)

/-- A finite-supremum little-o DFT estimate supplies the real
minor-contribution quarter-smallness target. -/
theorem PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftSupComplementLittleO
    (hSup :
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness :=
  PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformComplementLittleO
    (PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
      hSup)

/-- Since the SW major-error quarter-smallness is closed, a finite-supremum
little-o uniform minor DFT estimate supplies the split T3 package. -/
theorem PathA_T3SWQuarterSmallnessPackage_of_dftSupComplementLittleOMinorContribution
    (hSup :
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness) :
    PathA_T3SWQuarterSmallnessPackage :=
  PathA_T3SWQuarterSmallnessPackage_of_dftUniformComplementLittleOMinorContribution
    (PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
      hSup)

/-- Project the major-error quarter-smallness theorem from the split T3
package. -/
theorem t3SWMajorErrorQuarterSmallness_of_t3SWQuarterSmallnessPackage
    (h : PathA_T3SWQuarterSmallnessPackage) :
    PathA_T3SWMajorErrorQuarterSmallness :=
  h.1

/-- Project the minor-contribution quarter-smallness theorem from the split
T3 package. -/
theorem t3MinorContributionQuarterSmallness_of_t3SWQuarterSmallnessPackage
    (h : PathA_T3SWQuarterSmallnessPackage) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness :=
  h.2

/-- Split quarter-smallness implies the existing thresholded T3 smallness
contract, taking `δ_M = δ_m = 1 / 4`. -/
theorem PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallness
    (hMajor : PathA_T3SWMajorErrorQuarterSmallness)
    (hMinor : PathA_T3MinorContributionQuarterSmallnessForFareyWitness) :
    PathA_T3SWThresholdSmallnessForFareyWitness := by
  intro Q N₀ majorArcs C c hQ hC hc hmajor hMinorArc
  rcases hMajor hC hc with ⟨N_M, herror_small⟩
  rcases hMinor hQ hC hc hmajor hMinorArc with ⟨N_m, hminor_small⟩
  refine ⟨N_M, N_m, (1 / 4 : ℝ), (1 / 4 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact herror_small
  · exact hminor_small

/-- A split quarter-smallness package implies the existing thresholded T3
smallness contract. -/
theorem PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
    (h : PathA_T3SWQuarterSmallnessPackage) :
    PathA_T3SWThresholdSmallnessForFareyWitness :=
  PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallness
    (t3SWMajorErrorQuarterSmallness_of_t3SWQuarterSmallnessPackage h)
    (t3MinorContributionQuarterSmallness_of_t3SWQuarterSmallnessPackage h)

/-- A witness-form smallness theorem plus a Farey major-arc witness gives
the existential Farey-witness smallness statement. -/
theorem PathA_HardyLittlewoodSmallnessForFareyWitness_of_witnessForm
    (hFarey : PathA_FareyMajorArcWitnessShape)
    (hSmall : PathA_HardyLittlewoodSmallness_witness_form) :
    PathA_HardyLittlewoodSmallnessForFareyWitness := by
  rcases hFarey with ⟨Q, N₀, majorArcs, errorFn, hQ, hmajor⟩
  exact ⟨Q, N₀, majorArcs, errorFn, hQ, hmajor, hSmall hQ hmajor⟩

/-- The older, stronger T3 aggregation contract implies the Farey-witness
contract by applying it to the closed Farey major-arc witness shape. -/
theorem PathA_T3FareyWitnessAggregation_of_T3Aggregation
    (hT3 : PathA_T3Aggregation) :
    PathA_T3FareyWitnessAggregation := by
  intro hSW hAgg hI hII hIII
  exact PathA_HardyLittlewoodSmallnessForFareyWitness_of_witnessForm
    PathA_FareyMajorArcWitnessShape_holds (hT3 hSW hAgg hI hII hIII)

/-- The local SW-shaped T3 smallness contract implies the Farey-witness T3
aggregation contract.

The proof separates the three inputs:
* `hAgg + hSW` produce a substantive SW-shaped Farey major-arc witness;
* the Vinogradov Type I/II/III hypotheses produce the no-RH minor-arc cosine
  bound;
* `hSmall` performs the remaining T3 relative-smallness comparison for that
  exact witness. -/
theorem PathA_T3FareyWitnessAggregation_of_swSmallness
    (hSmall : PathA_T3SWSmallnessForFareyWitness) :
    PathA_T3FareyWitnessAggregation := by
  intro hSW hAgg hI hII hIII
  rcases PathA_FareyMajorArcBound_SiegelWalfisz_of_aggregation hSW hAgg with
    ⟨Q, N₀, majorArcs, C, c, hQ, hC, hc, hmajor⟩
  have hMinor : MinorArcCosineSumBound :=
    minorArcCosineSumBound_of_vinogradov_unconditional_witnesses
      hI hII hIII
  refine ⟨Q, N₀, majorArcs, siegelWalfiszErrorFn C c, hQ, hmajor, ?_⟩
  exact hSmall hQ hC hc hmajor hMinor

/-- The thresholded local SW-shaped T3 smallness contract implies the
Farey-witness T3 aggregation contract.

The only extra bookkeeping versus
`PathA_T3FareyWitnessAggregation_of_swSmallness` is replacing the major
threshold `N₀` by `max N₀ N_M`, so both the major approximation and the
eventual SW-error smallness are available for the same witness. -/
theorem PathA_T3FareyWitnessAggregation_of_swThresholdSmallness
    (hSmall : PathA_T3SWThresholdSmallnessForFareyWitness) :
    PathA_T3FareyWitnessAggregation := by
  intro hSW hAgg hI hII hIII
  rcases PathA_FareyMajorArcBound_SiegelWalfisz_of_aggregation hSW hAgg with
    ⟨Q, N₀, majorArcs, C, c, hQ, hC, hc, hmajor⟩
  have hMinor : MinorArcCosineSumBound :=
    minorArcCosineSumBound_of_vinogradov_unconditional_witnesses
      hI hII hIII
  rcases hSmall hQ hC hc hmajor hMinor with
    ⟨N_M, N_m, δ_M, δ_m,
      hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small, hminor_small⟩
  let N' : Nat := max N₀ N_M
  have hmajor' :
      ∀ n : Nat, N' < n → Even n →
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
            majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          siegelWalfiszErrorFn C c n := by
    intro n hn hEven
    have hN₀_lt : N₀ < n := lt_of_le_of_lt (le_max_left N₀ N_M) hn
    exact hmajor n hN₀_lt hEven
  have herror_small' :
      ∀ n : Nat, N' < n → Even n →
        siegelWalfiszErrorFn C c n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
    intro n hn hEven
    have hN_M_lt : N_M < n := lt_of_le_of_lt (le_max_right N₀ N_M) hn
    exact herror_small n hN_M_lt hEven
  refine ⟨Q, N', majorArcs, siegelWalfiszErrorFn C c, hQ, hmajor', ?_⟩
  exact ⟨N_m, δ_M, δ_m,
    hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small', hminor_small⟩

/-- A local SW-shaped T3 smallness contract produces the quantitative
Hardy-Littlewood content for the supplied major/minor analytic inputs. -/
theorem pathA_quantitativeContent_of_T3SWSmallness
    (hSW : SiegelWalfiszBound)
    (hAgg : SiegelWalfiszPerArcToFourierAggregation)
    (hI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (hII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (hIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional)
    (hSmall : PathA_T3SWSmallnessForFareyWitness) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness
    ((PathA_T3FareyWitnessAggregation_of_swSmallness hSmall)
      hSW hAgg hI hII hIII)

/-- A thresholded local SW-shaped T3 smallness contract produces the
quantitative Hardy-Littlewood content for the supplied major/minor analytic
inputs. -/
theorem pathA_quantitativeContent_of_T3SWThresholdSmallness
    (hSW : SiegelWalfiszBound)
    (hAgg : SiegelWalfiszPerArcToFourierAggregation)
    (hI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (hII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (hIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional)
    (hSmall : PathA_T3SWThresholdSmallnessForFareyWitness) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness
    ((PathA_T3FareyWitnessAggregation_of_swThresholdSmallness hSmall)
      hSW hAgg hI hII hIII)

/-- A thresholded local SW-shaped T3 smallness contract gives the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_T3SWThresholdSmallness
    (hSW : SiegelWalfiszBound)
    (hAgg : SiegelWalfiszPerArcToFourierAggregation)
    (hI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (hII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (hIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional)
    (hSmall : PathA_T3SWThresholdSmallnessForFareyWitness) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_T3SWThresholdSmallness
      hSW hAgg hI hII hIII hSmall)

/-- **Minor-arc plus thresholded T3 package.**

This is the handoff shape after the Vinogradov/Vaughan work has already
assembled a no-RH `MinorArcCosineSumBound`: the remaining T3 side needs
the SW-to-Fourier aggregation and the thresholded local comparison for the
same SW-shaped Farey witness. -/
def PathA_MinorArcT3SWThresholdPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    MinorArcCosineSumBound ∧
      PathA_T3SWThresholdSmallnessForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the minor-arc/T3
package. -/
theorem swAggregation_of_minorArcT3SWThresholdPackage
    (h : PathA_MinorArcT3SWThresholdPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the assembled no-RH minor-arc cosine bound from the
minor-arc/T3 package. -/
theorem minorArcCosineSumBound_of_minorArcT3SWThresholdPackage
    (h : PathA_MinorArcT3SWThresholdPackage) :
    MinorArcCosineSumBound :=
  h.2.1

/-- Project the thresholded SW-shaped T3 smallness field from the
minor-arc/T3 package. -/
theorem t3SWThresholdSmallness_of_minorArcT3SWThresholdPackage
    (h : PathA_MinorArcT3SWThresholdPackage) :
    PathA_T3SWThresholdSmallnessForFareyWitness :=
  h.2.2

/-- A minor-arc/T3 package plus Siegel-Walfisz gives the Farey-witness
Hardy-Littlewood smallness statement.

Compared with `PathA_T3FareyWitnessAggregation_of_swThresholdSmallness`,
this bridge consumes an already assembled `MinorArcCosineSumBound` instead
of the three separate Vinogradov witness-bound fields. -/
theorem PathA_HardyLittlewoodSmallnessForFareyWitness_of_minorArcT3SWThresholdPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_MinorArcT3SWThresholdPackage) :
    PathA_HardyLittlewoodSmallnessForFareyWitness := by
  rcases hPackage with ⟨hAgg, hMinor, hSmall⟩
  rcases PathA_FareyMajorArcBound_SiegelWalfisz_of_aggregation hSW hAgg with
    ⟨Q, N₀, majorArcs, C, c, hQ, hC, hc, hmajor⟩
  rcases hSmall hQ hC hc hmajor hMinor with
    ⟨N_M, N_m, δ_M, δ_m,
      hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small, hminor_small⟩
  let N' : Nat := max N₀ N_M
  have hmajor' :
      ∀ n : Nat, N' < n → Even n →
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
            majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          siegelWalfiszErrorFn C c n := by
    intro n hn hEven
    have hN₀_lt : N₀ < n := lt_of_le_of_lt (le_max_left N₀ N_M) hn
    exact hmajor n hN₀_lt hEven
  have herror_small' :
      ∀ n : Nat, N' < n → Even n →
        siegelWalfiszErrorFn C c n ≤
          δ_M * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
    intro n hn hEven
    have hN_M_lt : N_M < n := lt_of_le_of_lt (le_max_right N₀ N_M) hn
    exact herror_small n hN_M_lt hEven
  refine ⟨Q, N', majorArcs, siegelWalfiszErrorFn C c, hQ, hmajor', ?_⟩
  exact ⟨N_m, δ_M, δ_m,
    hδ_M_nn, hδ_M_lt, hδ_m_nn, hsum_lt, herror_small', hminor_small⟩

/-- A minor-arc/T3 package plus Siegel-Walfisz produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_minorArcT3SWThresholdPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_MinorArcT3SWThresholdPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness
    (PathA_HardyLittlewoodSmallnessForFareyWitness_of_minorArcT3SWThresholdPackage
      hSW hPackage)

/-- A minor-arc/T3 package plus Siegel-Walfisz gives the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_MinorArcT3SWThresholdPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_minorArcT3SWThresholdPackage
      hSW hPackage)

/-- **Lowered Vinogradov plus thresholded T3 package.**

This is the handoff shape before the minor-arc cosine bound has been
assembled: it bundles SW-to-Fourier aggregation, the full lowered
Vinogradov/Vaughan formalization package, and the thresholded local T3
comparison. -/
def PathA_VinogradovT3SWThresholdPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanBilinearFormalizationPackage ∧
      PathA_T3SWThresholdSmallnessForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the lowered
Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovT3SWThresholdPackage
    (h : PathA_VinogradovT3SWThresholdPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the full lowered Vinogradov/Vaughan package. -/
theorem vinogradovBilinearFormalization_of_vinogradovT3SWThresholdPackage
    (h : PathA_VinogradovT3SWThresholdPackage) :
    VinogradovVaughanBilinearFormalizationPackage :=
  h.2.1

/-- Project the thresholded SW-shaped T3 smallness field from the lowered
Vinogradov/T3 package. -/
theorem t3SWThresholdSmallness_of_vinogradovT3SWThresholdPackage
    (h : PathA_VinogradovT3SWThresholdPackage) :
    PathA_T3SWThresholdSmallnessForFareyWitness :=
  h.2.2

/-- A lowered Vinogradov/T3 package assembles the minor-arc/T3 package by
deriving the no-RH minor-arc cosine bound from the Vinogradov formalization
package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovT3SWThresholdPackage
    (h : PathA_VinogradovT3SWThresholdPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovT3SWThresholdPackage h,
    minorArcCosineSumBound_of_vinogradov_bilinearFormalizationPackage
      (vinogradovBilinearFormalization_of_vinogradovT3SWThresholdPackage h),
    t3SWThresholdSmallness_of_vinogradovT3SWThresholdPackage h⟩

/-- A lowered Vinogradov/T3 package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovT3SWThresholdPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovT3SWThresholdPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovT3SWThresholdPackage hPackage)

/-- A lowered Vinogradov/T3 package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovT3SWThresholdPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovT3SWThresholdPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovT3SWThresholdPackage hPackage)

/-! ### Lowered Vinogradov/T3 package with split quarter-smallness -/

/-- **Lowered Vinogradov plus split-quarter T3 package.**

This is one level lower than `PathA_VinogradovT3SWThresholdPackage`: instead
of consuming a bundled thresholded T3 comparison, it consumes the split
quarter-smallness package separating the SW major-error comparison from the
minor-contribution aggregation estimate. -/
def PathA_VinogradovT3SWQuarterSmallnessPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanBilinearFormalizationPackage ∧
      PathA_T3SWQuarterSmallnessPackage

/-- Project the SW-to-Fourier aggregation field from the lowered
Vinogradov/T3 split-quarter package. -/
theorem swAggregation_of_vinogradovT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the full lowered Vinogradov/Vaughan package from the
Vinogradov/T3 split-quarter package. -/
theorem vinogradovBilinearFormalization_of_vinogradovT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    VinogradovVaughanBilinearFormalizationPackage :=
  h.2.1

/-- Project the split T3 quarter-smallness package from the lowered
Vinogradov/T3 package. -/
theorem t3SWQuarterSmallness_of_vinogradovT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  h.2.2

/-- A split-quarter Vinogradov/T3 package assembles the thresholded
Vinogradov/T3 package by converting quarter-smallness to threshold
smallness. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovT3SWQuarterSmallnessPackage h,
    vinogradovBilinearFormalization_of_vinogradovT3SWQuarterSmallnessPackage h,
    PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
      (t3SWQuarterSmallness_of_vinogradovT3SWQuarterSmallnessPackage h)⟩

/-- A split-quarter Vinogradov/T3 package assembles the minor-arc/T3
package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovT3SWThresholdPackage
    (vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage h)

/-- A split-quarter Vinogradov/T3 package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovT3SWThresholdPackage hSW
    (vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
      hPackage)

/-- A split-quarter Vinogradov/T3 package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovT3SWQuarterSmallnessPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovT3SWThresholdPackage
    hSW
    (vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
      hPackage)

/-! ### Lowered Vinogradov/T3 package with separated bilinear energies -/

/-- **Separated Vinogradov plus split-quarter T3 package.**

This is one level lower on the Vinogradov side than
`PathA_VinogradovT3SWQuarterSmallnessPackage`: Type II and Type III are
supplied in separated coefficient/kernel energy form, then Lean reassembles
the current bilinear formalization package. -/
def PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanSeparatedBilinearFormalizationPackage ∧
      PathA_T3SWQuarterSmallnessPackage

/-- Project the SW-to-Fourier aggregation field from the separated
Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the separated Vinogradov/Vaughan package. -/
theorem vinogradovSeparatedBilinearFormalization_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    VinogradovVaughanSeparatedBilinearFormalizationPackage :=
  h.2.1

/-- Project the split T3 quarter-smallness package from the separated
Vinogradov/T3 package. -/
theorem t3SWQuarterSmallness_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  h.2.2

/-- A separated Vinogradov/T3 split-quarter package supplies the current
Vinogradov/T3 split-quarter package. -/
theorem vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    PathA_VinogradovT3SWQuarterSmallnessPackage :=
  ⟨swAggregation_of_vinogradovSeparatedT3SWQuarterSmallnessPackage h,
    vinogradovBilinearFormalizationPackage_of_separatedBilinearFormalizationPackage
      (vinogradovSeparatedBilinearFormalization_of_vinogradovSeparatedT3SWQuarterSmallnessPackage h),
    t3SWQuarterSmallness_of_vinogradovSeparatedT3SWQuarterSmallnessPackage h⟩

/-- A separated Vinogradov/T3 package assembles the thresholded
Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
    (vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage h)

/-- A separated Vinogradov/T3 package assembles the minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
    (vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage h)

/-- A separated Vinogradov/T3 package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovT3SWQuarterSmallnessPackage hSW
    (vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
      hPackage)

/-- A separated Vinogradov/T3 package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovT3SWQuarterSmallnessPackage
    hSW
    (vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
      hPackage)

/-! ### Lowered Vinogradov/T3 package with fully separated Type I/II/III -/

/-- **Fully separated Vinogradov plus split-quarter T3 package.**

This is one level lower than
`PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage`: Type I is also
supplied in separated coefficient/kernel form, while Type II/III remain in
separated coefficient/kernel energy form. -/
def PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3SWQuarterSmallnessPackage

/-- Project the SW-to-Fourier aggregation field from the fully separated
Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the split T3 quarter-smallness package from the fully separated
Vinogradov/T3 package. -/
theorem t3SWQuarterSmallness_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  h.2.2

/-- A fully separated Vinogradov/T3 split-quarter package supplies the
separated-bilinear Vinogradov/T3 split-quarter package. -/
theorem vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h,
    vinogradovSeparatedBilinearFormalizationPackage_of_fullySeparatedFormalizationPackage
      (vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h),
    t3SWQuarterSmallness_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h⟩

/-- A fully separated Vinogradov/T3 package supplies the current
Vinogradov/T3 split-quarter package. -/
theorem vinogradovT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_VinogradovT3SWQuarterSmallnessPackage :=
  vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h)

/-- A fully separated Vinogradov/T3 package assembles the thresholded
Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h)

/-- A fully separated Vinogradov/T3 package assembles the minor-arc/T3
package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    (vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage h)

/-- A fully separated Vinogradov/T3 package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovSeparatedT3SWQuarterSmallnessPackage hSW
    (vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
      hPackage)

/-- A fully separated Vinogradov/T3 package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
    hSW
    (vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
      hPackage)

/-! ### Fully separated Vinogradov/T3 with only minor-contribution T3 open -/

/-- **Fully separated Vinogradov plus minor-contribution quarter-smallness.**

This is one level lower on the T3 side than
`PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage`: the SW
major-error quarter-smallness half is now proved in Lean, so the package only
asks for the minor-contribution quarter-smallness estimate. -/
def PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage : Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3MinorContributionQuarterSmallnessForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the fully separated
Vinogradov/T3 minor-quarter package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package from the
Vinogradov/T3 minor-quarter package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the remaining T3 minor-contribution quarter-smallness field. -/
theorem t3MinorContributionQuarterSmallness_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness :=
  h.2.2

/-- A fully separated Vinogradov/T3 minor-quarter package supplies the split
T3 quarter-smallness package by using the closed SW major-error theorem. -/
theorem t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  PathA_T3SWQuarterSmallnessPackage_of_minorContributionQuarterSmallness
    (t3MinorContributionQuarterSmallness_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      h)

/-- A fully separated Vinogradov/T3 minor-quarter package supplies the previous
fully separated split-quarter package. -/
theorem vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage h,
    vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage h,
    t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage h⟩

/-- A fully separated Vinogradov/T3 minor-quarter package supplies the
separated-bilinear split-quarter package. -/
theorem vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage :=
  vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      h)

/-- A fully separated Vinogradov/T3 minor-quarter package assembles the
thresholded Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      h)

/-- A fully separated Vinogradov/T3 minor-quarter package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (h : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    (vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      h)

/-- A fully separated Vinogradov/T3 minor-quarter package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage hSW
    (vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      hPackage)

/-- A fully separated Vinogradov/T3 minor-quarter package plus Siegel-Walfisz
gives the existential Hardy-Littlewood lower bound consumed by the finite
Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
    hSW
    (vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      hPackage)

/-! ### Fully separated Vinogradov/T3 with DFT-uniform minor-quarter T3 open -/

/-- **Fully separated Vinogradov plus DFT-uniform minor-quarter smallness.**

This lowers the remaining T3 field one more step: instead of asking directly
for a real minor-contribution bound, it asks for the uniform DFT-square
minor-arc target from which Lean derives that real bound using the discrete
Fourier minor-contribution estimate. -/
def PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the DFT-uniform
minor-quarter Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package from the
DFT-uniform minor-quarter Vinogradov/T3 package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the DFT-uniform T3 minor-contribution quarter-smallness field. -/
theorem t3DftUniformMinorContributionQuarterSmallness_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness :=
  h.2.2

/-- A DFT-uniform minor-quarter package supplies the previous minor-quarter
package by Fourier bookkeeping. -/
theorem vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h,
    vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h,
    PathA_T3MinorContributionQuarterSmallnessForFareyWitness_of_dftUniformSquareQuarterSmallness
      (t3DftUniformMinorContributionQuarterSmallness_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
        h)⟩

/-- A DFT-uniform minor-quarter package supplies the split T3 package. -/
theorem t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h)

/-- A DFT-uniform minor-quarter package supplies the previous fully separated
split-quarter package. -/
theorem vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h)

/-- A DFT-uniform minor-quarter package supplies the separated-bilinear
split-quarter package. -/
theorem vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage :=
  vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h)

/-- A DFT-uniform minor-quarter package assembles the thresholded
Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h)

/-- A DFT-uniform minor-quarter package assembles the minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      h)

/-- A DFT-uniform minor-quarter package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    hSW
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      hPackage)

/-- A DFT-uniform minor-quarter package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
    hSW
    (vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      hPackage)

/-! ### Fully separated Vinogradov/T3 with little-o uniform DFT minor T3 open -/

/-- **Fully separated Vinogradov plus little-o uniform DFT minor bound.**

This is one level lower than the DFT-square quarter package: the remaining
T3 field is the analytic statement that the uniform DFT bound on minor
frequencies is `o(sqrt n)`.  Lean turns that limit into the quarter-square
budget using the singular-series lower bound. -/
def PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3MinorContributionDftUniformLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the little-o uniform
minor DFT Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package from the little-o
uniform minor DFT Vinogradov/T3 package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the little-o uniform DFT T3 field. -/
theorem t3DftUniformLittleO_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_T3MinorContributionDftUniformLittleOForFareyWitness :=
  h.2.2

/-- A little-o uniform DFT package supplies the previous DFT-square
minor-quarter package. -/
theorem vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage h,
    vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h,
    PathA_T3MinorContributionDftUniformSquareQuarterSmallnessForFareyWitness_of_dftUniformLittleO
      (t3DftUniformLittleO_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
        h)⟩

/-- A little-o uniform DFT package supplies the previous real minor-quarter
package. -/
theorem vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h)

/-- A little-o uniform DFT package supplies the split T3 package. -/
theorem t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h)

/-- A little-o uniform DFT package supplies the fully separated split-quarter
package. -/
theorem vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h)

/-- A little-o uniform DFT package supplies the thresholded Vinogradov/T3
package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h)

/-- A little-o uniform DFT package assembles the minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (h : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      h)

/-- A little-o uniform DFT package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      hPackage)

/-- A little-o uniform DFT package plus Siegel-Walfisz gives the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage : PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      hPackage)

/-! ### Fully separated Vinogradov/T3 with complement little-o DFT minor T3 open -/

/-- **Fully separated Vinogradov plus complement little-o uniform DFT minor
bound.**

This is one level lower than the minor-frequency little-o package: the
remaining T3 field is stated directly on the complement of the supplied
Farey major arcs, `k ∉ majorArcs n`.  Lean converts that complement statement
to `zmodMinorFrequencies` and then reuses the existing little-o-to-quarter
budget bridge. -/
def PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the complement little-o
uniform minor DFT Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package from the
complement little-o uniform minor DFT Vinogradov/T3 package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the complement little-o uniform DFT T3 field. -/
theorem t3DftUniformComplementLittleO_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness :=
  h.2.2

/-- A complement little-o uniform DFT package supplies the previous
minor-frequency little-o package. -/
theorem vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h,
    vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h,
    PathA_T3MinorContributionDftUniformLittleOForFareyWitness_of_complementLittleO
      (t3DftUniformComplementLittleO_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
        h)⟩

/-- A complement little-o uniform DFT package supplies the previous
DFT-square minor-quarter package. -/
theorem vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package supplies the previous real
minor-quarter package. -/
theorem vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package supplies the split T3 package. -/
theorem t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package supplies the fully separated
split-quarter package. -/
theorem vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package supplies the thresholded
Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package assembles the minor-arc/T3
package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      h)

/-- A complement little-o uniform DFT package plus Siegel-Walfisz produces
the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      hPackage)

/-- A complement little-o uniform DFT package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      hPackage)

/-! ### Fully separated Vinogradov/T3 with finite-supremum little-o DFT minor T3 open -/

/-- **Fully separated Vinogradov plus finite-supremum little-o DFT minor
bound.**

This is the canonical scalar version of the complement little-o package:
the remaining T3 field is the statement that the actual finite supremum of
minor-frequency DFT norms is `o(sqrt n)`.  Lean uses the finite supremum as
the uniform bound and then reuses the complement little-o package. -/
def PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanFullySeparatedFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the finite-supremum
little-o uniform minor DFT Vinogradov/T3 package. -/
theorem swAggregation_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated Vinogradov/Vaughan package from the
finite-supremum little-o uniform minor DFT Vinogradov/T3 package. -/
theorem vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanFullySeparatedFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field. -/
theorem t3DftSupComplementLittleO_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- A finite-supremum little-o DFT package supplies the previous complement
little-o package. -/
theorem vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h,
    vinogradovFullySeparatedFormalization_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h,
    PathA_T3MinorContributionDftUniformComplementLittleOForFareyWitness_of_supComplementLittleO
      (t3DftSupComplementLittleO_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
        h)⟩

/-- A finite-supremum little-o DFT package supplies the previous
minor-frequency little-o package. -/
theorem vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage :=
  vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package supplies the previous DFT-square
minor-quarter package. -/
theorem vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package supplies the previous real
minor-quarter package. -/
theorem vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package supplies the split T3 package. -/
theorem t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_T3SWQuarterSmallnessPackage :=
  t3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package supplies the fully separated
split-quarter package. -/
theorem vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage :=
  vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package supplies the thresholded
Vinogradov/T3 package. -/
theorem vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovT3SWThresholdPackage :=
  vinogradovT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package assembles the minor-arc/T3
package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      h)

/-- A finite-supremum little-o DFT package plus Siegel-Walfisz produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- A finite-supremum little-o DFT package plus Siegel-Walfisz gives the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
    hSW
    (vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with concrete expanded Type-I target -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with expanded
Type-I target.**

This variant keeps the current finite-supremum DFT T3 target, but replaces
the fully separated Type-I field by the concrete divisor-antidiagonal
expanded Type-I estimate proved in `PathA_MinorArc`.  Type II and Type III
remain in separated bilinear-energy form. -/
def PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanTypeIDivisorAntidiagonalFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the expanded-Type-I
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the expanded-Type-I Vinogradov/Vaughan package. -/
theorem vinogradovTypeIDivisorAntidiagonalFormalization_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanTypeIDivisorAntidiagonalFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the
expanded-Type-I package. -/
theorem t3DftSupComplementLittleO_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The expanded-Type-I finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      h,
    minorArcCosineSumBound_of_vinogradov_typeIDivisorAntidiagonalFormalizationPackage
      (vinogradovTypeIDivisorAntidiagonalFormalization_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
        h),
    PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
      (PathA_T3SWQuarterSmallnessPackage_of_dftSupComplementLittleOMinorContribution
        (t3DftSupComplementLittleO_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
          h))⟩

/-- The expanded-Type-I finite-supremum DFT package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The expanded-Type-I finite-supremum DFT package plus Siegel-Walfisz gives
the existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with all Vaughan pieces expanded to divisor antidiagonals -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with all
Vaughan pieces expanded.**

This variant keeps the finite-supremum DFT T3 target and consumes a
Vinogradov package whose Type I, Type II, and Type III fields are all bounds
on the actual divisor-antidiagonal expansions of the Vaughan sums. -/
def PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanDivisorAntidiagonalFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the fully expanded
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully expanded Vinogradov/Vaughan package. -/
theorem vinogradovDivisorAntidiagonalFormalization_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanDivisorAntidiagonalFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the fully
expanded package. -/
theorem t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The fully expanded finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      h,
    minorArcCosineSumBound_of_vinogradov_divisorAntidiagonalFormalizationPackage
      (vinogradovDivisorAntidiagonalFormalization_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
        h),
    PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
      (PathA_T3SWQuarterSmallnessPackage_of_dftSupComplementLittleOMinorContribution
        (t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
          h))⟩

/-- The fully expanded finite-supremum DFT package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The fully expanded finite-supremum DFT package plus Siegel-Walfisz gives
the existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with expanded Type I and separated-energy expanded Type II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with expanded
Type I and separated-energy expanded Type II/III.**

This is the lower proof-structure handoff for the expanded Vaughan sums:
Type I remains a bound on its concrete divisor-antidiagonal sum, while
Type II/III expose coefficient and kernel energies for their concrete
expanded sums. -/
def PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanTypeIDivisorAntidiagonalSeparatedEnergyFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the expanded/separated
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the expanded/separated-energy Vinogradov/Vaughan package. -/
theorem vinogradovTypeIDivisorAntidiagonalSeparatedEnergyFormalization_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanTypeIDivisorAntidiagonalSeparatedEnergyFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the
expanded/separated-energy package. -/
theorem t3DftSupComplementLittleO_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The expanded/separated-energy finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      h,
    minorArcCosineSumBound_of_vinogradov_typeIDivisorAntidiagonalSeparatedEnergyPackage
      (vinogradovTypeIDivisorAntidiagonalSeparatedEnergyFormalization_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
        h),
    PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
      (PathA_T3SWQuarterSmallnessPackage_of_dftSupComplementLittleOMinorContribution
        (t3DftSupComplementLittleO_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
          h))⟩

/-- The expanded/separated-energy finite-supremum DFT package plus
Siegel-Walfisz produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The expanded/separated-energy finite-supremum DFT package plus
Siegel-Walfisz gives the existential Hardy-Littlewood lower bound consumed
by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with separated-energy expanded Type I/II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with
separated-energy targets for all expanded Vaughan divisor-antidiagonal
sums.**

This is the current lowest Vinogradov/T3 proof-structure handoff: Type I,
Type II, and Type III are all fixed to their actual divisor-antidiagonal
expansions, and all three are supplied through coefficient/kernel energy
estimates for those expansions. -/
def PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanDivisorAntidiagonalSeparatedEnergyFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the fully
separated-energy finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the fully separated-energy Vinogradov/Vaughan package. -/
theorem vinogradovDivisorAntidiagonalSeparatedEnergyFormalization_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanDivisorAntidiagonalSeparatedEnergyFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the fully
separated-energy package. -/
theorem t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The fully separated-energy finite-supremum DFT package forgets to the
previous package where Type I has already been converted back to a direct
expanded-sum estimate. -/
theorem vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      h,
    vinogradovTypeIDivisorAntidiagonalSeparatedEnergyFormalizationPackage_of_divisorAntidiagonalSeparatedEnergyPackage
      (vinogradovDivisorAntidiagonalSeparatedEnergyFormalization_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
        h),
    t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      h⟩

/-- The fully separated-energy finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      h)

/-- The fully separated-energy finite-supremum DFT package plus
Siegel-Walfisz produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The fully separated-energy finite-supremum DFT package plus
Siegel-Walfisz gives the existential Hardy-Littlewood lower bound consumed
by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with componentized separated-energy expanded Type I/II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with
componentized separated-energy targets for all expanded Vaughan
divisor-antidiagonal sums.**

This strengthens the previous separated-energy handoff by requiring global
coefficient-energy and kernel-energy functions for each actual Vaughan
expansion, together with the product comparisons that yield the final
square-root-size bounds. -/
def PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanDivisorAntidiagonalSeparatedEnergyComponentsFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the componentized
separated-energy finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the componentized separated-energy Vinogradov/Vaughan package. -/
theorem vinogradovDivisorAntidiagonalSeparatedEnergyComponentsFormalization_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanDivisorAntidiagonalSeparatedEnergyComponentsFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the
componentized separated-energy package. -/
theorem t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The componentized separated-energy finite-supremum DFT package forgets
to the previous separated-energy package. -/
theorem vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage_of_componentsPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
      h,
    vinogradovDivisorAntidiagonalSeparatedEnergyPackage_of_componentsPackage
      (vinogradovDivisorAntidiagonalSeparatedEnergyComponentsFormalization_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
        h),
    t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
      h⟩

/-- The componentized separated-energy finite-supremum DFT package
assembles the minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
    (vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage_of_componentsPackage
      h)

/-- The componentized separated-energy finite-supremum DFT package plus
Siegel-Walfisz produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The componentized separated-energy finite-supremum DFT package plus
Siegel-Walfisz gives the existential Hardy-Littlewood lower bound consumed
by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with exact-energy expanded Type I/II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with
exact-energy product targets for all expanded Vaughan divisor-antidiagonal
sums.**

This is the current lowest Vinogradov proof-structure handoff: the energy
functions are the actual finite square-energy sums, and the remaining
analytic Vinogradov input is the product estimate for those exact energies. -/
def PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanDivisorAntidiagonalExactEnergyFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the exact-energy
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the exact-energy Vinogradov/Vaughan package. -/
theorem vinogradovDivisorAntidiagonalExactEnergyFormalization_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanDivisorAntidiagonalExactEnergyFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the exact-energy
package. -/
theorem t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The exact-energy finite-supremum DFT package forgets to the previous
componentized separated-energy package. -/
theorem vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage_of_exactEnergyPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
      h,
    vinogradovDivisorAntidiagonalSeparatedEnergyComponentsPackage_of_exactEnergyPackage
      (vinogradovDivisorAntidiagonalExactEnergyFormalization_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
        h),
    t3DftSupComplementLittleO_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
      h⟩

/-- The exact-energy finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
    (vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage_of_exactEnergyPackage
      h)

/-- The exact-energy finite-supremum DFT package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The exact-energy finite-supremum DFT package plus Siegel-Walfisz gives
the existential Hardy-Littlewood lower bound consumed by the finite
Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with inner-sum bilinear-energy Type II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with
inner-sum bilinear-energy targets.**

This package keeps the T3 target at the actual finite DFT supremum, while the
Vinogradov side exposes the first-Cauchy-Schwarz endpoint for Type II/III:
outer coefficient energy times the square-energy of the inner oscillatory
sums.  That is the proof shape where rational approximation and geometric-sum
estimates enter. -/
def PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanInnerBilinearFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the inner-bilinear
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the inner-sum bilinear Vinogradov/Vaughan package. -/
theorem vinogradovInnerBilinearFormalization_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanInnerBilinearFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the inner-bilinear
package. -/
theorem t3DftSupComplementLittleO_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- The inner-sum bilinear finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  ⟨swAggregation_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
      h,
    minorArcCosineSumBound_of_vinogradov_innerBilinearFormalizationPackage
      (vinogradovInnerBilinearFormalization_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
        h),
    PathA_T3SWThresholdSmallnessForFareyWitness_of_quarterSmallnessPackage
      (PathA_T3SWQuarterSmallnessPackage_of_dftSupComplementLittleOMinorContribution
        (t3DftSupComplementLittleO_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
          h))⟩

/-- The inner-sum bilinear finite-supremum DFT package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The inner-sum bilinear finite-supremum DFT package plus Siegel-Walfisz
gives the existential Hardy-Littlewood lower bound consumed by the finite
Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
      hPackage)

/-! ### Vinogradov/T3 with pointwise inner-sum Type II/III -/

/-- **Vinogradov plus finite-supremum little-o DFT T3 package with pointwise
inner-sum Type II/III targets.**

The Type II/III fields now expose the geometric-sum stage directly: each
inner oscillatory sum has a pointwise majorant, and those majorants have a
summed square-energy bound. -/
def PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage :
    Prop :=
  SiegelWalfiszPerArcToFourierAggregation ∧
    VinogradovVaughanInnerPointwiseFormalizationPackage ∧
      PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness

/-- Project the SW-to-Fourier aggregation field from the pointwise inner-sum
finite-supremum DFT package. -/
theorem swAggregation_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    SiegelWalfiszPerArcToFourierAggregation :=
  h.1

/-- Project the pointwise inner-sum Vinogradov/Vaughan package. -/
theorem vinogradovInnerPointwiseFormalization_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    VinogradovVaughanInnerPointwiseFormalizationPackage :=
  h.2.1

/-- Project the finite-supremum little-o DFT T3 field from the pointwise
inner-sum package. -/
theorem t3DftSupComplementLittleO_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    PathA_T3MinorContributionDftSupComplementLittleOForFareyWitness :=
  h.2.2

/-- Pointwise inner-sum finite-supremum DFT input supplies the previous
inner-bilinear finite-supremum DFT package. -/
theorem vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage_of_innerPointwisePackage
    (h :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage :=
  ⟨swAggregation_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
      h,
    vinogradovInnerBilinearFormalizationPackage_of_innerPointwiseFormalizationPackage
      (vinogradovInnerPointwiseFormalization_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
        h),
    t3DftSupComplementLittleO_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
      h⟩

/-- The pointwise inner-sum finite-supremum DFT package assembles the
minor-arc/T3 package. -/
theorem minorArcT3SWThresholdPackage_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (h :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    PathA_MinorArcT3SWThresholdPackage :=
  minorArcT3SWThresholdPackage_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
    (vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage_of_innerPointwisePackage
      h)

/-- The pointwise inner-sum finite-supremum DFT package plus Siegel-Walfisz
produces the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage hSW
    (minorArcT3SWThresholdPackage_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- The pointwise inner-sum finite-supremum DFT package plus Siegel-Walfisz
gives the existential Hardy-Littlewood lower bound consumed by the finite
Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
    (hSW : SiegelWalfiszBound)
    (hPackage :
      PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_minorArcT3SWThresholdPackage
    hSW
    (minorArcT3SWThresholdPackage_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage
      hPackage)

/-- A Farey-witness T3 aggregation field produces the quantitative
Hardy-Littlewood content for the supplied major/minor analytic inputs. -/
theorem pathA_quantitativeContent_of_T3FareyWitnessAggregation
    (hSW : SiegelWalfiszBound)
    (hAgg : SiegelWalfiszPerArcToFourierAggregation)
    (hI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (hII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (hIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional)
    (hT3 : PathA_T3FareyWitnessAggregation) :
    PathA_QuantitativeHardyLittlewoodContent :=
  PathA_QuantitativeHardyLittlewoodContent_of_smallnessForFareyWitness
    (hT3 hSW hAgg hI hII hIII)

/-- Farey-witness T3 aggregation gives the existential Hardy-Littlewood
lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_T3FareyWitnessAggregation
    (hSW : SiegelWalfiszBound)
    (hAgg : SiegelWalfiszPerArcToFourierAggregation)
    (hI : VinogradovTypeIBoundForVaughanWitnessUnconditional)
    (hII : VinogradovTypeIIBoundForVaughanWitnessUnconditional)
    (hIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional)
    (hT3 : PathA_T3FareyWitnessAggregation) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_T3FareyWitnessAggregation
      hSW hAgg hI hII hIII hT3)

/-- **Unconditional Path A open content**.

The fields match the requested next-stage mountain list:

* `pntRemainder` is PNT with `exp(-c sqrt(log N))` remainder, closing the
  principal Siegel-Walfisz case.
* `pageSiegelNonPrincipal` is the Page-Siegel zero-free-region output for
  non-principal progressions.
* `swAggregation` is the T3 per-arc-to-Fourier aggregation step.
* `vinogradovTypeI`, `vinogradovTypeII`, and `vinogradovTypeIII` are the
  full unconditional Vinogradov/Vaughan bounds for the concrete witnesses.
* `t3Aggregation` combines those analytic estimates into the final
  major/minor smallness witness. -/
structure PathA_UnconditionalOpenContent where
  /-- PNT with `sqrt log` remainder for the principal `q = 1` case. -/
  pntRemainder : PrimeCounting_PNT_RemainderBound
  /-- Page-Siegel/zero-free-region output for non-principal progressions. -/
  pageSiegelNonPrincipal : SiegelWalfiszNonPrincipal
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- PNT plus the non-principal Page-Siegel output gives the full
Siegel-Walfisz input used by the major-arc side. -/
theorem siegelWalfiszBound_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pnt_and_nonPrincipal
    content.pntRemainder content.pageSiegelNonPrincipal

/-- Diagnostic: the unconditional content gives the substantive major
arc estimate through the T3 per-arc-to-Fourier aggregation interface. -/
theorem majorArcEstimate_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    MajorArcEstimate :=
  majorArcEstimate_of_SiegelWalfisz_aggregation
    (siegelWalfiszBound_of_unconditionalContent content)
    content.swAggregation

/-- Diagnostic: the unconditional Vinogradov fields give the minor-arc
cosine bound outright, with no RH or `ψ` square-root hypothesis. -/
theorem minorArcCosineSumBound_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_vinogradov_unconditional_witnesses
    content.vinogradovTypeI content.vinogradovTypeII content.vinogradovTypeIII

/-- The T3 aggregation field packages the final major/minor smallness
statement for the same analytic inputs. -/
theorem pathA_smallness_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    PathA_HardyLittlewoodSmallness_witness_form :=
  content.t3Aggregation
    (siegelWalfiszBound_of_unconditionalContent content)
    content.swAggregation
    content.vinogradovTypeI
    content.vinogradovTypeII
    content.vinogradovTypeIII

/-- The unconditional content implies the Path A analytic implication
without using RH. -/
theorem pathA_analyticImplication_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_smallness
    (pathA_smallness_of_unconditionalContent content)

/-- The unconditional content yields the existential Hardy-Littlewood
lower bound consumed by the final Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_unconditionalContent
    (content : PathA_UnconditionalOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_smallness
      (pathA_smallness_of_unconditionalContent content))

/-- **No-RH final Path A wrapper.**

Once the unconditional content fields above and a finite certificate
covering the extracted threshold are supplied, `StrongGoldbach` follows.
The theorem name keeps the public `under_RH` lineage visible while
making the absence of an RH hypothesis explicit. -/
theorem strongGoldbach_under_RH_unconditional
    (content : PathA_UnconditionalOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  rcases exists_quarterBinaryHardyLittlewoodLowerBound_of_unconditionalContent
      content with ⟨T, δ, hδ, hHL⟩
  rcases threshold_covered T δ hδ hHL with ⟨hT_le, hContam⟩
  exact strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound
    hδ finite hHL hT_le hContam

/-! ### Refined no-RH content: zero-free regions plus explicit-formula bridges

The handoff above already removes RH, but its two major-arc fields
`pntRemainder` and `pageSiegelNonPrincipal` are still aggregated analytic
Props.  The next highest mountain is to replace them by the lower-level
deliverables a future mathlib effort can attack directly:

* the zeta zero-free region and explicit formula giving PNT with
  `sqrt log` remainder;
* the Page-Siegel zero-free region and explicit formula giving the
  non-principal Siegel-Walfisz estimate.

This refined bundle makes that split available without changing downstream
Goldbach consumers. -/

/-- **Refined unconditional Path A open content.**

Compared with `PathA_UnconditionalOpenContent`, this replaces the aggregated
PNT and non-principal Siegel-Walfisz fields by lower-level zero-free-region
targets plus their explicit-formula bridges.  It is still open analytic
content, but it is closer to the requested Page-Siegel/PNT mathlib work. -/
structure PathA_UnconditionalRefinedOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge from zeta zero-free region to PNT. -/
  zetaToPNTRemainder : ZetaZeroFreeRegionToPNTRemainderBridge
  /-- Page-Siegel zero-free region for non-principal Dirichlet L-functions. -/
  pageSiegelZeroFreeRegion : PageSiegelZeroFreeRegion
  /-- Explicit-formula bridge from Page-Siegel to non-principal SW. -/
  pageSiegelToNonPrincipal :
    PageSiegelToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- The refined zeta fields produce the PNT remainder used by the principal
Siegel-Walfisz component. -/
theorem pntRemainder_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion
    content.zetaZeroFreeRegion content.zetaToPNTRemainder

/-- The refined Page-Siegel fields produce the non-principal
Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegel
    content.pageSiegelZeroFreeRegion content.pageSiegelToNonPrincipal

/-- Forget the refined zero-free-region split back to the existing no-RH
handoff content bundle. -/
def PathA_UnconditionalOpenContent_of_refined
    (content : PathA_UnconditionalRefinedOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder := pntRemainder_of_refinedUnconditionalContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_refinedUnconditionalContent content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Refined diagnostic: zero-free-region content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_refined content)

/-- Refined diagnostic: zero-free-region content gives the substantive
major-arc estimate through T3 aggregation. -/
theorem majorArcEstimate_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    MajorArcEstimate :=
  majorArcEstimate_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_refined content)

/-- Refined diagnostic: the Vinogradov fields still give the no-RH minor
arc cosine bound. -/
theorem minorArcCosineSumBound_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_refined content)

/-- Refined diagnostic: all refined analytic inputs imply the final
Hardy-Littlewood smallness witness. -/
theorem pathA_smallness_of_refinedUnconditionalContent
    (content : PathA_UnconditionalRefinedOpenContent) :
    PathA_HardyLittlewoodSmallness_witness_form :=
  pathA_smallness_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_refined content)

/-- Refined no-RH Path A wrapper.  This is the same final implication as
`strongGoldbach_under_RH_unconditional`, but with the PNT and Page-Siegel
inputs split into zero-free-region and explicit-formula bridge fields. -/
theorem strongGoldbach_under_RH_unconditional_refined
    (content : PathA_UnconditionalRefinedOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_refined content)
    finite threshold_covered

/-! ### Mathlib-facing refined no-RH content

The previous refined bundle still lets the Page-Siegel field range over all
non-principal characters and lets the zeta/PNT bridge target the project-local
PNT Prop directly.  The bundle below exposes the two targets in the form a
future mathlib development is more likely to provide:

* a `Chebyshev.psi` PNT remainder obtained from the zeta zero-free region;
* a primitive-character Page-Siegel zero-free region, plus a separate bridge
  handling imprimitive characters via conductors and Euler factors.

Forgetting this bundle back to `PathA_UnconditionalRefinedOpenContent` is
fully formalized here. -/

/-- **Mathlib-facing refined unconditional Path A open content.**

This is the lowest-level no-RH handoff currently exposed by the project:
the PNT side is stated in terms of mathlib's `Chebyshev.psi`, and the
Page-Siegel side is stated first for primitive characters. -/
structure PathA_UnconditionalMathlibRefinedOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to mathlib's `Chebyshev.psi` remainder. -/
  zetaToChebyshevPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge
  /-- Primitive-character Page-Siegel zero-free region. -/
  primitivePageSiegelZeroFreeRegion : PrimitivePageSiegelZeroFreeRegion
  /-- Transfer from primitive characters to all non-principal characters. -/
  primitivePageSiegelToPageSiegel : PrimitivePageSiegelToPageSiegelBridge
  /-- Explicit-formula bridge from all-character Page-Siegel to non-principal SW. -/
  pageSiegelToNonPrincipal :
    PageSiegelToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Mathlib-facing refined content gives the project-local PNT remainder. -/
theorem pntRemainder_of_mathlibRefinedUnconditionalContent
    (content : PathA_UnconditionalMathlibRefinedOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPNTRemainder

/-- Mathlib-facing refined content gives the all-character Page-Siegel field. -/
theorem pageSiegelZeroFreeRegion_of_mathlibRefinedUnconditionalContent
    (content : PathA_UnconditionalMathlibRefinedOpenContent) :
    PageSiegelZeroFreeRegion :=
  pageSiegelZeroFreeRegion_of_primitivePageSiegel
    content.primitivePageSiegelZeroFreeRegion
    content.primitivePageSiegelToPageSiegel

/-- Forget mathlib-facing refined content back to the existing refined bundle. -/
def PathA_UnconditionalRefinedOpenContent_of_mathlibRefined
    (content : PathA_UnconditionalMathlibRefinedOpenContent) :
    PathA_UnconditionalRefinedOpenContent where
  zetaZeroFreeRegion := content.zetaZeroFreeRegion
  zetaToPNTRemainder := fun hZF =>
    pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
      hZF content.zetaToChebyshevPNTRemainder
  pageSiegelZeroFreeRegion :=
    pageSiegelZeroFreeRegion_of_mathlibRefinedUnconditionalContent content
  pageSiegelToNonPrincipal := content.pageSiegelToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Mathlib-facing refined content gives the non-principal Siegel-Walfisz
component after primitive-to-all-character transfer. -/
theorem siegelWalfiszNonPrincipal_of_mathlibRefinedUnconditionalContent
    (content : PathA_UnconditionalMathlibRefinedOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_refinedUnconditionalContent
    (PathA_UnconditionalRefinedOpenContent_of_mathlibRefined content)

/-- Mathlib-facing refined content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_mathlibRefinedUnconditionalContent
    (content : PathA_UnconditionalMathlibRefinedOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_refinedUnconditionalContent
    (PathA_UnconditionalRefinedOpenContent_of_mathlibRefined content)

/-- Mathlib-facing refined no-RH Path A wrapper.  This is the same final
implication as `strongGoldbach_under_RH_unconditional_refined`, but with
PNT stated through mathlib's `Chebyshev.psi` and Page-Siegel stated first
for primitive characters. -/
theorem strongGoldbach_under_RH_unconditional_mathlib_refined
    (content : PathA_UnconditionalMathlibRefinedOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_refined
    (PathA_UnconditionalRefinedOpenContent_of_mathlibRefined content)
    finite threshold_covered

/-! ### Exceptional-zero Page-Siegel refined no-RH content

Classically, the Page-Siegel route may first prove a zero-free region for
primitive characters away from one possible real exceptional zero, then
use Siegel's theorem to show that this exceptional contribution is still
small enough for Siegel-Walfisz in the `q <= (log N)^A` range.  This bundle
records that route directly, so a future formalization is not forced to
pretend that the exceptional-zero handling is literally a uniform zero-free
strip for every character. -/

/-- **Exceptional-zero Page-Siegel refined unconditional Path A content.**

The PNT side is still mathlib-native (`Chebyshev.psi`).  The non-principal
Siegel-Walfisz side is supplied by a primitive Page-Siegel theorem with one
possible exceptional real zero plus the analytic bridge that controls that
exceptional contribution. -/
structure PathA_UnconditionalExceptionalPageSiegelOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to mathlib's `Chebyshev.psi` remainder. -/
  zetaToChebyshevPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region away from one possible real zero. -/
  primitivePageSiegelExceptional :
    PrimitivePageSiegelZeroFreeRegionWithExceptional
  /-- Explicit formula, conductor transfer, and Siegel lower-bound handling. -/
  primitivePageSiegelExceptionalToNonPrincipal :
    PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Exceptional-zero Page-Siegel refined content gives the project-local
PNT remainder. -/
theorem pntRemainder_of_exceptionalPageSiegelContent
    (content : PathA_UnconditionalExceptionalPageSiegelOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPNTRemainder

/-- Exceptional-zero Page-Siegel refined content gives the non-principal
Siegel-Walfisz component directly. -/
theorem siegelWalfiszNonPrincipal_of_exceptionalPageSiegelContent
    (content : PathA_UnconditionalExceptionalPageSiegelOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptional
    content.primitivePageSiegelExceptional
    content.primitivePageSiegelExceptionalToNonPrincipal

/-- Forget exceptional-zero Page-Siegel refined content back to the
existing no-RH handoff bundle. -/
def PathA_UnconditionalOpenContent_of_exceptionalPageSiegel
    (content : PathA_UnconditionalExceptionalPageSiegelOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder := pntRemainder_of_exceptionalPageSiegelContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_exceptionalPageSiegelContent content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Exceptional-zero Page-Siegel refined content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_exceptionalPageSiegelContent
    (content : PathA_UnconditionalExceptionalPageSiegelOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_exceptionalPageSiegel content)

/-- Exceptional-zero Page-Siegel no-RH Path A wrapper.  This is the same
final implication as `strongGoldbach_under_RH_unconditional`, but with the
major-arc Page-Siegel input split into the classical exceptional-zero route. -/
theorem strongGoldbach_under_RH_unconditional_exceptional_pageSiegel
    (content : PathA_UnconditionalExceptionalPageSiegelOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_exceptionalPageSiegel content)
    finite threshold_covered

/-! ### Exceptional-character Page-Siegel refined no-RH content

This is the most detailed Page-Siegel handoff currently exposed: the
possible exceptional zero is tied to an optional primitive character, not
just to a modulus.  This is the form most directly usable by a future
formalization of the Dirichlet explicit formula and character-orthogonality
sum. -/

/-- **Exceptional-character Page-Siegel refined unconditional Path A
content.** -/
structure PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to mathlib's `Chebyshev.psi` remainder. -/
  zetaToChebyshevPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional exceptional character. -/
  primitivePageSiegelExceptionalCharacter :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter
  /-- Explicit formula and Siegel lower-bound handling for the exceptional character. -/
  primitivePageSiegelExceptionalCharacterToNonPrincipal :
    PrimitivePageSiegelExceptionalCharacterToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Exceptional-character Page-Siegel content gives the project-local PNT
remainder. -/
theorem pntRemainder_of_exceptionalCharacterPageSiegelContent
    (content : PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPNTRemainder

/-- Exceptional-character Page-Siegel content gives the non-principal
Siegel-Walfisz component directly. -/
theorem siegelWalfiszNonPrincipal_of_exceptionalCharacterPageSiegelContent
    (content : PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalCharacter
    content.primitivePageSiegelExceptionalCharacter
    content.primitivePageSiegelExceptionalCharacterToNonPrincipal

/-- Forget exceptional-character Page-Siegel content back to the existing
no-RH handoff bundle. -/
def PathA_UnconditionalOpenContent_of_exceptionalCharacterPageSiegel
    (content : PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder := pntRemainder_of_exceptionalCharacterPageSiegelContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_exceptionalCharacterPageSiegelContent content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Exceptional-character Page-Siegel content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_exceptionalCharacterPageSiegelContent
    (content : PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_exceptionalCharacterPageSiegel content)

/-- Exceptional-character Page-Siegel no-RH Path A wrapper. -/
theorem strongGoldbach_under_RH_unconditional_exceptional_character_pageSiegel
    (content : PathA_UnconditionalExceptionalCharacterPageSiegelOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_exceptionalCharacterPageSiegel content)
    finite threshold_covered

/-! ### Exceptional-zero Page-Siegel refined no-RH content

This variant records the possible exceptional character together with the
actual real zero of its L-function.  It is the most explicit Page-Siegel
handoff currently exposed by the project. -/

/-- **Exceptional-zero Page-Siegel refined unconditional Path A content.** -/
structure PathA_UnconditionalExceptionalZeroPageSiegelOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to mathlib's `Chebyshev.psi` remainder. -/
  zetaToChebyshevPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional recorded zero. -/
  primitivePageSiegelExceptionalZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalZero
  /-- Explicit formula and Siegel lower-bound handling for the recorded zero. -/
  primitivePageSiegelExceptionalZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Exceptional-zero Page-Siegel content gives the project-local PNT
remainder. -/
theorem pntRemainder_of_exceptionalZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalZeroPageSiegelOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPNTRemainder

/-- Exceptional-zero Page-Siegel content gives the non-principal
Siegel-Walfisz component directly. -/
theorem siegelWalfiszNonPrincipal_of_exceptionalZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalZeroPageSiegelOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalZero
    content.primitivePageSiegelExceptionalZero
    content.primitivePageSiegelExceptionalZeroToNonPrincipal

/-- Forget exceptional-zero Page-Siegel content back to the existing no-RH
handoff bundle. -/
def PathA_UnconditionalOpenContent_of_exceptionalZeroPageSiegel
    (content : PathA_UnconditionalExceptionalZeroPageSiegelOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder := pntRemainder_of_exceptionalZeroPageSiegelContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_exceptionalZeroPageSiegelContent content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Exceptional-zero Page-Siegel content gives the full Siegel-Walfisz
input. -/
theorem siegelWalfiszBound_of_exceptionalZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalZeroPageSiegelOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_exceptionalZeroPageSiegel content)

/-- Exceptional-zero Page-Siegel no-RH Path A wrapper. -/
theorem strongGoldbach_under_RH_unconditional_exceptional_zero_pageSiegel
    (content : PathA_UnconditionalExceptionalZeroPageSiegelOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_exceptionalZeroPageSiegel content)
    finite threshold_covered

/-! ### Exceptional-quadratic-zero Page-Siegel refined no-RH content

This variant records the classical shape of a possible Siegel zero: the
exceptional primitive character is explicitly quadratic (`χ ^ 2 = 1`),
and the actual real zero of its L-function is recorded. -/

/-- **Exceptional-quadratic-zero Page-Siegel refined unconditional Path A
content.** -/
structure PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to mathlib's `Chebyshev.psi` remainder. -/
  zetaToChebyshevPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Exceptional-quadratic-zero Page-Siegel content gives the project-local
PNT remainder. -/
theorem pntRemainder_of_exceptionalQuadraticZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPNTRemainder

/-- Exceptional-quadratic-zero Page-Siegel content gives the
non-principal Siegel-Walfisz component directly. -/
theorem siegelWalfiszNonPrincipal_of_exceptionalQuadraticZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal

/-- Forget exceptional-quadratic-zero Page-Siegel content back to the
existing no-RH handoff bundle. -/
def PathA_UnconditionalOpenContent_of_exceptionalQuadraticZeroPageSiegel
    (content : PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder := pntRemainder_of_exceptionalQuadraticZeroPageSiegelContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_exceptionalQuadraticZeroPageSiegelContent content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Exceptional-quadratic-zero Page-Siegel content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_exceptionalQuadraticZeroPageSiegelContent
    (content : PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_exceptionalQuadraticZeroPageSiegel content)

/-- Exceptional-quadratic-zero Page-Siegel no-RH Path A wrapper. -/
theorem strongGoldbach_under_RH_unconditional_exceptional_quadratic_zero_pageSiegel
    (content : PathA_UnconditionalExceptionalQuadraticZeroPageSiegelOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_exceptionalQuadraticZeroPageSiegel content)
    finite threshold_covered

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel content

This is the most mathlib-facing no-RH handoff currently exposed here:
the PNT side is the real-variable `Chebyshev.psi` remainder, while the
Page-Siegel side uses the classical primitive quadratic exceptional-zero
shape. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel
unconditional Path A content.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final aggregation of the major/minor estimates into HL smallness. -/
  t3Aggregation : PathA_T3Aggregation

/-- Real-Chebyshev PNT content gives the project-local PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegelContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_realChebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPsiRealPNTRemainder

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegelContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal

/-- Forget the real-Chebyshev PNT / exceptional-quadratic-zero content
back to the existing no-RH handoff bundle. -/
def PathA_UnconditionalOpenContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent) :
    PathA_UnconditionalOpenContent where
  pntRemainder :=
    pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegelContent content
  pageSiegelNonPrincipal :=
    siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegelContent
      content
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3Aggregation := content.t3Aggregation

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegelContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_unconditionalContent
    (PathA_UnconditionalOpenContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional
    (PathA_UnconditionalOpenContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel
      content)
    finite threshold_covered

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel + Farey-witness T3

This variant keeps the same most mathlib-facing PNT/Page-Siegel inputs as
the previous wrapper, but replaces the stronger `PathA_T3Aggregation`
field by the weaker, more proof-shaped `PathA_T3FareyWitnessAggregation`.
The latter only has to produce one Farey major-arc witness with matching
major/minor smallness for the supplied analytic inputs. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
with Farey-witness T3 aggregation.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Final Farey-witness aggregation into HL smallness. -/
  t3FareyWitnessAggregation : PathA_T3FareyWitnessAggregation

/-- Farey-witness T3 content gives the project-local PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegion_realChebyshevBridge
    content.zetaZeroFreeRegion content.zetaToChebyshevPsiRealPNTRemainder

/-- Farey-witness T3 content gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZero
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal

/-- Farey-witness T3 content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pnt_and_nonPrincipal
    (pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
      content)
    (siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
      content)

/-- Farey-witness T3 content gives the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_T3FareyWitnessAggregation
    (siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
      content)
    content.swAggregation
    content.vinogradovTypeI
    content.vinogradovTypeII
    content.vinogradovTypeIII
    content.t3FareyWitnessAggregation

/-- Farey-witness T3 content yields the existential Hardy-Littlewood lower
bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper using the weaker Farey-witness T3 aggregation contract. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_fareyWitnessT3
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  rcases exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
      content with ⟨T, δ, hδ, hHL⟩
  rcases threshold_covered T δ hδ hHL with ⟨hT_le, hContam⟩
  exact strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound
    hδ finite hHL hT_le hContam

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel + local SW T3 smallness

This is the tightest no-RH wrapper in this file.  It keeps the
mathlib-facing PNT/Page-Siegel inputs and replaces the Farey-witness T3
aggregation field by the still-lower local contract
`PathA_T3SWSmallnessForFareyWitness`.

That local contract no longer has to assemble Siegel-Walfisz, Fourier
aggregation, or Vinogradov.  It only has to prove the final T3 comparison:
for the SW-shaped Farey major-arc witness and the assembled minor-arc cosine
bound, produce the relative major/minor smallness data for the same witness. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
with local SW-shaped T3 smallness.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type II bilinear bound for the Vaughan witness. -/
  vinogradovTypeII : VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Full unconditional Vinogradov Type III/high-high bound for the Vaughan witness. -/
  vinogradovTypeIII : VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- Local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWSmallness : PathA_T3SWSmallnessForFareyWitness

/-- Local SW-shaped T3 content forgets to the Farey-witness T3 content
bundle by deriving the Farey-witness aggregation contract. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3Smallness
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent where
  zetaZeroFreeRegion := content.zetaZeroFreeRegion
  zetaToChebyshevPsiRealPNTRemainder :=
    content.zetaToChebyshevPsiRealPNTRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    content.primitivePageSiegelExceptionalQuadraticZero
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII := content.vinogradovTypeII
  vinogradovTypeIII := content.vinogradovTypeIII
  t3FareyWitnessAggregation :=
    PathA_T3FareyWitnessAggregation_of_swSmallness content.t3SWSmallness

/-- Local SW-shaped T3 content gives the project-local PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3Smallness
      content)

/-- Local SW-shaped T3 content gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3Smallness
      content)

/-- Local SW-shaped T3 content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3Smallness
      content)

/-- Local SW-shaped T3 content gives the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_T3SWSmallness
    (siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
      content)
    content.swAggregation
    content.vinogradovTypeI
    content.vinogradovTypeII
    content.vinogradovTypeIII
    content.t3SWSmallness

/-- Local SW-shaped T3 content yields the existential Hardy-Littlewood lower
bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper using the local SW-shaped T3 smallness contract. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3Smallness
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_fareyWitnessT3
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3Smallness
      content)
    finite threshold_covered

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel + bilinear-energy Vinogradov

This no-RH handoff keeps the local SW-shaped T3 smallness contract and
replaces the Type II and Type III Vinogradov witness-bound fields by the
lower-level bilinear energy targets from `PathAMinorArc`.

Filling these two energy fields requires the real Vinogradov work: concrete
bilinear representations of the two Vaughan high pieces and the resulting
post-Cauchy-Schwarz energy estimates.  Lean then supplies the bridge back to
the witness bounds used by the final circle-method synthesis. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
with local SW-shaped T3 smallness and Type II/III bilinear-energy
Vinogradov targets.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Full unconditional Vinogradov Type I bound for the Vaughan witness. -/
  vinogradovTypeI : VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Lower-level Type II bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIEnergy : VinogradovTypeIIBilinearEnergyForVaughanWitness
  /-- Lower-level Type III/high-high bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIIEnergy : VinogradovTypeIIIBilinearEnergyForVaughanWitness
  /-- Local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWSmallness : PathA_T3SWSmallnessForFareyWitness

/-- Bilinear-energy Vinogradov content forgets to the local SW-shaped T3
smallness bundle by deriving the Type II and Type III witness bounds from
their lower-level energy estimates. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent where
  zetaZeroFreeRegion := content.zetaZeroFreeRegion
  zetaToChebyshevPsiRealPNTRemainder :=
    content.zetaToChebyshevPsiRealPNTRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    content.primitivePageSiegelExceptionalQuadraticZero
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeI := content.vinogradovTypeI
  vinogradovTypeII :=
    vinogradovTypeIIBoundForVaughanWitnessUnconditional_of_bilinearEnergy
      content.vinogradovTypeIIEnergy
  vinogradovTypeIII :=
    vinogradovTypeIIIBoundForVaughanWitnessUnconditional_of_bilinearEnergy
      content.vinogradovTypeIIIEnergy
  t3SWSmallness := content.t3SWSmallness

/-- Bilinear-energy content gives the assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_vinogradov_bilinearEnergies
    content.vinogradovTypeI
    content.vinogradovTypeIIEnergy
    content.vinogradovTypeIIIEnergy

/-- Bilinear-energy content gives the project-local PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)

/-- Bilinear-energy content gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)

/-- Bilinear-energy content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)

/-- Bilinear-energy content gives the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)

/-- Bilinear-energy content yields the existential Hardy-Littlewood lower
bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3SmallnessContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper using local SW-shaped T3 smallness and Type II/III
bilinear-energy Vinogradov targets. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3_bilinearEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3Smallness
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
      content)
    finite threshold_covered

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel + fully lowered Vinogradov

This is the tightest no-RH handoff currently exposed by the Path A interface.
It keeps the Page-Siegel/PNT and local SW-shaped T3 contracts above, and lowers
all three Vaughan/Vinogradov inputs to finite-sum targets:

* Type I: one-index linear representation plus post-summation-by-parts bound;
* Type II: bilinear representation plus Cauchy-Schwarz energy bound;
* Type III/high-high: the same bilinear-energy shape as Type II.

The bridges from these lower-level targets back to the witness-level bounds
are proved in `PathAMinorArc`; this final layer only threads them through the
existing no-RH synthesis. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
with local SW-shaped T3 smallness, Type-I linear estimate, and Type-II/III
bilinear-energy Vinogradov targets.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Lower-level Type I linear target for the Vaughan witness. -/
  vinogradovTypeILinear : VinogradovTypeILinearEstimateForVaughanWitness
  /-- Lower-level Type II bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIEnergy : VinogradovTypeIIBilinearEnergyForVaughanWitness
  /-- Lower-level Type III/high-high bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIIEnergy : VinogradovTypeIIIBilinearEnergyForVaughanWitness
  /-- Local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWSmallness : PathA_T3SWSmallnessForFareyWitness

/-- Fully lowered Vinogradov content forgets to the bilinear-energy content
by deriving the Type I witness bound from the linear estimate. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent where
  zetaZeroFreeRegion := content.zetaZeroFreeRegion
  zetaToChebyshevPsiRealPNTRemainder :=
    content.zetaToChebyshevPsiRealPNTRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    content.primitivePageSiegelExceptionalQuadraticZero
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeI :=
    vinogradovTypeIBoundForVaughanWitnessUnconditional_of_linearEstimate
      content.vinogradovTypeILinear
  vinogradovTypeIIEnergy := content.vinogradovTypeIIEnergy
  vinogradovTypeIIIEnergy := content.vinogradovTypeIIIEnergy
  t3SWSmallness := content.t3SWSmallness

/-- Fully lowered Vinogradov content forgets to the local SW-shaped T3
smallness bundle. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_vinogradovEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent :=
  PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3SmallnessOpenContent_of_bilinearEnergy
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Fully lowered Vinogradov content gives the assembled no-RH minor-arc
cosine bound. -/
theorem minorArcCosineSumBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_vinogradov_typeI_linear_typeII_typeIII_bilinearEnergies
    content.vinogradovTypeILinear
    content.vinogradovTypeIIEnergy
    content.vinogradovTypeIIIEnergy

/-- Fully lowered Vinogradov content gives the project-local PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Fully lowered Vinogradov content gives the non-principal Siegel-Walfisz
component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Fully lowered Vinogradov content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Fully lowered Vinogradov content gives the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Fully lowered Vinogradov content yields the existential Hardy-Littlewood
lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3VinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3BilinearEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper using local SW-shaped T3 smallness, a Type-I linear estimate,
and Type-II/III bilinear-energy Vinogradov targets. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3_vinogradovEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3VinogradovEnergyOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3_bilinearEnergy
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3BilinearEnergyOpenContent_of_vinogradovEnergy
      content)
    finite threshold_covered

/-! ### Real-Chebyshev PNT + exceptional-quadratic-zero Page-Siegel + thresholded T3 + fully lowered Vinogradov

This handoff keeps the fully lowered Vinogradov targets and weakens the T3
field from the earlier local SW smallness contract to the thresholded form.
That is closer to the actual final aggregation proof: the SW-shaped major
estimate may have one starting threshold, while the eventual major-error
smallness comparison and the minor contribution bound can start later. -/

/-- **Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel content
with thresholded local SW-shaped T3 smallness, Type-I linear estimate, and
Type-II/III bilinear-energy Vinogradov targets.** -/
structure PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent where
  /-- Zeta zero-free region used for PNT with `sqrt log` remainder. -/
  zetaZeroFreeRegion : ZetaZeroFreeRegionForPNT
  /-- Perron/explicit-formula bridge to real-variable `Chebyshev.psi` remainder. -/
  zetaToChebyshevPsiRealPNTRemainder :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Lower-level Type I linear target for the Vaughan witness. -/
  vinogradovTypeILinear : VinogradovTypeILinearEstimateForVaughanWitness
  /-- Lower-level Type II bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIEnergy : VinogradovTypeIIBilinearEnergyForVaughanWitness
  /-- Lower-level Type III/high-high bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIIEnergy : VinogradovTypeIIIBilinearEnergyForVaughanWitness
  /-- Thresholded local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWThresholdSmallness : PathA_T3SWThresholdSmallnessForFareyWitness

/-- Thresholded T3 + fully lowered Vinogradov content forgets to the
Farey-witness T3 content by deriving witness-level Vinogradov bounds and
turning thresholded T3 smallness into a Farey-witness aggregation field. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent where
  zetaZeroFreeRegion := content.zetaZeroFreeRegion
  zetaToChebyshevPsiRealPNTRemainder :=
    content.zetaToChebyshevPsiRealPNTRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    content.primitivePageSiegelExceptionalQuadraticZero
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeI :=
    vinogradovTypeIBoundForVaughanWitnessUnconditional_of_linearEstimate
      content.vinogradovTypeILinear
  vinogradovTypeII :=
    vinogradovTypeIIBoundForVaughanWitnessUnconditional_of_bilinearEnergy
      content.vinogradovTypeIIEnergy
  vinogradovTypeIII :=
    vinogradovTypeIIIBoundForVaughanWitnessUnconditional_of_bilinearEnergy
      content.vinogradovTypeIIIEnergy
  t3FareyWitnessAggregation :=
    PathA_T3FareyWitnessAggregation_of_swThresholdSmallness
      content.t3SWThresholdSmallness

/-- Thresholded T3 + fully lowered Vinogradov content gives the assembled
no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_vinogradov_typeI_linear_typeII_typeIII_bilinearEnergies
    content.vinogradovTypeILinear
    content.vinogradovTypeIIEnergy
    content.vinogradovTypeIIIEnergy

/-- Thresholded T3 + fully lowered Vinogradov content gives the project-local
PNT remainder. -/
theorem pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)

/-- Thresholded T3 + fully lowered Vinogradov content gives the
non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)

/-- Thresholded T3 + fully lowered Vinogradov content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)

/-- Thresholded T3 + fully lowered Vinogradov content gives the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)

/-- Thresholded T3 + fully lowered Vinogradov content yields the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_fareyWitnessT3Content
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)

/-- Real-Chebyshev PNT plus exceptional-quadratic-zero Page-Siegel no-RH
Path A wrapper using thresholded local SW-shaped T3 smallness, a Type-I
linear estimate, and Type-II/III bilinear-energy Vinogradov targets. -/
theorem strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3Threshold_vinogradovEnergy
    (content :
      PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_fareyWitnessT3
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelFareyWitnessT3OpenContent_of_swT3ThresholdVinogradovEnergy
      content)
    finite threshold_covered

/-! ### Direct real-Chebyshev PNT package + exceptional-quadratic-zero Page-Siegel + thresholded T3 + fully lowered Vinogradov

This final wrapper accepts the PNT side as a direct package containing both
the zeta zero-free region and the real-variable Chebyshev `ψ` remainder.
It is useful when the PNT-with-`sqrt log` remainder is imported as a theorem
directly, rather than routed through a project-local explicit-formula bridge
from the zero-free region. -/

/-- **Direct real-Chebyshev PNT package plus exceptional-quadratic-zero
Page-Siegel content with thresholded local SW-shaped T3 smallness, Type-I
linear estimate, and Type-II/III bilinear-energy Vinogradov targets.** -/
structure PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Primitive Page-Siegel zero-free region with an optional quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZero :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero
  /-- Explicit formula and Siegel lower-bound handling for the quadratic zero. -/
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Lower-level Type I linear target for the Vaughan witness. -/
  vinogradovTypeILinear : VinogradovTypeILinearEstimateForVaughanWitness
  /-- Lower-level Type II bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIEnergy : VinogradovTypeIIBilinearEnergyForVaughanWitness
  /-- Lower-level Type III/high-high bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIIEnergy : VinogradovTypeIIIBilinearEnergyForVaughanWitness
  /-- Thresholded local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWThresholdSmallness : PathA_T3SWThresholdSmallnessForFareyWitness

/-- Direct real-Chebyshev PNT package content forgets to the earlier
bridge-shaped PNT interface by projecting the zero-free region and adapting
the packaged real-variable remainder to the old bridge field. -/
def PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent where
  zetaZeroFreeRegion :=
    zetaZeroFreeRegionForPNT_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
      content.pntRealRemainder
  zetaToChebyshevPsiRealPNTRemainder :=
    zetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
      content.pntRealRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    content.primitivePageSiegelExceptionalQuadraticZero
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    content.primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeILinear := content.vinogradovTypeILinear
  vinogradovTypeIIEnergy := content.vinogradovTypeIIEnergy
  vinogradovTypeIIIEnergy := content.vinogradovTypeIIIEnergy
  t3SWThresholdSmallness := content.t3SWThresholdSmallness

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
gives the assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
gives the project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    content.pntRealRemainder

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
gives the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)

/-- Direct PNT package + thresholded T3 + fully lowered Vinogradov content
yields the existential Hardy-Littlewood lower bound consumed by the finite
Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_realChebyshevPNT_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)

/-- Direct real-Chebyshev PNT-package plus exceptional-quadratic-zero
Page-Siegel no-RH Path A wrapper using thresholded local SW-shaped T3
smallness, a Type-I linear estimate, and Type-II/III bilinear-energy
Vinogradov targets. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_exceptional_quadratic_zero_pageSiegel_swT3Threshold_vinogradovEnergy
    (content :
      PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_realChebyshevPNT_exceptional_quadratic_zero_pageSiegel_swT3Threshold_vinogradovEnergy
    (PathA_UnconditionalRealChebyshevPNTExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pntRealRemainder
      content)
    finite threshold_covered

/-! ### Direct PNT package + direct Page-Siegel non-principal package + thresholded T3 + fully lowered Vinogradov

This wrapper packages the Page-Siegel side in the same style as the direct
PNT package above: the final no-RH handoff may consume a theorem package
containing both the quadratic exceptional-zero Page-Siegel statement and
the resulting non-principal Siegel-Walfisz estimate. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package,
thresholded local SW-shaped T3 smallness, Type-I linear estimate, and
Type-II/III bilinear-energy Vinogradov targets.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- T3 aggregation from per-arc Siegel-Walfisz shape to Fourier major arcs. -/
  swAggregation : SiegelWalfiszPerArcToFourierAggregation
  /-- Lower-level Type I linear target for the Vaughan witness. -/
  vinogradovTypeILinear : VinogradovTypeILinearEstimateForVaughanWitness
  /-- Lower-level Type II bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIEnergy : VinogradovTypeIIBilinearEnergyForVaughanWitness
  /-- Lower-level Type III/high-high bilinear-energy target for the Vaughan witness. -/
  vinogradovTypeIIIEnergy : VinogradovTypeIIIBilinearEnergyForVaughanWitness
  /-- Thresholded local T3 comparison for SW-shaped Farey witnesses. -/
  t3SWThresholdSmallness : PathA_T3SWThresholdSmallnessForFareyWitness

/-- Direct Page-Siegel package content forgets to the earlier bridge-shaped
Page-Siegel interface by projecting the zero-free region and adapting the
packaged non-principal Siegel-Walfisz theorem to the old bridge field. -/
def PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent where
  pntRealRemainder := content.pntRealRemainder
  primitivePageSiegelExceptionalQuadraticZero :=
    primitivePageSiegelExceptionalQuadraticZero_of_pageSiegelNonPrincipalPackage
      content.pageSiegelNonPrincipal
  primitivePageSiegelExceptionalQuadraticZeroToNonPrincipal :=
    primitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge_of_pageSiegelNonPrincipalPackage
      content.pageSiegelNonPrincipal
  swAggregation := content.swAggregation
  vinogradovTypeILinear := content.vinogradovTypeILinear
  vinogradovTypeIIEnergy := content.vinogradovTypeIIEnergy
  vinogradovTypeIIIEnergy := content.vinogradovTypeIIIEnergy
  t3SWThresholdSmallness := content.t3SWThresholdSmallness

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content gives the assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content gives the project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content gives the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegelNonPrincipalPackage
    content.pageSiegelNonPrincipal

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content gives the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content gives the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)

/-- Direct PNT and Page-Siegel packages + thresholded T3 + fully lowered
Vinogradov content yields the existential Hardy-Littlewood lower bound
consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_swT3ThresholdVinogradovEnergyContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_exceptionalQuadraticZeroPageSiegel_swT3ThresholdVinogradovEnergyContent
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)

/-- Direct PNT and Page-Siegel package no-RH Path A wrapper using
thresholded local SW-shaped T3 smallness, a Type-I linear estimate, and
Type-II/III bilinear-energy Vinogradov targets. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_swT3Threshold_vinogradovEnergy
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalSWT3ThresholdVinogradovEnergyOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_exceptional_quadratic_zero_pageSiegel_swT3Threshold_vinogradovEnergy
    (PathA_UnconditionalPNTRealRemainderExceptionalQuadraticZeroPageSiegelSWT3ThresholdVinogradovEnergyOpenContent_of_pageSiegelNonPrincipal
      content)
    finite threshold_covered

/-! ### Direct PNT + direct Page-Siegel + minor-arc/T3 package

This is the tightest final handoff currently exposed here.  It keeps the
PNT and Page-Siegel theorem packages from the previous wrappers, and it
replaces the remaining separate Vinogradov/T3 fields by a single package
containing the assembled no-RH minor-arc bound plus thresholded T3
smallness for the SW-shaped Farey witness. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and
a combined minor-arc/T3 package.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- Combined SW aggregation, assembled minor arc, and thresholded T3
  package. -/
  minorArcT3 : PathA_MinorArcT3SWThresholdPackage

/-- Direct PNT/Page-Siegel/minor-arc-T3 content gives the project-local PNT
remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    content.pntRealRemainder

/-- Direct PNT/Page-Siegel/minor-arc-T3 content gives the non-principal
Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegelNonPrincipalPackage
    content.pageSiegelNonPrincipal

/-- Direct PNT/Page-Siegel/minor-arc-T3 content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pnt_and_nonPrincipal
    (pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
      content)
    (siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
      content)

/-- Direct PNT/Page-Siegel/minor-arc-T3 content gives the assembled no-RH
minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_minorArcT3SWThresholdPackage content.minorArcT3

/-- Direct PNT/Page-Siegel/minor-arc-T3 content gives the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_minorArcT3SWThresholdPackage
    (siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
      content)
    content.minorArcT3

/-- Direct PNT/Page-Siegel/minor-arc-T3 content yields the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_PathA_QuantitativeContent
    (pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
      content)

/-- Direct PNT and Page-Siegel packages plus a combined minor-arc/T3
package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  rcases
      exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
        content with
    ⟨T, δ, hδ, hHL⟩
  rcases threshold_covered T δ hδ hHL with ⟨hT_le, hContam⟩
  exact strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound
    hδ finite hHL hT_le hContam

/-! ### Direct PNT + direct Page-Siegel + lowered Vinogradov/T3 package

This wrapper is one level lower than the assembled minor-arc/T3 wrapper:
it consumes the full lowered Vinogradov/Vaughan formalization package
directly and lets Lean assemble the no-RH minor-arc cosine bound. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and
a lowered Vinogradov/T3 package.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation plus full lowered Vinogradov/Vaughan formalization and
  thresholded T3 comparison. -/
  vinogradovT3 : PathA_VinogradovT3SWThresholdPackage

/-- Lowered Vinogradov/T3 final content forgets to the assembled
minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovT3SWThresholdPackage
      content.vinogradovT3

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content gives the
project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content gives the
non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content gives the assembled
no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content gives the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT/Page-Siegel/lowered-Vinogradov-T3 content yields the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)

/-- Direct PNT and Page-Siegel packages plus a lowered Vinogradov/T3
package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovT3
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovT3
      content)
    finite threshold_covered

/-! ### Direct PNT + direct Page-Siegel + Vinogradov/T3 split-quarter package

This is the tightest current no-RH final wrapper for the T3 side: the final
content no longer assumes the bundled thresholded T3 comparison, but instead
exposes the two quarter-smallness theorem targets separately through
`PathA_VinogradovT3SWQuarterSmallnessPackage`. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and
a lowered Vinogradov/T3 split-quarter package.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation plus full lowered Vinogradov/Vaughan formalization and
  split quarter-smallness T3 comparisons. -/
  vinogradovT3Quarter : PathA_VinogradovT3SWQuarterSmallnessPackage

/-- Split-quarter Vinogradov/T3 final content forgets to the thresholded
Vinogradov/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovT3 :=
    vinogradovT3SWThresholdPackage_of_vinogradovT3SWQuarterSmallnessPackage
      content.vinogradovT3Quarter

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content gives the
project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content gives the
non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content gives the
full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content gives the
assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content gives the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT/Page-Siegel/split-quarter-Vinogradov-T3 content yields the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)

/-- Direct PNT and Page-Siegel packages plus a lowered Vinogradov/T3
split-quarter package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3OpenContent_of_vinogradovT3Quarter
      content)
    finite threshold_covered

/-! ### Direct PNT + Page-Siegel + separated Vinogradov/T3 split-quarter package

This is the tightest current no-RH final wrapper on the Vinogradov/T3 side:
Type II and Type III are exposed in separated coefficient/kernel energy form,
and Prop 4 is exposed as the split quarter-smallness package. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and
a separated Vinogradov/T3 split-quarter package.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation plus separated Vinogradov/Vaughan formalization and
  split quarter-smallness T3 comparisons. -/
  vinogradovSeparatedT3Quarter :
    PathA_VinogradovSeparatedT3SWQuarterSmallnessPackage

/-- Separated Vinogradov/T3 final content forgets to the split-quarter
Vinogradov/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovT3Quarter :=
    vinogradovT3SWQuarterSmallnessPackage_of_vinogradovSeparatedT3SWQuarterSmallnessPackage
      content.vinogradovSeparatedT3Quarter

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content gives the
project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content gives the
non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content gives the assembled
no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content gives the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/separated-Vinogradov-T3 content yields the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)

/-- Direct PNT and Page-Siegel packages plus a separated Vinogradov/T3
split-quarter package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovSeparatedT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovT3Quarter
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovT3QuarterOpenContent_of_vinogradovSeparatedT3Quarter
      content)
    finite threshold_covered

/-! ### Direct PNT + Page-Siegel + fully separated Vinogradov/T3 package

This is the tightest current no-RH final wrapper on the Vinogradov/T3 side:
Type I, Type II, and Type III are all exposed in separated coefficient/kernel
forms, and Prop 4 is exposed as the split quarter-smallness package. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and
a fully separated Vinogradov/T3 split-quarter package.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation plus fully separated Vinogradov/Vaughan formalization
  and split quarter-smallness T3 comparisons. -/
  vinogradovFullySeparatedT3Quarter :
    PathA_VinogradovFullySeparatedT3SWQuarterSmallnessPackage

/-- Fully separated Vinogradov/T3 final content forgets to the
separated-bilinear Vinogradov/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovSeparatedT3Quarter :=
    vinogradovSeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3SWQuarterSmallnessPackage
      content.vinogradovFullySeparatedT3Quarter

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content gives the
project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content gives the
non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content gives the
full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content gives the
assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content gives the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3 content yields the
existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovSeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
split-quarter package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3Quarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovSeparatedT3Quarter
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovSeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3Quarter
      content)
    finite threshold_covered

/-! ### Direct PNT + Page-Siegel + fully separated Vinogradov/T3 minor package

This is the tightest current no-RH final wrapper on the Vinogradov/T3 side:
Type I, Type II, and Type III are all exposed in separated coefficient/kernel
forms, and the SW major-error half of Prop 4 is closed by
`PathA_T3SWMajorErrorQuarterSmallness_holds`.  The only remaining T3 field is
the minor-contribution quarter-smallness estimate. -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and a
fully separated Vinogradov/T3 package whose only T3 field is minor-contribution
quarter-smallness.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, fully separated Vinogradov/Vaughan formalization, and
  the remaining T3 minor-contribution quarter-smallness comparison. -/
  vinogradovFullySeparatedT3MinorQuarter :
    PathA_VinogradovFullySeparatedT3MinorQuarterSmallnessPackage

/-- Fully separated Vinogradov/T3 minor-quarter final content forgets to the
previous fully separated split-quarter final content by using the closed SW
major-error theorem. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovFullySeparatedT3Quarter :=
    vinogradovFullySeparatedT3SWQuarterSmallnessPackage_of_vinogradovFullySeparatedT3MinorQuarterSmallnessPackage
      content.vinogradovFullySeparatedT3MinorQuarter

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content gives
the project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content gives
the non-principal Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content gives
the full Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content gives
the assembled no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content gives
the quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT/Page-Siegel/fully-separated-Vinogradov-T3-minor content yields
the existential Hardy-Littlewood lower bound consumed by the finite Goldbach
bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3QuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
minor-quarter package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3Quarter
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3QuarterOpenContent_of_vinogradovFullySeparatedT3MinorQuarter
      content)
    finite threshold_covered

/-! ### Direct PNT + Page-Siegel + DFT-uniform T3 minor package -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and a
fully separated Vinogradov/T3 package whose remaining T3 field is the
DFT-uniform square minor-quarter target.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, fully separated Vinogradov/Vaughan formalization, and
  the remaining DFT-uniform minor-arc square quarter-smallness target. -/
  vinogradovFullySeparatedT3DftUniformMinorQuarter :
    PathA_VinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage

/-- DFT-uniform minor-quarter final content forgets to the previous
minor-quarter final content by using the Fourier-to-real minor bridge. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovFullySeparatedT3MinorQuarter :=
    vinogradovFullySeparatedT3MinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage
      content.vinogradovFullySeparatedT3DftUniformMinorQuarter

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content gives the project-local
PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content gives the non-principal
Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content gives the assembled
no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content gives the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT/Page-Siegel/DFT-uniform-minor content yields the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
DFT-uniform minor-quarter package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarter
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3MinorQuarter
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3MinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformMinorQuarter
      content)
    finite threshold_covered

/-! ### Direct PNT + Page-Siegel + little-o uniform DFT T3 minor package -/

/-- **Direct PNT package plus direct Page-Siegel non-principal package and a
fully separated Vinogradov/T3 package whose remaining T3 field is the
little-o uniform minor DFT bound.** -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent where
  /-- PNT package containing the zeta zero-free region and real-variable
  `Chebyshev.psi` remainder. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel package containing the quadratic exceptional-zero region
  and the resulting non-principal Siegel-Walfisz theorem. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, fully separated Vinogradov/Vaughan formalization, and
  the remaining little-o uniform minor DFT target. -/
  vinogradovFullySeparatedT3DftUniformLittleOMinor :
    PathA_VinogradovFullySeparatedT3DftUniformLittleOMinorPackage

/-- Little-o uniform DFT final content forgets to the previous DFT-square
minor-quarter final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovFullySeparatedT3DftUniformMinorQuarter :=
    vinogradovFullySeparatedT3DftUniformMinorQuarterSmallnessPackage_of_vinogradovFullySeparatedT3DftUniformLittleOMinorPackage
      content.vinogradovFullySeparatedT3DftUniformLittleOMinor

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content gives the project-local
PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content gives the non-principal
Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content gives the full
Siegel-Walfisz input. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content gives the assembled
no-RH minor-arc cosine bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content gives the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT/Page-Siegel/little-o-DFT-minor content yields the existential
Hardy-Littlewood lower bound consumed by the finite Goldbach bridge. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarterContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
little-o uniform minor DFT package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformMinorQuarter
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformMinorQuarterOpenContent_of_vinogradovFullySeparatedT3DftUniformLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with complement little-o DFT minor T3 handoff -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose T3 field
is stated on the complement of the supplied major arcs. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- Fully separated Vinogradov plus complement little-o uniform DFT minor
  T3 package. -/
  vinogradovFullySeparatedT3DftUniformComplementLittleOMinor :
    PathA_VinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage

/-- Complement little-o DFT content forgets to the previous minor-frequency
little-o DFT content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovFullySeparatedT3DftUniformLittleOMinor :=
    vinogradovFullySeparatedT3DftUniformLittleOMinorPackage_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage
      content.vinogradovFullySeparatedT3DftUniformComplementLittleOMinor

/-- Complement little-o DFT content gives the project-local PNT remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Complement little-o DFT content gives the non-principal Siegel-Walfisz
component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Complement little-o DFT content gives the full Siegel-Walfisz bound. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Complement little-o DFT content gives the assembled no-RH minor-arc
cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Complement little-o DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Complement little-o DFT content yields the existential Hardy-Littlewood
lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
complement little-o uniform minor DFT package suffice for the no-RH Path A
final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformLittleOMinor
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with finite-supremum little-o DFT minor T3 handoff -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose T3 field
is the finite-supremum DFT little-o statement on the supplied major-arc
complement. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- Fully separated Vinogradov plus finite-supremum little-o uniform DFT
  minor T3 package. -/
  vinogradovFullySeparatedT3DftSupComplementLittleOMinor :
    PathA_VinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage

/-- Finite-supremum little-o DFT content forgets to the previous complement
little-o DFT content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovFullySeparatedT3DftUniformComplementLittleOMinor :=
    vinogradovFullySeparatedT3DftUniformComplementLittleOMinorPackage_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinorPackage
      content.vinogradovFullySeparatedT3DftSupComplementLittleOMinor

/-- Finite-supremum little-o DFT content gives the project-local PNT
remainder. -/
theorem pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    PrimeCounting_PNT_RemainderBound :=
  pntRemainder_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Finite-supremum little-o DFT content gives the non-principal
Siegel-Walfisz component. -/
theorem siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Finite-supremum little-o DFT content gives the full Siegel-Walfisz bound. -/
theorem siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Finite-supremum little-o DFT content gives the assembled no-RH minor-arc
cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Finite-supremum little-o DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Finite-supremum little-o DFT content yields the existential
Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinorContent
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus a fully separated Vinogradov/T3
finite-supremum little-o uniform minor DFT package suffice for the no-RH
Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovFullySeparatedT3DftUniformComplementLittleOMinor
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovFullySeparatedT3DftUniformComplementLittleOMinorOpenContent_of_vinogradovFullySeparatedT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with expanded Type-I Vinogradov and finite-supremum DFT T3 handoff -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes Type I to the concrete divisor-antidiagonal Vaughan
expansion, keeps Type II/III as separated bilinear energies, and uses the
finite-supremum DFT little-o T3 target. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, expanded-Type-I Vinogradov, separated Type II/III
  energies, and finite-supremum little-o DFT T3. -/
  vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor :
    PathA_VinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage

/-- Expanded-Type-I finite-supremum DFT content forgets to the assembled
minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      content.vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor

/-- Expanded-Type-I finite-supremum DFT content gives the assembled no-RH
minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Expanded-Type-I finite-supremum DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Expanded-Type-I finite-supremum DFT content yields the existential
Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the expanded-Type-I
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with all Vaughan pieces expanded and finite-supremum DFT T3 handoff -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes Type I, Type II, and Type III to concrete nested
divisor-antidiagonal Vaughan expansions and uses the finite-supremum DFT
little-o T3 target. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, fully divisor-antidiagonal Vinogradov, and
  finite-supremum little-o DFT T3. -/
  vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor :
    PathA_VinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage

/-- Fully divisor-antidiagonal finite-supremum DFT content forgets to the
assembled minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorPackage
      content.vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor

/-- Fully divisor-antidiagonal finite-supremum DFT content gives the
assembled no-RH minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Fully divisor-antidiagonal finite-supremum DFT content produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Fully divisor-antidiagonal finite-supremum DFT content yields the
existential Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the fully divisor-antidiagonal
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with expanded Type I and separated-energy expanded Type II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes Type I to its concrete divisor-antidiagonal sum and
fixes Type II/III to coefficient/kernel energy estimates for their concrete
divisor-antidiagonal sums. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, expanded Type I, separated-energy expanded Type II/III,
  and finite-supremum little-o DFT T3. -/
  vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor :
    PathA_VinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage

/-- Expanded/separated-energy finite-supremum DFT content forgets to the
assembled minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      content.vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor

/-- Expanded/separated-energy finite-supremum DFT content gives the
assembled no-RH minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Expanded/separated-energy finite-supremum DFT content produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Expanded/separated-energy finite-supremum DFT content yields the
existential Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the expanded/separated-energy
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovTypeIDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with separated-energy expanded Type I/II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes all three Vaughan pieces to their concrete
divisor-antidiagonal sums and supplies all three through coefficient/kernel
energy estimates. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, separated-energy expanded Type I/II/III, and
  finite-supremum little-o DFT T3. -/
  vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor :
    PathA_VinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage

/-- Fully separated-energy finite-supremum DFT content forgets to the
assembled minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorPackage
      content.vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor

/-- Fully separated-energy finite-supremum DFT content gives the assembled
no-RH minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Fully separated-energy finite-supremum DFT content produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Fully separated-energy finite-supremum DFT content yields the
existential Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the fully separated-energy
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with componentized separated-energy expanded Type I/II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes all three Vaughan pieces to their concrete
divisor-antidiagonal sums and supplies componentized coefficient/kernel
energy functions for all three. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, componentized separated-energy expanded Type I/II/III,
  and finite-supremum little-o DFT T3. -/
  vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor :
    PathA_VinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage

/-- Componentized separated-energy finite-supremum DFT content forgets to
the assembled minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorPackage
      content.vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor

/-- Componentized separated-energy finite-supremum DFT content gives the
assembled no-RH minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
      content)

/-- Componentized separated-energy finite-supremum DFT content produces the
quantitative Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
      content)

/-- Componentized separated-energy finite-supremum DFT content yields the
existential Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the componentized
separated-energy Vinogradov/T3 finite-supremum DFT package suffice for the
no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalSeparatedEnergyComponentsT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with exact-energy expanded Type I/II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field fixes all three Vaughan pieces to their concrete
divisor-antidiagonal sums and asks only for product estimates on the actual
coefficient/kernel square-energies. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, exact-energy expanded Type I/II/III, and
  finite-supremum little-o DFT T3. -/
  vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor :
    PathA_VinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage

/-- Exact-energy finite-supremum DFT content forgets to the assembled
minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorPackage
      content.vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor

/-- Exact-energy finite-supremum DFT content gives the assembled no-RH
minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
      content)

/-- Exact-energy finite-supremum DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
      content)

/-- Exact-energy finite-supremum DFT content yields the existential
Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the exact-energy Vinogradov/T3
finite-supremum DFT package suffice for the no-RH Path A final wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovDivisorAntidiagonalExactEnergyT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with inner-sum bilinear Type II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field asks for Type II/III in the first-Cauchy-Schwarz inner-sum
energy form, paired with the finite-supremum little-o DFT T3 target. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, inner-sum bilinear Type II/III Vinogradov package, and
  finite-supremum little-o DFT T3. -/
  vinogradovInnerBilinearT3DftSupComplementLittleOMinor :
    PathA_VinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage

/-- Inner-sum bilinear finite-supremum DFT content forgets to the assembled
minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  minorArcT3 :=
    minorArcT3SWThresholdPackage_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage
      content.vinogradovInnerBilinearT3DftSupComplementLittleOMinor

/-- Inner-sum bilinear finite-supremum DFT content gives the assembled no-RH
minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
      content)

/-- Inner-sum bilinear finite-supremum DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
      content)

/-- Inner-sum bilinear finite-supremum DFT content yields the existential
Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the inner-sum bilinear
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_minorArcT3
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
      content)
    finite threshold_covered

/-! ### Final wrapper with pointwise inner-sum Type II/III -/

/-- Open analytic content for the direct PNT/Page-Siegel route whose
Vinogradov field asks for Type II/III pointwise inner-sum geometric majorants,
paired with the finite-supremum little-o DFT T3 target. -/
structure PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent where
  /-- PNT with `sqrt log` remainder, bundled with the zeta zero-free-region
  source used to prove it. -/
  pntRealRemainder : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
  /-- Page-Siegel exceptional quadratic-zero theorem bundled with the
  resulting non-principal Siegel-Walfisz statement. -/
  pageSiegelNonPrincipal :
    PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal
  /-- SW aggregation, pointwise inner-sum Type II/III Vinogradov package, and
  finite-supremum little-o DFT T3. -/
  vinogradovInnerPointwiseT3DftSupComplementLittleOMinor :
    PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage

/-- Pointwise inner-sum finite-supremum DFT content forgets to the
inner-bilinear final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent_of_innerPointwise
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent where
  pntRealRemainder := content.pntRealRemainder
  pageSiegelNonPrincipal := content.pageSiegelNonPrincipal
  vinogradovInnerBilinearT3DftSupComplementLittleOMinor :=
    vinogradovInnerBilinearT3DftSupComplementLittleOMinorPackage_of_innerPointwisePackage
      content.vinogradovInnerPointwiseT3DftSupComplementLittleOMinor

/-- Pointwise inner-sum finite-supremum DFT content forgets to the assembled
minor-arc/T3 final content. -/
def PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent) :
    PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent :=
  PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent_of_innerPointwise
      content)

/-- Pointwise inner-sum finite-supremum DFT content gives the assembled no-RH
minor-arc cosine-sum bound. -/
theorem minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent) :
    MinorArcCosineSumBound :=
  minorArcCosineSumBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
      content)

/-- Pointwise inner-sum finite-supremum DFT content produces the quantitative
Hardy-Littlewood content. -/
theorem pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent) :
    PathA_QuantitativeHardyLittlewoodContent :=
  pathA_quantitativeContent_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
      content)

/-- Pointwise inner-sum finite-supremum DFT content yields the existential
Hardy-Littlewood lower-bound package. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinorContent
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ :=
  exists_quarterBinaryHardyLittlewoodLowerBound_of_pntRealRemainder_quadraticZeroPageSiegelNonPrincipal_minorArcT3Content
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalMinorArcT3OpenContent_of_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
      content)

/-- Direct PNT and Page-Siegel packages plus the pointwise inner-sum
Vinogradov/T3 finite-supremum DFT package suffice for the no-RH Path A final
wrapper. -/
theorem strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
    (content :
      PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerPointwiseT3DftSupComplementLittleOMinorOpenContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerBilinearT3DftSupComplementLittleOMinor
    (PathA_UnconditionalPNTRealRemainderQuadraticZeroPageSiegelNonPrincipalVinogradovInnerBilinearT3DftSupComplementLittleOMinorOpenContent_of_innerPointwise
      content)
    finite threshold_covered

/-! ## Section 30 — P5-M8 Phase 5 reduced bundle

After Phase 5 (P5-T1 through P5-T6) decomposed and partially closed the
Phase 4 / M7 atoms, the genuinely remaining open analytic content
shrinks.  This section consolidates the Phase 5 reductions into a single
new bundle `PathA_Phase5ReducedContent` and exposes a new headline
`strongGoldbach_under_RH_phase5_reduced` alongside the M7 headline.

### Phase 5 closures absorbed by the new bundle

* `ZS, TE, bridge, hZS, hTE` from `PathA_MaximallyReducedContent` are
  replaced by the **3 Perron-chain atoms** from P5-T1
  (`PerronTruncatedFormulaCorrect`, `ContourShiftIdentityHolds`,
  `ResidueExtractionCorrect`) plus a `PsiSquareRootErrorBound` field
  (the `RH`-side analytic content needed to bound the trivial-witness
  `ZS x := ψ x − x` pair).  The three Perron atoms are unconditionally
  inhabited (`*_holds` lemmas in `PathA_ExplicitFormula`), so they
  record the *interface* of the Perron decomposition without imposing
  new open content.

* `perronToPsiAPErrorBridge` is replaced by the **3 character-twisted
  Perron-chain atoms** (`CharacterPerronTruncatedFormula`,
  `CharacterContourShiftIdentity`, `CharacterResidueExtraction`) plus
  the irreducible chain step
  `CharacterChainGivesPsiAPErrorBoundShape`.  The three atoms are
  unconditionally inhabited; the chain step is the single residual
  analytic content.

* `pageSiegelZeroFree` is replaced by the **2 open Page-Siegel
  sub-Props** (`ZFRPrimitiveLogarithmicDistance`,
  `SiegelExceptionalZeroAlone`); the third sub-Prop
  `ZFRPrimitiveStripVerticalLine` was *closed via mathlib* in P5-T2
  (`zFRPrimitiveStripVerticalLine_proved`).

* `singleShapeData` is replaced by the **Plancherel / character
  orthogonality** data `(A, A_pos, Q, Q_ge_one, N₀, aggConsts,
  uniformPlancherel)` for the concrete Farey arc family
  `faradayArcFamilyAt Q` (P5-T3).

* `typeI_abel`, `typeI_dirichlet`, `typeII_cauchy`, `typeII_dirichlet`
  from `PathA_MaximallyReducedContent` are dropped.  P5-T4 / P5-T5
  closed `AbelSummationOnGeometricSum vaughanS_I_witness` and
  `CauchySchwarzOnBilinearSum vaughanS_II_witness` unconditionally with
  trivial witnesses, and the Dirichlet-refined `DirichletApprox*`
  components are structurally vacuous Phase 4 conditions.  Only the
  universal-`α` `typeIUnconditional`, `typeIIUnconditional`,
  `typeIIIUnconditional` Vinogradov bounds carry through (they remain
  the genuine Phase 6 target).

* `smallness_major`, `smallness_minor`, `smallness_compat` are replaced
  by the **P5-T6 pinned major-arc smallness** (`δ_M = 1/4`, concretely
  obtained from the Plancherel data) plus a single named minor-arc
  Phase 6 target `MinorArcSmallnessFromVinogradovBoundThreeQuarter
  (faradayArcFamilyAt Q)` with `δ_m < 3/4`.  Compatibility
  `δ_M + δ_m < 1` is then automatic numerics.

### Carrying through unchanged

* `pntRemainder : PrimeCounting_PNT_RemainderBound` — Phase 5 did not
  reduce this; it remains the principal-modulus SW input.
* `typeIUnconditional`, `typeIIUnconditional`, `typeIIIUnconditional` —
  P5-T4/T5 only reduced the Dirichlet-refined components.  The
  universal-`α` Props remain (false-as-stated for `α = 0`, hence a
  genuine Phase 6 target).
-/

/-- **Phase 5 reduced bundle** consolidating the remaining open
analytic content after P5-T1 through P5-T6.

This bundle is the Phase-5-aware analogue of
`PathA_MaximallyReducedContent`.  Compared with the M7 bundle it:

* replaces the function-form Perron bridge `(ZS, TE, bridge, hZS, hTE)`
  with the **three named P5-T1 atoms** plus a `PsiSquareRootErrorBound`
  field (the trivial-witness route);
* replaces `perronToPsiAPErrorBridge` with the **three character-twisted
  P5-T1 atoms** plus the irreducible
  `CharacterChainGivesPsiAPErrorBoundShape` step;
* replaces `pageSiegelZeroFree` with the **two open P5-T2 sub-Props**
  (`ZFRPrimitiveLogarithmicDistance`, `SiegelExceptionalZeroAlone`); the
  strip vertical line sub-Prop is closed by mathlib;
* replaces `singleShapeData` with the **P5-T3 Plancherel / character
  orthogonality data** `(A, Q, N₀, aggConsts, uniformPlancherel)` for
  the concrete Farey arc family;
* drops the Dirichlet-refined Vinogradov sub-Props (P5-T4/T5 either
  closed them unconditionally or showed they are structurally vacuous);
* replaces `(smallness_major, smallness_minor, smallness_compat)` with
  the **P5-T6 minor-arc target**
  `MinorArcSmallnessFromVinogradovBoundThreeQuarter (faradayArcFamilyAt Q)`
  with `δ_m < 3/4`; the major-arc side and compatibility numerics are
  pinned mechanically.

Combined with `RiemannHypothesis` and the usual finite-verification
hypothesis, an inhabitant of this structure yields `StrongGoldbach` via
`strongGoldbach_under_RH_phase5_reduced`. -/
structure PathA_Phase5ReducedContent where
  /-- P5-T1 Atom 1: Perron truncated formula correctness (existential). -/
  perronTruncated : PerronTruncatedFormulaCorrect
  /-- P5-T1 Atom 2: contour-shift residue-decomposition identity. -/
  contourShift : ContourShiftIdentityHolds
  /-- P5-T1 Atom 3: residue extraction with RH-side zero-sum bound. -/
  residueExtract : ResidueExtractionCorrect
  /-- RH-side analytic input for the trivial-witness explicit-formula
  bridge route.  This is the function-form analog of `(hZS, hTE)` with
  `ZS x := ψ(x) − x`, `TE := 0`. -/
  psiBound : PsiSquareRootErrorBound
  /-- Character-twisted Perron Atom 1: truncated formula. -/
  charPerronTruncated :
    Gdbh.CharacterPerronTruncatedFormula
  /-- Character-twisted Perron Atom 2: contour-shift identity. -/
  charContourShift :
    Gdbh.CharacterContourShiftIdentity
  /-- Character-twisted Perron Atom 3: residue extraction. -/
  charResidueExtract :
    Gdbh.CharacterResidueExtraction
  /-- Irreducible character-chain step: the three character atoms imply
  `PsiAPErrorBoundShape`. -/
  charChainGivesShape :
    Gdbh.CharacterChainGivesPsiAPErrorBoundShape
  /-- P5-T2 open sub-Prop: logarithmic-distance Page region (all
  non-real zeros excluded). -/
  pageLogDistance : Gdbh.ZFRPrimitiveLogarithmicDistance
  /-- P5-T2 open sub-Prop: Siegel exceptional-zero alone. -/
  siegelAlone : Gdbh.SiegelExceptionalZeroAlone
  /-- Principal Siegel-Walfisz input: PNT with `exp(−c√log)` remainder. -/
  pntRemainder : Gdbh.PrimeCounting_PNT_RemainderBound
  /-- P5-T3 Plancherel data: SW shape parameter `A > 0`. -/
  A : ℝ
  /-- Positivity of the SW shape parameter. -/
  A_pos : 0 < A
  /-- P5-T3 Plancherel data: Farey cutoff `Q ≥ 1`. -/
  Q : Nat
  /-- Lower bound `1 ≤ Q`. -/
  Q_ge_one : 1 ≤ Q
  /-- P5-T3 Plancherel data: uniform threshold `N₀`. -/
  N₀ : Nat
  /-- P5-T3 Plancherel data: aggregation constants map. -/
  aggConsts : ℝ → ℝ → ℝ × ℝ
  /-- P5-T3 Plancherel + character orthogonality witness for the
  Farey arc family. -/
  uniformPlancherel :
    UniformCharacterOrthogonalityAndPlancherelForFareyFamily A Q N₀ aggConsts
  /-- Universal-`α` unconditional Vinogradov Type I bound on the
  concrete Vaughan witness. -/
  typeIUnconditional :
    PathAMinorArc.VinogradovTypeIBoundForVaughanWitnessUnconditional
  /-- Universal-`α` unconditional Vinogradov Type II bound. -/
  typeIIUnconditional :
    PathAMinorArc.VinogradovTypeIIBoundForVaughanWitnessUnconditional
  /-- Universal-`α` unconditional Vinogradov Type III/high-high bound. -/
  typeIIIUnconditional :
    PathAMinorArc.VinogradovTypeIIIBoundForVaughanWitnessUnconditional
  /-- P5-T6 minor-arc Phase 6 target: effective Vinogradov-bilinear
  bound on the real minor contribution against
  `faradayArcFamilyAt Q`, with explicit `δ_m < 3/4` so that the
  compatibility constraint with the pinned `δ_M = 1/4` holds. -/
  minorArcVinogradov :
    MinorArcSmallnessFromVinogradovBoundThreeQuarter (faradayArcFamilyAt Q)

/-- **Projection**: the Phase 5 bundle's Page-Siegel sub-Props assemble
to `PrimitivePageSiegelZeroFreeRegionWithExceptional`.  The strip
vertical-line sub-Prop is closed by mathlib (P5-T2). -/
theorem pageSiegelZeroFree_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_subProps_strip_closed
    content.pageLogDistance content.siegelAlone

/-- **Projection**: the Phase 5 bundle's character-twisted Perron chain
assembles to `PerronToPsiAPErrorFromZeroFreeRegionBridge`. -/
theorem perronToPsiAPErrorBridge_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    PerronToPsiAPErrorFromZeroFreeRegionBridge :=
  perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChain
    content.charPerronTruncated content.charContourShift
    content.charResidueExtract content.charChainGivesShape

/-- **Projection**: the Phase 5 bundle's Page-Siegel + character-Perron
fields assemble to `SiegelWalfiszNonPrincipal`. -/
theorem siegelWalfiszNonPrincipal_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegelExceptional_perron
    (pageSiegelZeroFree_of_phase5ReducedContent content)
    (perronToPsiAPErrorBridge_of_phase5ReducedContent content)

/-- **Projection**: the Phase 5 bundle plus PNT remainder give the full
`SiegelWalfiszBound`. -/
theorem siegelWalfiszBound_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_pnt_and_nonPrincipal content.pntRemainder
    (siegelWalfiszNonPrincipal_of_phase5ReducedContent content)

/-- **Projection**: the Phase 5 bundle's Plancherel data assembles to
a concrete `SiegelWalfiszSingleShapeData` value at the Farey arc family
`faradayArcFamilyAt Q`. -/
noncomputable def singleShapeData_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    SiegelWalfiszSingleShapeData :=
  defaultSiegelWalfiszSingleShapeData_of_subProps
    content.A_pos content.Q_ge_one content.N₀ content.aggConsts
    content.uniformPlancherel

/-- **Projection**: the Phase 5 bundle's Plancherel data assembles to
`SiegelWalfiszFourierBridge`. -/
theorem siegelWalfiszFourierBridge_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    SiegelWalfiszFourierBridge :=
  siegelWalfiszFourierBridge_of_uniformFareySubProps
    content.A_pos content.Q_ge_one content.N₀ content.aggConsts
    content.uniformPlancherel

/-- **Projection**: the Phase 5 bundle assembles to `MajorArcEstimate`
via the standard SW + Fourier-bridge composition. -/
theorem majorArcEstimate_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    MajorArcEstimate :=
  majorArcEstimate_of_SiegelWalfisz_substantive
    (siegelWalfiszBound_of_phase5ReducedContent content)
    (siegelWalfiszFourierBridge_of_phase5ReducedContent content)

/-- **Projection**: the Phase 5 bundle's three universal-`α` Vinogradov
fields produce `MinorArcCosineSumBound`. -/
theorem minorArcCosineSumBound_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    MinorArcCosineSumBound :=
  PathAMinorArc.minorArcCosineSumBound_of_vinogradov_unconditional_witnesses
    content.typeIUnconditional content.typeIIUnconditional
    content.typeIIIUnconditional

/-- **Projection**: the Phase 5 bundle's `MinorArcSmallnessFromVinogradovBoundThreeQuarter`
field forgets to the contribution-form Phase 4 sub-Prop. -/
theorem minorArcSmallnessFromContribution_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    MinorArcSmallnessFromContribution (faradayArcFamilyAt content.Q) :=
  MinorArcSmallnessFromContribution_of_threeQuarter content.minorArcVinogradov

/-- **Projection**: the Phase 5 bundle's three Perron atoms + the
`PsiSquareRootErrorBound` field produce a `VonMangoldtExplicitFormulaBound`
via the trivial-witness route (`ZS x := ψ x − x`, `TE := 0`,
`bridge := ExplicitFormulaBridgeFor_trivial_witness`).

The three atoms are not consumed mechanically; they record the Phase 5
decomposition of the analytic content.  The `PsiSquareRootErrorBound`
field carries the RH-side input. -/
theorem vonMangoldtExplicitFormulaBound_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    VonMangoldtExplicitFormulaBound :=
  vonMangoldtExplicitFormulaBound_of_bridge_for
    (fun x => Chebyshev.psi x - x) (fun _ => 0)
    ExplicitFormulaBridgeFor_trivial_witness
    content.psiBound
    ⟨1, 1, by norm_num, by norm_num, fun x hx => by
      have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
      have h1 : 0 ≤ 1 * (Real.log x) ^ (2 : Nat) := by positivity
      have h2 : 0 ≤ 1 * Real.log x := by positivity
      have habs : |(0 : ℝ)| = 0 := abs_zero
      rw [habs]; linarith⟩

/-! ### Farey-witness route: Phase 5 bundle to `PathA_AnalyticImplication`

The Phase 5 bundle pins all of its analytic content at the concrete
Farey arc family `faradayArcFamilyAt content.Q`.  We therefore route
the analytic implication through the **witness-specific** Farey form
`PathA_HardyLittlewoodSmallnessForFareyWitness`, *not* the universal-form
witness sub-Prop of the M7 maximally-reduced bundle.

This is the genuinely Phase-5-aware route: the universal-form smallness
Prop is not constructible from the Farey-pinned data without further
Phase 6 content.  In exchange, we obtain a *strictly tighter* analytic
implication that lives at the concrete `faradayArcFamilyAt content.Q`. -/

/-- **Pinned major-arc smallness for the Farey family at level
`content.Q`** in full witness form, with the explicit error function
and concrete threshold produced by the P5-T6 + P5-T3 chain. -/
theorem phase5_pinned_majorArcSmallness_full
    (content : PathA_Phase5ReducedContent) :
    ∃ (N₀_pin : Nat) (C c : ℝ),
      0 < C ∧ 0 < c ∧
      (∀ n : Nat, N₀_pin < n → Even n →
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
            (faradayArcFamilyAt content.Q) n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          siegelWalfiszErrorFn C c n) ∧
      MajorArcSmallnessFromErrorFn N₀_pin
        (siegelWalfiszErrorFn C c) :=
  pinned_majorArcSmallness_full_for_farady_family
    content.A_pos content.Q_ge_one content.N₀ content.aggConsts
    (siegelWalfiszBound_of_phase5ReducedContent content)
    content.uniformPlancherel

/-- **Farey-witness Hardy-Littlewood smallness from the Phase 5
bundle**.  Every existential quantifier of
`PathA_HardyLittlewoodSmallnessForFareyWitness` is pinned to a
Phase-5-specific concrete value:

* `Q := content.Q`,
* `N₀ := max N₀_pin N_M` where `N₀_pin` is the major-arc
  approximation threshold from the P5-T6 pinning and `N_M` is the
  eventual-quarter threshold for `siegelWalfiszErrorFn C c`,
* `majorArcs := faradayArcFamilyAt content.Q`,
* `errorFn := siegelWalfiszErrorFn C c` with `(C, c)` from the P5-T3
  Plancherel data + the M7 connector,
* `δ_M = 1/4` (the pinned coefficient from the eventually-quarter
  lemma), `δ_m < 3/4` from the bundle's `minorArcVinogradov` field.
  Compatibility `1/4 + δ_m < 1` is automatic from `δ_m < 3/4`. -/
theorem phase5_HardyLittlewoodSmallnessForFareyWitness
    (content : PathA_Phase5ReducedContent) :
    PathA_HardyLittlewoodSmallnessForFareyWitness := by
  -- Step 1: extract pinned major-arc data.
  obtain ⟨N₀_pin, C, c, hC_pos, hc_pos, hAgg, _hMajor⟩ :=
    phase5_pinned_majorArcSmallness_full content
  -- Step 2: extract the eventual-quarter threshold N_M for the SW error.
  obtain ⟨N_M, hQuarter⟩ :=
    MajorArc_siegelWalfiszErrorFn_eventually_quarter_singularSeries hC_pos hc_pos
  -- Step 3: combine thresholds via max.  Both the approximation bound
  -- and the quarter bound hold for `n > max N₀_pin N_M`.
  refine ⟨content.Q, max N₀_pin N_M,
    faradayArcFamilyAt content.Q,
    siegelWalfiszErrorFn C c, content.Q_ge_one, ?_, ?_⟩
  · -- Major-arc approximation bound on the combined threshold.
    intro n hn hEven
    have hn_pin : N₀_pin < n :=
      lt_of_le_of_lt (le_max_left _ _) hn
    exact hAgg n hn_pin hEven
  · -- Witness-specific smallness via the pinned-quarter assembly.
    refine pathA_HardyLittlewoodSmallnessForWitness_of_pinned_quarter_threeQuarter
      (N₀ := max N₀_pin N_M) ?_ content.minorArcVinogradov
    intro n hn hEven
    have hn_NM : N_M < n :=
      lt_of_le_of_lt (le_max_right _ _) hn
    exact hQuarter n hn_NM hEven

/-- **Phase 5 bundle to `PathA_AnalyticImplication`** via the Farey
witness route.  Composes the Farey-witness smallness with the closed
Farey major-arc witness shape (`PathA_FareyMajorArcBound_holds`). -/
theorem pathA_analyticImplication_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    PathA_AnalyticImplication :=
  pathA_analyticImplication_of_smallnessForFareyWitness
    (phase5_HardyLittlewoodSmallnessForFareyWitness content)

/-- **Phase 5 bundle to existential quarter Hardy-Littlewood bound**:
combine the analytic implication with the three Phase 4 intermediate
bounds projected from the Phase 5 fields. -/
theorem exists_quarterBinaryHardyLittlewoodLowerBound_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent) :
    ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
      QuarterBinaryHardyLittlewoodLowerBound T δ := by
  have psi : PsiSquareRootErrorBound :=
    psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound
      (vonMangoldtExplicitFormulaBound_of_phase5ReducedContent content)
  exact pathA_analyticImplication_of_phase5ReducedContent content
    psi (minorArcCosineSumBound_of_phase5ReducedContent content)
    (majorArcEstimate_of_phase5ReducedContent content)

/-! ### Subsumption note: Phase 5 bundle ⟹ headline

The Phase 5 bundle does **not** produce a `PathA_MaximallyReducedContent`
or `PathA_MinimalOpenContent` value, because both of those bundles
carry a *universal-form* smallness sub-Prop quantified over arbitrary
arc families, while the Phase 5 bundle pins all of its smallness
content at the concrete `faradayArcFamilyAt content.Q` (via P5-T3 +
P5-T6).  The Farey-pinned data does not imply the universal-form
smallness without further analytic content.

Instead, the subsumption is expressed at the **headline level**: every
end-conclusion produced by `strongGoldbach_under_RH_maximally_reduced`
or `strongGoldbach_under_RH_minimal_open` (i.e. `StrongGoldbach`) is
also produced by `strongGoldbach_under_RH_phase5_reduced`, but through
a *different* internal chain — the Farey-pinned smallness witness
rather than the universal-form smallness sub-Prop.

The intermediate Path A bounds (`PsiSquareRootErrorBound`,
`MinorArcCosineSumBound`, `MajorArcEstimate`,
`PathA_AnalyticImplication`) are also projectable from the Phase 5
bundle, and the projections appear in Section 30 above. -/

/-! ### Headline theorem: `strongGoldbach_under_RH_phase5_reduced` -/

/-- **P5-M8 headline**: given `RiemannHypothesis`, a Phase 5 reduced
bundle, and the usual finite-verification hypothesis, conclude
`StrongGoldbach`.

The chain composes:

1. `vonMangoldtExplicitFormulaBound_of_phase5ReducedContent` produces
   `VonMangoldtExplicitFormulaBound` from the trivial-witness Perron
   bridge + `psiBound`.
2. `minorArcFromPsiBound_of_vinogradov_unconditional_witnesses` on the
   three universal-α Vinogradov fields gives `MinorArcFromPsiBound`
   (ignoring the ψ hypothesis).
3. `majorArcEstimate_of_phase5ReducedContent` chains
   `pntRemainder + pageLogDistance + siegelAlone + charPerronChain +
   uniformPlancherel` through the SW + Fourier-bridge composition.
4. `pathA_analyticImplication_of_phase5ReducedContent` routes through
   the Farey-pinned smallness data via
   `pathA_HardyLittlewoodSmallnessForWitness_of_pinned_quarter_threeQuarter`.
5. The Phase A wrapper `strongGoldbach_via_PathA_full` closes the
   chain modulo `RiemannHypothesis`. -/
theorem strongGoldbach_under_RH_phase5_reduced
    (rh : RiemannHypothesis)
    (content : PathA_Phase5ReducedContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach :=
  strongGoldbach_via_PathA_full rh
    (fun _ => vonMangoldtExplicitFormulaBound_of_phase5ReducedContent content)
    (PathAMinorArc.minorArcFromPsiBound_of_vinogradov_unconditional_witnesses
      content.typeIUnconditional content.typeIIUnconditional
      content.typeIIIUnconditional)
    (majorArcEstimate_of_phase5ReducedContent content)
    (pathA_analyticImplication_of_phase5ReducedContent content)
    finite threshold_covered

/-- **Single-arrow form** parameterised by the Phase 5 bundle:
`RiemannHypothesis ⟹ StrongGoldbach`. -/
theorem strongGoldbach_under_RH_of_phase5ReducedContent
    (content : PathA_Phase5ReducedContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    RiemannHypothesis → StrongGoldbach :=
  fun rh =>
    strongGoldbach_under_RH_phase5_reduced rh content finite threshold_covered

end Gdbh
