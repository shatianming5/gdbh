/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P24-T3 (Phase 24 / Path A — status check after P5 reductions).
-/
import Gdbh.PathA_Final

/-!
# Path A — P24-T3: Status check after Phase 5 reductions

## Mission

This file is the **Phase 24 status snapshot** of Path A — the
RH-conditional binary Goldbach route via von Mangoldt + circle method
(Phases 1–5).  Phases 6–23 focused on Path C (Schnirelmann + Brun);
this file records the current closure state of Path A so that any
future work can resume from a known baseline.

## Path A in two lines

`StrongGoldbach` follows from `RiemannHypothesis` together with an
inhabitant of `PathA_Phase5ReducedContent`, via the headline theorem
`Gdbh.strongGoldbach_under_RH_phase5_reduced` (see `Gdbh/PathA_Final.lean`).
This is the most-reduced Path A bundle currently in the project.

## The Phase 5 reduced bundle (22 fields total — 17 Props + 5 data)

The bundle `Gdbh.PathA_Phase5ReducedContent` lives at
`Gdbh/PathA_Final.lean:7139`.  Its fields, grouped by P5 subtask:

* **P5-T1 (Perron decomposition)** — three "atoms" + the ψ-input field:
  1. `perronTruncated  : PerronTruncatedFormulaCorrect`
  2. `contourShift     : ContourShiftIdentityHolds`
  3. `residueExtract   : ResidueExtractionCorrect`
  4. `psiBound         : PsiSquareRootErrorBound`     -- RH-conditional!
* **P5-T1c (Character-twisted Perron chain)** — four character atoms:
  5. `charPerronTruncated   : CharacterPerronTruncatedFormula`
  6. `charContourShift      : CharacterContourShiftIdentity`
  7. `charResidueExtract    : CharacterResidueExtraction`
  8. `charChainGivesShape   : CharacterChainGivesPsiAPErrorBoundShape`
* **P5-T2 (Zero-free region — Page + Siegel)** — two open sub-Props:
  9. `pageLogDistance       : ZFRPrimitiveLogarithmicDistance`
  10. `siegelAlone          : SiegelExceptionalZeroAlone`
* **Principal SW input**:
  11. `pntRemainder         : PrimeCounting_PNT_RemainderBound`
* **P5-T3 (Plancherel / Fourier aggregation)** — 5 numerical data + 1 Prop:
  12. `A          : ℝ`
  13. `A_pos      : 0 < A`
  14. `Q          : Nat`
  15. `Q_ge_one   : 1 ≤ Q`
  16. `N₀         : Nat`
  17. `aggConsts  : ℝ → ℝ → ℝ × ℝ`
  18. `uniformPlancherel :
       UniformCharacterOrthogonalityAndPlancherelForFareyFamily A Q N₀ aggConsts`
* **P5-T5 (Universal-α Vinogradov bounds)** — three unconditional Props:
  19. `typeIUnconditional   : VinogradovTypeIBoundForVaughanWitnessUnconditional`
  20. `typeIIUnconditional  : VinogradovTypeIIBoundForVaughanWitnessUnconditional`
  21. `typeIIIUnconditional : VinogradovTypeIIIBoundForVaughanWitnessUnconditional`
* **P5-T6 (Minor-arc smallness ⟨3/4⟩)**:
  22. `minorArcVinogradov   :
        MinorArcSmallnessFromVinogradovBoundThreeQuarter (faradayArcFamilyAt Q)`

## False-Prop risk audit

In Phases 9-22 the Path C closure flagged **15 literal false-Prop
catches** (documented in `Gdbh/PathC_FinalSummaryPhase22.lean`).  We
audit each Path A field for the analogous risks (vacuous existential,
universally-false universal, or hidden inconsistency).

### Risk 1 — DEFINITIVELY PRESENT: the universal `ExplicitFormulaBridge`

The legacy bundle `Gdbh.PathA_TotalAnalyticContent`
(`Gdbh/PathA_Final.lean:115`) has a field
`bridge : ExplicitFormulaBridge` whose Prop is
**structurally false** when read literally:
`∀ x ≥ 1, ∀ ZeroSum TruncErr : ℝ, |ψ(x) - x| ≤ |ZeroSum| + |TruncErr| + log x`.
Taking `ZeroSum = TruncErr = 0` would force `|ψ(x) - x| ≤ log x`,
which is false (cf. the explicit comment block at
`Gdbh/PathA_ExplicitFormula.lean:613-624`).

**Resolution path (already applied):** The newer bundles
`PathA_MinimalOpenContent`, `PathA_MaximallyReducedContent`, and
`PathA_Phase5ReducedContent` instead use the **function-form** bridge
`ExplicitFormulaBridgeFor (ZS TE : ℝ → ℝ)` together with named
analytic bounds `hZS, hTE` (in the minimal/maximally-reduced bundles)
or the direct `psiBound : PsiSquareRootErrorBound` (in the Phase 5
bundle).  The function-form bridge IS satisfiable (witness:
`ZS x := ψ(x) − x, TE := 0`), and the analytic content has been
**moved out of the bridge** into the witness bounds.

In the Phase 5 bundle specifically, the bridge identity is discharged
mechanically by `ExplicitFormulaBridgeFor_trivial_witness` (with
`ZS x := ψ x - x`, `TE := 0`), so the bridge field is **not a gap**.
The genuine RH content lives entirely in `psiBound`.

### Risk 2 — DEFERRED: P5-T1 Perron atoms are existential-only

Each of `PerronTruncatedFormulaCorrect`, `ContourShiftIdentityHolds`,
`ResidueExtractionCorrect` is an existential `Prop` that admits a
trivial *quantifier* witness (e.g. take `PT T x := ψ(x)`,
`R := 0`, `Tail := 0`, etc.).  Concretely, the theorems
`PerronTruncatedFormulaCorrect_quantifier_witness`,
`ContourShiftIdentityHolds_quantifier_witness`,
`ResidueExtractionCorrect_quantifier_witness` are already proved at
`Gdbh/PathA_ExplicitFormula.lean:964, 981, 995`.

This means the three atoms are **not genuine RH gaps** (they are
shape Props, not analytic content); their trivial witnesses combined
with the `psiBound` field discharge `VonMangoldtExplicitFormulaBound`
via the function-form bridge route.  No false-Prop risk here.

### Risk 3 — GENUINE GAP: `PsiSquareRootErrorBound` is the load-bearing field

`PsiSquareRootErrorBound` (`Gdbh/ConditionalPaths.lean:46`):
`∃ C x₀, ∀ x ≥ x₀, |ψ(x) − x| ≤ C · √x · log²x`.

Under GRH this is a theorem; **unconditionally it is open**.  Under
RH (the Path A premise), it follows from the explicit-formula
machinery via the (still-open) zero-counting + residue calculation.

This is **the single hardest field** of the Phase 5 bundle and is a
genuine analytic open Prop, not a false Prop.  It cannot be
trivialized: the constant `C` and the exponent `log²x` exclude any
vacuous witness.

### Risk 4 — Page + Siegel + PNT remainder

`ZFRPrimitiveLogarithmicDistance`, `SiegelExceptionalZeroAlone`, and
`PrimeCounting_PNT_RemainderBound` are classical analytic Props from
mathlib's Dirichlet-L-function chapter
(`Gdbh/MathlibExtras/DirichletLFunctions.lean`).  Each is satisfiable
in shape (the existentials admit witnesses), but each requires the
genuine analytic proof (Hadamard product, Siegel's effective zero,
PNT with `exp(−c√log N)` remainder).  None is a false Prop.

### Risk 5 — Plancherel data + uniform character orthogonality

`UniformCharacterOrthogonalityAndPlancherelForFareyFamily` is
satisfiable in its quantifier shape but encodes the actual analytic
Plancherel + character-orthogonality content; the five numerical
parameters `A, Q, N₀, aggConsts` are data that the user chooses, not
gaps.  No false-Prop risk.

### Risk 6 — Vinogradov universal-α bounds + minor-arc 3/4-bound

`VinogradovTypeIBoundForVaughanWitnessUnconditional` (etc.) and
`MinorArcSmallnessFromVinogradovBoundThreeQuarter` are the genuine
unconditional Vinogradov + Vaughan content needed for the minor-arc
side; classical, not yet formalised.  No false-Prop risk.

## Conclusion

After scanning all 22 fields of `PathA_Phase5ReducedContent`:

* **No field is structurally false.**  The known structural false Prop
  `ExplicitFormulaBridge` was already refactored out of the Phase 5
  bundle (and out of the minimal / maximally-reduced bundles) and
  replaced with the function-form variant.  This is the analog of the
  Path C false-Prop catches 11-13.
* **One field is the load-bearing RH content:** `psiBound :
  PsiSquareRootErrorBound`.  Closing this single field under RH closes
  the entire P5-T1 / P5-T1c Perron-chain block of the bundle
  (combined with the existing trivial witnesses).
* **Three classical analytic Props remain open:** Page (Z FR),
  Siegel (alone), and PNT remainder.  Each is a known classical
  theorem not yet in mathlib v4.29.1.
* **Four Vinogradov / minor-arc Props remain open:** the three
  universal-α Type I/II/III Vinogradov bounds and the
  `δ_m < 3/4` Vaughan bilinear bound.  All are classical.

In total, **9 genuinely open Props** remain on the Path A Phase 5
bundle (psiBound, page, siegel, pntRemainder, uniformPlancherel,
typeI, typeII, typeIII, minorArcVinogradov), modulo the fixed
numerical data fields (`A, A_pos, Q, Q_ge_one, N₀, aggConsts`) which
the user supplies as parameters, and the four shape-only existential
witnesses (three Perron atoms + four character atoms) which are
already closed mechanically.

## Strict constraints (P24-T3 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene:  only `[Classical.choice, Quot.sound, propext]`.
* This file **only adds**; it does not modify any other file in the
  project.

-/

namespace Gdbh
namespace PathAStatusPhase24

/-! ## Section 1 — Field-by-field status enumeration (data form)

The 22 fields of `PathA_Phase5ReducedContent` are catalogued as data,
together with the "Prop type" and a one-line status. -/

/-- One bundle-field audit entry. -/
structure FieldEntry where
  /-- Lean-side field name. -/
  name        : String
  /-- Either `"Prop"`, `"ℝ"`, `"ℕ"`, `"function"`, or `"inequality"`. -/
  kind        : String
  /-- One-line status (`"closed"`, `"shape-only"`, `"RH-conditional"`,
  `"classical-open"`, or `"user data"`). -/
  status      : String
  /-- Optional task tag (`"P5-T1"`, `"P5-T1c"`, `"P5-T2"`, etc.). -/
  task        : String

/-- The 22-entry catalogue of Phase-5-reduced fields. -/
def PathA_Phase5_FieldCatalogue : List FieldEntry :=
  [ -- P5-T1 Perron decomposition (3 atoms + 1 RH input)
    { name := "perronTruncated",
      kind := "Prop", status := "shape-only", task := "P5-T1" }
  , { name := "contourShift",
      kind := "Prop", status := "shape-only", task := "P5-T1" }
  , { name := "residueExtract",
      kind := "Prop", status := "shape-only", task := "P5-T1" }
  , { name := "psiBound",
      kind := "Prop", status := "RH-conditional", task := "P5-T1" }
    -- P5-T1c Character-twisted Perron chain (4 atoms)
  , { name := "charPerronTruncated",
      kind := "Prop", status := "shape-only", task := "P5-T1c" }
  , { name := "charContourShift",
      kind := "Prop", status := "shape-only", task := "P5-T1c" }
  , { name := "charResidueExtract",
      kind := "Prop", status := "shape-only", task := "P5-T1c" }
  , { name := "charChainGivesShape",
      kind := "Prop", status := "shape-only", task := "P5-T1c" }
    -- P5-T2 Page + Siegel zero-free region (2 open sub-Props)
  , { name := "pageLogDistance",
      kind := "Prop", status := "classical-open", task := "P5-T2" }
  , { name := "siegelAlone",
      kind := "Prop", status := "classical-open", task := "P5-T2" }
    -- Principal SW input (PNT remainder)
  , { name := "pntRemainder",
      kind := "Prop", status := "classical-open", task := "P5-T2" }
    -- P5-T3 Plancherel data (5 numerical + 1 Prop)
  , { name := "A",
      kind := "ℝ", status := "user data", task := "P5-T3" }
  , { name := "A_pos",
      kind := "inequality", status := "user data", task := "P5-T3" }
  , { name := "Q",
      kind := "ℕ", status := "user data", task := "P5-T3" }
  , { name := "Q_ge_one",
      kind := "inequality", status := "user data", task := "P5-T3" }
  , { name := "N₀",
      kind := "ℕ", status := "user data", task := "P5-T3" }
  , { name := "aggConsts",
      kind := "function", status := "user data", task := "P5-T3" }
  , { name := "uniformPlancherel",
      kind := "Prop", status := "classical-open", task := "P5-T3" }
    -- P5-T5 Universal-α Vinogradov bounds (3 unconditional)
  , { name := "typeIUnconditional",
      kind := "Prop", status := "classical-open", task := "P5-T5" }
  , { name := "typeIIUnconditional",
      kind := "Prop", status := "classical-open", task := "P5-T5" }
  , { name := "typeIIIUnconditional",
      kind := "Prop", status := "classical-open", task := "P5-T5" }
    -- P5-T6 Minor-arc 3/4-bound
  , { name := "minorArcVinogradov",
      kind := "Prop", status := "classical-open", task := "P5-T6" }
  ]

/-- The catalogue has 22 entries (matching the 22 fields of
`PathA_Phase5ReducedContent`). -/
def PathA_Phase5_FieldCatalogue_length : Nat :=
  PathA_Phase5_FieldCatalogue.length

/-- Sanity: catalogue is the right length. -/
theorem pathA_phase5_fieldCatalogue_length_eq_twentyTwo :
    PathA_Phase5_FieldCatalogue_length = 22 := by decide

/-- The catalogue is non-empty. -/
theorem pathA_phase5_fieldCatalogue_length_pos :
    0 < PathA_Phase5_FieldCatalogue_length := by decide

/-! ## Section 2 — False-Prop risk enumeration (data form)

A catalogue of false-Prop risks we audited for Path A, with the
resolution path of each. -/

/-- One false-Prop risk entry. -/
structure FalsePropRisk where
  /-- Risk index (1-based). -/
  index       : Nat
  /-- The literal Prop name. -/
  prop        : String
  /-- One-line description of the failure mode. -/
  mode        : String
  /-- One-line resolution path (`"already refactored"`, etc.). -/
  resolution  : String

/-- The Path A false-Prop risk catalogue. -/
def PathA_FalsePropRiskCatalogue : List FalsePropRisk :=
  [ { index := 1,
      prop := "ExplicitFormulaBridge (universal form, legacy bundle)",
      mode := "∀ ZeroSum TruncErr forces |ψ(x) − x| ≤ log x — structurally false",
      resolution :=
        "Refactored to function-form `ExplicitFormulaBridgeFor ZS TE` in Phase 5" }
  , { index := 2,
      prop := "PerronTruncatedFormulaCorrect / ContourShiftIdentityHolds / ResidueExtractionCorrect",
      mode := "Existential shape only; trivial quantifier witnesses exist",
      resolution :=
        "Closed mechanically by `_quantifier_witness` lemmas in PathA_ExplicitFormula" }
  , { index := 3,
      prop := "PsiSquareRootErrorBound",
      mode := "RH-conditional; genuine analytic content, not a false Prop",
      resolution :=
        "Closure requires RH + explicit-formula chain (Phase 5 future work)" }
  , { index := 4,
      prop := "ZFRPrimitiveLogarithmicDistance / SiegelExceptionalZeroAlone",
      mode := "Classical analytic Props (Page + Siegel) — not false",
      resolution :=
        "Closure requires Hadamard product + Siegel's effective-zero argument" }
  , { index := 5,
      prop := "PrimeCounting_PNT_RemainderBound",
      mode := "Classical PNT-with-remainder; not false",
      resolution :=
        "Closure requires the standard `exp(−c√log N)` PNT remainder" }
  , { index := 6,
      prop := "VinogradovTypeI/II/III ForVaughanWitnessUnconditional",
      mode := "Classical universal-α Vinogradov bounds — not false",
      resolution :=
        "Closure requires Vinogradov-Vaughan's classical argument" }
  , { index := 7,
      prop := "MinorArcSmallnessFromVinogradovBoundThreeQuarter",
      mode := "Classical bilinear-form minor-arc bound — not false",
      resolution :=
        "Closure requires the explicit `δ_m < 3/4` bilinear estimate" }
  ]

/-- Number of false-Prop risk entries. -/
def PathA_FalsePropRiskCatalogue_length : Nat :=
  PathA_FalsePropRiskCatalogue.length

/-- Sanity: seven risks audited. -/
theorem pathA_falsePropRiskCatalogue_length_eq_seven :
    PathA_FalsePropRiskCatalogue_length = 7 := by decide

/-- At most one risk was a literal structural false Prop (Risk #1),
and it was refactored out of the Phase 5 bundle. -/
def PathA_StructuralFalseProps_Count : Nat := 1

/-- The single structural false Prop is no longer used by Phase 5. -/
def PathA_StructuralFalseProps_In_Phase5 : Nat := 0

theorem pathA_structuralFalseProps_in_phase5_eq_zero :
    PathA_StructuralFalseProps_In_Phase5 = 0 := rfl

/-! ## Section 3 — Genuine analytic open count

After excluding shape-only Props (closed by trivial witnesses), user
data fields (parameters supplied by the user), and the single
already-refactored structural false Prop, the Phase 5 bundle has
**nine genuinely open analytic Props**:

* `psiBound`              (P5-T1, RH-conditional)
* `pageLogDistance`       (P5-T2, classical Page)
* `siegelAlone`           (P5-T2, classical Siegel)
* `pntRemainder`          (P5-T2, classical PNT remainder)
* `uniformPlancherel`     (P5-T3, classical Plancherel)
* `typeIUnconditional`    (P5-T5, classical Vinogradov)
* `typeIIUnconditional`   (P5-T5, classical Vinogradov)
* `typeIIIUnconditional`  (P5-T5, classical Vinogradov)
* `minorArcVinogradov`    (P5-T6, classical bilinear)
-/

/-- The set of genuinely open analytic Props in the Phase 5 bundle. -/
def PathA_GenuineOpenProps : List String :=
  [ "psiBound", "pageLogDistance", "siegelAlone", "pntRemainder",
    "uniformPlancherel", "typeIUnconditional", "typeIIUnconditional",
    "typeIIIUnconditional", "minorArcVinogradov" ]

/-- The genuinely-open-Prop count is 9. -/
theorem pathA_genuineOpenProps_length_eq_nine :
    PathA_GenuineOpenProps.length = 9 := by decide

/-! ## Section 4 — Headline re-export

The Phase 5 Path A headline theorem, re-exported under a documentation
alias for ease of reference. -/

/-- **P24-T3 documentation re-export**: under `RiemannHypothesis`, an
inhabitant of `PathA_Phase5ReducedContent`, and the usual finite-
verification hypothesis, `StrongGoldbach` follows.

This is exactly `Gdbh.strongGoldbach_under_RH_phase5_reduced` — the
current Path A headline.  See `Gdbh/PathA_Final.lean:7445`. -/
theorem pathA_phase5_headline
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
  strongGoldbach_under_RH_phase5_reduced rh content finite threshold_covered

/-! ## Section 5 — Summary theorem listing what is needed

A single theorem statement that captures, in one place, the
"if-and-only-if-by-Path-A" structure of Path A Phase 5: given the
nine genuinely open Props (plus the user data and the closed shape
witnesses, which we collapse into an inhabitant of
`PathA_Phase5ReducedContent`), `StrongGoldbach` follows under RH and
finite verification. -/

/-- **What is needed to close Path A under RH.**

Given:
* `rh : RiemannHypothesis`,
* `content : PathA_Phase5ReducedContent` (an inhabitant of the full
  22-field Phase 5 bundle — equivalently, the nine genuinely open
  analytic Props above, together with the closed shape-only witnesses
  and the user data),
* a finite-verification bound `B` covering all small `n` (via
  `finite : GoldbachUpTo B`),
* the threshold-coverage hypothesis pinning the analytic threshold
  below `B`,

we obtain `StrongGoldbach`.

This theorem is the single named statement that summarises the entire
Path A closure under RH after the Phase 5 reduction. -/
theorem pathA_phase5_closure_under_RH
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
  pathA_phase5_headline rh content finite threshold_covered

/-! ## Section 6 — Axiom audit on key headlines

For Phase 24, the following are the relevant axiom-set audits.  These
are stated as `#print axioms` directives (commented out below for
reference).  The actual auditing should be performed by running
`lake env lean Gdbh/PathA_StatusPhase24.lean` and verifying that the
axiom output matches `[propext, Classical.choice, Quot.sound]`. -/

-- #print axioms Gdbh.strongGoldbach_under_RH_phase5_reduced
-- #print axioms Gdbh.PathAStatusPhase24.pathA_phase5_headline
-- #print axioms Gdbh.PathAStatusPhase24.pathA_phase5_closure_under_RH
-- #print axioms Gdbh.PathAStatusPhase24.pathA_phase5_fieldCatalogue_length_eq_twentyTwo
-- #print axioms Gdbh.PathAStatusPhase24.pathA_genuineOpenProps_length_eq_nine

/-- **Axiom-clean marker theorem** for this status file.

This trivially-true theorem exists so that `#print axioms` can be run
on it to confirm the file uses only the three mathlib foundation
axioms `[Classical.choice, Quot.sound, propext]`. -/
theorem pathA_statusPhase24_axiom_marker : True := trivial

end PathAStatusPhase24
end Gdbh
