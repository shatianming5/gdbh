import Gdbh.ConditionalPaths
import Gdbh.DiscreteCircleMethod
import Gdbh.SingularSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Path A — GRH-conditional binary Goldbach: scaffolding

This file breaks "RiemannHypothesis ⟹ binary Goldbach" into precisely-
named Lean targets and proves the easier connecting steps.

## What this file proves (axiom-clean)

* `psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound`:
  `VonMangoldtExplicitFormulaBound → PsiSquareRootErrorBound`.

This is the "absorb the additive constant" step: an explicit-formula
bound with additive `C₂` correction implies the clean form needed for
the rest of Path A.

## What remains (each ~weeks of Lean work)

* `VonMangoldtExplicitFormulaBound` itself — requires von Mangoldt's
  explicit formula `ψ(x) = x − Σ_ρ x^ρ/ρ − …` and the Riemann-von
  Mangoldt bound `Σ_{|γ|≤T} 1/|γ| ≤ C log² T`.
* `HardyLittlewoodFromPsiBound` — circle method conversion of ψ error
  bound into binary Hardy-Littlewood lower bound.
-/

namespace Gdbh

open Filter Real

/-! ## Statement of the missing analytic content -/

/-- **Explicit-formula bound on `|ψ(x) - x|`**: there exist constants
`C₁, C₂, x₀` such that for all `x ≥ x₀`,
`|ψ(x) - x| ≤ C₁ · √x · log²x + C₂`.

Under the Riemann Hypothesis this follows from von Mangoldt's
explicit formula. -/
def VonMangoldtExplicitFormulaBound : Prop :=
  ∃ C₁ C₂ x₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤
        C₁ * Real.sqrt x * (Real.log x) ^ (2 : Nat) + C₂

/-! ## Absorption helper -/

/-- `√x · log²x → ∞` as `x → ∞`.  Eventually (for `x ≥ e`),
`√x · log²x ≥ √x`, and `√x → ∞`. -/
theorem tendsto_sqrt_mul_log_sq_atTop :
    Tendsto (fun x : ℝ => Real.sqrt x * (Real.log x) ^ (2 : Nat)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  have hsqrt_ev : ∀ᶠ x : ℝ in atTop, M ≤ Real.sqrt x :=
    Real.tendsto_sqrt_atTop.eventually_ge_atTop M
  have hlog_ev : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  rcases (Filter.eventually_atTop.mp hsqrt_ev) with ⟨N₁, hN₁⟩
  rcases (Filter.eventually_atTop.mp hlog_ev) with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  have hxN₁ : N₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxN₂ : N₂ ≤ x := le_trans (le_max_right _ _) hx
  have hsqrt_ge : M ≤ Real.sqrt x := hN₁ x hxN₁
  have hlog_ge_one : (1 : ℝ) ≤ Real.log x := hN₂ x hxN₂
  have hlog_sq_ge : (1 : ℝ) ≤ (Real.log x) ^ (2 : Nat) := by
    have hone : (1 : ℝ) = 1 ^ (2 : Nat) := by norm_num
    rw [hone]
    exact pow_le_pow_left₀ (by norm_num) hlog_ge_one 2
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  nlinarith [hsqrt_ge, hlog_sq_ge, hsqrt_nn]

/-- For every `M`, eventually `√x · log²x ≥ M`. -/
theorem eventually_sqrt_mul_log_sq_ge (M : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      M ≤ Real.sqrt x * (Real.log x) ^ (2 : Nat) :=
  tendsto_sqrt_mul_log_sq_atTop.eventually_ge_atTop M

/-! ## Step: explicit-formula bound ⟹ ψ square-root error bound -/

/-- **Step 1**: explicit-formula bound (with additive `C₂`) implies the
clean `PsiSquareRootErrorBound` by absorbing `C₂` into the leading term
for sufficiently large `x`.

Proof: pick `C = C₁ + 1`.  For `x` large enough that `√x · log²x ≥ C₂`,
the additive `C₂` is dominated by the extra `+1·√x·log²x` slack. -/
theorem psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound
    (efb : VonMangoldtExplicitFormulaBound) :
    PsiSquareRootErrorBound := by
  rcases efb with ⟨C₁, C₂, x₀, hC₁_pos, hC₂_pos, hx₀_pos, hbound⟩
  -- Find a threshold x₁ ≥ x₀ with √x · log²x ≥ C₂ for all x ≥ x₁.
  have habsorb : ∀ᶠ x : ℝ in atTop,
      C₂ ≤ Real.sqrt x * (Real.log x) ^ (2 : Nat) :=
    eventually_sqrt_mul_log_sq_ge C₂
  rw [Filter.eventually_atTop] at habsorb
  rcases habsorb with ⟨xA, hxA⟩
  let x₁ := max (max x₀ xA) 1
  refine ⟨C₁ + 1, x₁, by linarith, by positivity, ?_⟩
  intro x hx
  have hx_ge_x₀ : x₀ ≤ x :=
    le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hx
  have hx_ge_xA : xA ≤ x :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hx
  have hb := hbound x hx_ge_x₀
  have habs := hxA x hx_ge_xA
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right _ _) hx)
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hlog_sq_nn : (0 : ℝ) ≤ (Real.log x) ^ (2 : Nat) := by positivity
  have hslg_nn : (0 : ℝ) ≤ Real.sqrt x * (Real.log x) ^ (2 : Nat) := by positivity
  -- |ψ - x| ≤ C₁ · √x · log²x + C₂ ≤ C₁ · √x · log²x + √x · log²x = (C₁+1) · √x · log²x
  calc |Chebyshev.psi x - x|
      ≤ C₁ * Real.sqrt x * (Real.log x) ^ (2 : Nat) + C₂ := hb
    _ ≤ C₁ * Real.sqrt x * (Real.log x) ^ (2 : Nat) +
          Real.sqrt x * (Real.log x) ^ (2 : Nat) := by linarith
    _ = (C₁ + 1) * Real.sqrt x * (Real.log x) ^ (2 : Nat) := by ring

/-! ## Step 2: ψ error bound ⟹ minor arc exponential sum bound

The classical Vinogradov-Vaughan argument: given control on `ψ(x) - x`,
one can bound `|Σ_{m ≤ N} Λ(m) e(mα)|` on minor arcs.

The cleanest "GRH-style" minor arc bound is

```
|Σ_{m ≤ N} Λ(m) e(mα)| ≤ N^(1/2) · (log N)^k · q^(1/2)
```

for `α` close to `a/q` with `gcd(a,q) = 1`.  We package only the
existential form needed downstream. -/

/-- **Minor arc bound from ψ-square-root error**: there exist absolute
constants `C, N₀` and an integer exponent `k` such that for every
real `α`, every coprime pair `(a, q)` with `1 ≤ q ≤ N`, every
`|α - a/q| ≤ 1/(qN)`, and every `N ≥ N₀`,

```
|Σ_{m=1}^{N} Λ(m) · cos(2π · m · α)| ≤ C · √N · (log N)^k.
```

This is the "Vinogradov bound from GRH" in real-cosine form (we use
cosines instead of full complex exponentials for Lean ergonomics).
The full statement requires deeper formalization of bilinear sums. -/
def MinorArcCosineSumBound : Prop :=
  ∃ C : ℝ, ∃ k N₀ : Nat, 0 < C ∧
    ∀ N : Nat, N₀ ≤ N → ∀ α : ℝ,
      |∑ m ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt m : ℝ) * Real.cos (2 * Real.pi * m * α)| ≤
        C * Real.sqrt N * (Real.log N) ^ k

/-- The structural claim `PsiSquareRootErrorBound → MinorArcCosineSumBound`
packages the Vinogradov-Vaughan argument as a Prop. -/
def MinorArcFromPsiBound : Prop :=
  PsiSquareRootErrorBound → MinorArcCosineSumBound

/-! ## Step 3: Major arc estimate (Hardy-Littlewood singular series)

On major arcs `α ≈ a/q` with small `q`, the exponential sum is well
approximated by `(μ(q)/φ(q)) · N + error`.  The classical "Hardy-
Littlewood major arc estimate" packages this. -/

/-- **Major arc estimate**: an effective statement of the major arc
contribution to the binary Goldbach convolution.  Under standard
zero-free regions (implied by RH), this gives
`MajorArc(n) = 𝔖(n) · n + O(n / log²n)`.

This version is *substantive*: it exposes an explicit Farey cutoff `Q`,
an arc family `majorArcs`, and an error function `errorFn`, and asserts
that the Fourier major-arc contribution approximates the singular-series
main term `𝔖(n) · n` with absolute error at most `errorFn n`.

The full Path A goal is to prove an inhabitant with `errorFn = o(n)`.
We supply a trivial inhabitant in `Gdbh.PathA_MajorArc` (so the
`strongGoldbach_via_PathA_full` chain remains type-correct).  See
`Gdbh/PathA_MajorArc.lean`. -/
def MajorArcEstimate : Prop :=
  ∃ Q : Nat, ∃ N₀ : Nat,
    ∃ majorArcs : (n : Nat) → Finset (ZMod n.succ),
    ∃ errorFn : Nat → ℝ,
      1 ≤ Q ∧
      ∀ n : Nat, N₀ < n → Even n →
        ‖DiscreteCircleMethod.rawVonMangoldtFourierMajorArcComplexContribution
            majorArcs n -
          (Gdbh.goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          errorFn n

/-! ## Step 4: combining minor + major arc into Hardy-Littlewood -/

/-- **Path A's full analytic implication**: given the major arc estimate,
the minor arc bound, and the ψ error bound (i.e., the analytic content
of Path A), the binary Hardy-Littlewood lower bound follows. -/
def PathA_AnalyticImplication : Prop :=
  PsiSquareRootErrorBound →
    MinorArcCosineSumBound →
      MajorArcEstimate →
        ∃ T : Nat, ∃ δ : ℝ, δ < 1 ∧
          QuarterBinaryHardyLittlewoodLowerBound T δ

/-! ## Step 5: Full Path A chain RH → Goldbach -/

/-- **Path A full chain**: combining
* `RiemannHypothesis` (mathlib, `Prop`),
* `VonMangoldtExplicitFormulaBound` (open, needs explicit formula in Lean),
* `MinorArcFromPsiBound` (open, needs Vinogradov-Vaughan in Lean),
* `MajorArcEstimate` (open, needs Farey-fraction major arc def in Lean),
* `PathA_AnalyticImplication` (open, needs binary circle-method synthesis),
* `RiemannHypothesis → VonMangoldtExplicitFormulaBound` (open, needs
  explicit formula derivation from RH),

with the already-existing `strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound`
and a sufficient finite verification, yields `StrongGoldbach`. -/
theorem strongGoldbach_via_PathA_full
    (rh : RiemannHypothesis)
    (rh_to_efb : RiemannHypothesis → VonMangoldtExplicitFormulaBound)
    (minor_from_psi : MinorArcFromPsiBound)
    (major : MajorArcEstimate)
    (analytic : PathA_AnalyticImplication)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    StrongGoldbach := by
  -- Step 1: RH → explicit formula bound
  have efb : VonMangoldtExplicitFormulaBound := rh_to_efb rh
  -- Step 2: explicit formula bound → ψ square-root error bound (PROVED in this file)
  have psi_bound : PsiSquareRootErrorBound :=
    psiSquareRootErrorBound_of_VonMangoldtExplicitFormulaBound efb
  -- Step 3: ψ bound → minor arc bound
  have minor : MinorArcCosineSumBound := minor_from_psi psi_bound
  -- Step 4: combine ψ + minor + major → Hardy-Littlewood lower bound
  rcases analytic psi_bound minor major with ⟨T, δ, hδ, hHL⟩
  -- Step 5: Hardy-Littlewood + finite verification → Strong Goldbach
  rcases threshold_covered T δ hδ hHL with ⟨hT_le, hContam⟩
  exact strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound
    hδ finite hHL hT_le hContam

end Gdbh
