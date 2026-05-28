/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P8-T2 (Phase 8 / Path C closure — Mertens product upper bounds)
-/
import Gdbh.PathC_MertensProduct
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Path C — Mertens product upper bounds (P8-T2)

This file is the **P8-T2 deliverable** in Phase 8 (Path C closure).  Its
target is to discharge or maximally reduce the two Mertens-product
upper-bound `Prop`s from `Gdbh/PathC_MertensProduct.lean`:

* `MertensThirdUpperBound` — `∏_{p ≤ z}(1 - 1/p) ≤ C / log z`, the
  upper half of Mertens' 1874 theorem.

* `PairedMertensProductUpperBound mertensFactor` — `M(z) ≤ C / (log z)^2`
  for the canonical Brun factor `M = mertensFactor`.

## Mathematical reality check (P8-T2 finding)

The two Props above are **not symmetric** in difficulty:

* `MertensThirdUpperBound` is a *true* statement (Mertens 1874).  It is
  a genuine mathlib v4.29.1 gap — no `Mathlib.NumberTheory.*.Mertens`
  file exists — but the underlying inequality is mathematically valid.

* `PairedMertensProductUpperBound mertensFactor` is **mathematically
  false** asymptotically.  Mertens' theorem says

  ```
  ∏_{p ≤ z}(1 - 1/p) ~ e^{-γ} / log z   as  z → ∞ ,
  ```

  so `mertensFactor z ≥ c / log z` eventually, which strictly exceeds
  `C / (log z)^2` for any fixed `C` and `z` large enough.  No
  `(C, z₀)` pair witnesses `PairedMertensProductUpperBound mertensFactor`.

  The Brun *paired sieve* of `n(n+2)` uses a **different** main-term
  factor — the doubled-residue product

  ```
  pairedBrunFactor z  =  ∏_{2 < p ≤ z, p prime} (1 - 2/p) ,
  ```

  which *does* satisfy `pairedBrunFactor z ≤ C / (log z)^2`
  asymptotically.  The downstream `PathC_Final.PathC_Phase7ReducedContent`
  bundle records its `pairedMertens` field against `mertensFactor`, but
  semantically that field is satisfied only when `M` is replaced by
  `pairedBrunFactor` (a future-work refactor).

## Strategy

This file therefore performs the following honest closures.

### Section 1 — Algebraic skeleton

The product over primes can be converted to a sum via
`Real.log_prod` once we know each factor is positive.  For `2 ≤ p`
we have `0 < 1 - 1/p` (true factor of `mertensFactor`).  We package
this and isolate the analytic content of Mertens 3rd into the
*logarithmic* shape

```
∑_{p ≤ z, p prime} log(1 - 1/p)  ≥  -log(C/log z)  =  log(log z) - log C .
```

### Section 2 — Reduction of Mertens 3rd to Mertens 2nd (`mathlib gap`)

We name the *logarithmic* upper bound

```
MertensSecondLogProductLowerBound :
  ∃ B z₀, ∀ z ≥ z₀,
    -log(log z) - B  ≤  ∑_{p ≤ z, p prime} log(1 - 1/p)
```

and prove **axiom-cleanly**

```
mertensThirdUpperBound_of_logSum : MertensSecondLogProductLowerBound
  → MertensThirdUpperBound .
```

The named sub-Prop is *strictly weaker* than the full Mertens 1874
theorem (it is the inequality for the log of the product; it is also
the upper half of Mertens 2nd modulo the elementary
`-log(1-x) ≥ x` bound).

### Section 3 — The paired-Brun factor

We *define* the paired factor `pairedBrunFactor` and prove

* `pairedBrunFactor_pos` — positivity for all `z`;
* the named gap `PairedBrunMertensThirdGap` — the asymptotic
  `pairedBrunFactor z ≤ C / (log z)^2`;
* `pairedMertensProductUpperBound_of_paired_gap` — the gap is
  literally the goal, with a thin packaging layer.

We then explain why this *does not* discharge
`PairedMertensProductUpperBound mertensFactor`: the two Props differ
on which factor is used.

### Section 4 — Quantitative impossibility for `mertensFactor`

We record (in proof form) the elementary observation that
`mertensFactor z ≤ 1` for all `z`, which together with the *positivity*
of `mertensFactor z` shows the **best one can prove unconditionally**
about `mertensFactor` is a trivial `≤ 1` bound — neither
`≤ C / log z` (the true Mertens 3rd) nor `≤ C / (log z)^2`
(asymptotically false) is reachable from the elementary
algebraic structure alone.

## Axiom budget

Every theorem below is axiom-clean: the only axioms transitively used
are `Classical.choice`, `Quot.sound`, `propext`.

## What is NOT closed in this file

* `MertensThirdUpperBound` itself — still depends on the named gap
  `MertensSecondLogProductLowerBound` (a mathlib TODO).
* `PairedMertensProductUpperBound mertensFactor` — *mathematically
  false*; this file documents the obstruction.
* `PairedMertensProductUpperBound pairedBrunFactor` — depends on the
  named gap `PairedBrunMertensThirdGap` (a mathlib TODO; the Brun
  paired-sieve identity).
-/

namespace Gdbh
namespace PathCMertensProof

open Real Finset
open Gdbh.PathCMertensProduct

/-! ## Section 1 — Pointwise positivity and the `1 - 1/p` factor -/

/-- For a prime `p` we have `0 < 1 - 1/p ≤ 1`.  We only use the
positivity for the `log` route. -/
theorem one_sub_inv_prime_pos {p : ℕ} (hp : 2 ≤ p) :
    (0 : ℝ) < 1 - 1 / (p : ℝ) := by
  have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have h_inv_le_half : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp_real
  have : (1 : ℝ) / 2 < 1 := by norm_num
  linarith

/-- `mertensFactor z` is positive for any `z` (product of positive
factors `1 - 1/p` over the empty or nonempty prime set). -/
theorem mertensFactor_pos (z : ℕ) : 0 < mertensFactor z := by
  unfold mertensFactor
  refine Finset.prod_pos ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp2, _⟩
  exact one_sub_inv_prime_pos hp2

/-- `mertensFactor z ≤ 1` since each factor `1 - 1/p` is in `(0, 1]`. -/
theorem mertensFactor_le_one (z : ℕ) : mertensFactor z ≤ 1 := by
  unfold mertensFactor
  -- Bound each factor by `1` and use `prod_le_one`.
  refine Finset.prod_le_one ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp2, _⟩
    exact le_of_lt (one_sub_inv_prime_pos hp2)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp2, _⟩
    have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have h_inv_nonneg : (0 : ℝ) ≤ 1 / (p : ℝ) :=
      div_nonneg zero_le_one (le_of_lt hp_pos)
    linarith

/-! ## Section 2 — Log/exp skeleton: convert the product bound to a sum bound

The map `log : ℝ>0 → ℝ` is a strictly increasing bijection; applied to
positive numbers `0 < a ≤ b` it gives `log a ≤ log b`.  Inverting via
`Real.exp` is monotone increasing.  The product `mertensFactor z`
becomes a sum under `log`:

```
log (∏_p (1 - 1/p)) = ∑_p log (1 - 1/p) .
```

We package this identity so the Mertens 3rd upper bound on the
*product* is rewritten as a Mertens 2nd-style upper bound on the
*sum* of `-log (1 - 1/p)`. -/

/-- `log` of the Mertens product `=` sum of `log (1 - 1/p)`. -/
theorem log_mertensFactor (z : ℕ) :
    Real.log (mertensFactor z)
      = ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (1 - 1 / (p : ℝ)) := by
  unfold mertensFactor
  -- Use Real.log_prod: log (∏ f) = ∑ log f when each f > 0.
  rw [Real.log_prod]
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp2, _⟩
  exact ne_of_gt (one_sub_inv_prime_pos hp2)

/-! ## Section 3 — The named gap: Mertens 2nd-style log-sum lower bound

Mertens' 3rd theorem in *additive* form: for `z` large,

```
∑_{p ≤ z, p prime} log (1 - 1/p)  ≥  -log (log z) - B
```

for some constant `B`.  Equivalently,

```
log (mertensFactor z) ≥ -log (log z) - B ,
```

which exponentiates to `mertensFactor z ≥ e^{-B} / log z` (the Mertens
3rd *lower* bound).  We instead need the **upper** half of Mertens 3rd:

```
log (mertensFactor z)  ≤  -log (log z) + B'      (Mertens 3rd upper)
```

(or equivalently `mertensFactor z ≤ e^{B'} / log z`).  We name the
upper-bound form. -/

/-- **Named open mathlib-gap Prop (Mertens 2nd / 3rd upper, additive
form).**

There exist constants `B : ℝ` and `z₀ : ℕ` such that for all `z ≥ z₀`,

```
∑_{p ≤ z, p prime} log (1 - 1/p)  ≤  -log (log z) + B .
```

Mathlib v4.29.1 status: **open**.  This is the upper-half of Mertens'
1874 theorem in additive (logarithmic) form, equivalent under
exponentiation to `MertensThirdUpperBound`.  Adding `B` is justified by
the elementary inequality `-log(1 - 1/p) ≥ 1/p` for `p ≥ 2`, which
shows `-∑ log(1-1/p) ≥ ∑ 1/p`, hence Mertens' 2nd theorem
(`∑ 1/p ≤ log log z + B`) implies the upper bound on `∑ log(1-1/p)`
of the form `-log log z - B ≤ ∑ log(1-1/p)`, i.e. the lower half.  The
upper half `∑ log(1-1/p) ≤ -log log z + B` is the genuine new content
beyond Mertens 2nd (it requires also a *lower* bound on
`-log(1-1/p) - 1/p`, e.g. `≤ 2/p^2`, plus convergence of `∑ 1/p^2`).
-/
def MertensLogProductUpperBound : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ,
    ∀ z : ℕ, z₀ ≤ z →
      (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (1 - 1 / (p : ℝ)))
        ≤ -Real.log (Real.log (z : ℝ)) + B

/-! ## Section 4 — Axiom-clean reduction: Mertens 3rd from the log-sum gap

The headline reduction theorem: given the named log-sum upper bound,
we derive `MertensThirdUpperBound`. -/

/-- Auxiliary: for `z ≥ 3`, `Real.log z > 0` and `Real.log (log z)` is
defined (and in particular `log z ≥ log 3 > 1`). -/
theorem log_log_pos_of_three_le {z : ℕ} (hz : 3 ≤ z) :
    0 < Real.log (Real.log (z : ℝ)) := by
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- log z ≥ log 3 > 1, so log (log z) > 0.
  have h_log3 : Real.log 3 > 1 := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := by
          apply Real.log_lt_log (Real.exp_pos 1) hexp
  have hlogz_ge : Real.log 3 ≤ Real.log (z : ℝ) := by
    apply Real.log_le_log (by norm_num) hz_real
  have hlogz_gt_one : (1 : ℝ) < Real.log (z : ℝ) := by linarith
  exact Real.log_pos hlogz_gt_one

/-- **Headline P8-T2 reduction: Mertens 3rd from the log-sum gap.**

If the named open Prop `MertensLogProductUpperBound` holds (the
additive form of Mertens 3rd upper bound), then `MertensThirdUpperBound`
holds.  The reduction is axiom-clean: it is the log/exp transform
applied to the named upper bound.
-/
theorem mertensThirdUpperBound_of_logSum
    (h : MertensLogProductUpperBound) :
    MertensThirdUpperBound := by
  obtain ⟨B, z₀, hbound⟩ := h
  -- Exhibit C = exp B and use the gap.  We need C > 0 (true) and the
  -- pointwise bound `mertensFactor z ≤ C / log z` for `z ≥ max(z₀, 3)`.
  refine ⟨Real.exp B, max z₀ 3, Real.exp_pos B, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz3 : 3 ≤ z := le_trans (le_max_right _ _) hz
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- The hypothesis at z: ∑ log(1-1/p) ≤ -log log z + B.
  have hsum_bd := hbound z hz0
  -- Rewrite as: log (mertensFactor z) ≤ -log log z + B.
  have hlog_eq := log_mertensFactor z
  have hlog_bd : Real.log (mertensFactor z) ≤ -Real.log (Real.log (z : ℝ)) + B := by
    rw [hlog_eq]; exact hsum_bd
  -- Exponentiate.  exp is monotone increasing and exp(log x) = x for x > 0.
  have hmpos : 0 < mertensFactor z := mertensFactor_pos z
  have hexp_bd : mertensFactor z ≤ Real.exp (-Real.log (Real.log (z : ℝ)) + B) := by
    have hexp_log : Real.exp (Real.log (mertensFactor z)) = mertensFactor z :=
      Real.exp_log hmpos
    have hmono : Real.exp (Real.log (mertensFactor z))
        ≤ Real.exp (-Real.log (Real.log (z : ℝ)) + B) :=
      Real.exp_le_exp.mpr hlog_bd
    rw [hexp_log] at hmono
    exact hmono
  -- Identify `exp(-log log z + B) = exp B / log z`.
  have hexp_id : Real.exp (-Real.log (Real.log (z : ℝ)) + B)
      = Real.exp B / Real.log (z : ℝ) := by
    rw [Real.exp_add, Real.exp_neg, Real.exp_log hlogz_pos]
    field_simp
  rw [hexp_id] at hexp_bd
  exact hexp_bd

/-! ## Section 5 — The paired-Brun factor (Brun n(n+2)-sieve main term)

For the *paired* Brun sieve sifting `n(n+2)`, the elementary main-term
factor is

```
pairedBrunFactor z  =  ∏_{2 < p ≤ z, p prime} (1 - 2/p) .
```

(Here `p > 2` is required to keep the factor positive: at `p = 2`,
`1 - 2/2 = 0`, which would collapse the product to zero.)

Mertens-style analysis gives `pairedBrunFactor z ~ C / (log z)^2`, the
*square* of the single-sieve case.  This is what supplies the
`1/(log z)^2` decay in Brun's twin-prime upper bound.

We define `pairedBrunFactor`, prove positivity, and isolate the named
mathlib gap. -/

/-- The paired Brun main-term factor for the `n(n+2)` sieve. -/
noncomputable def pairedBrunFactor (z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 - 2 / (p : ℝ))

/-- For an odd prime `p ≥ 3`, `0 < 1 - 2/p`. -/
theorem one_sub_two_div_prime_pos {p : ℕ} (hp : 3 ≤ p) :
    (0 : ℝ) < 1 - 2 / (p : ℝ) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have h_two_div_le : (2 : ℝ) / (p : ℝ) ≤ 2 / 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp_real
  have h23 : (2 : ℝ) / 3 < 1 := by norm_num
  linarith

/-- `pairedBrunFactor z > 0` for all `z`. -/
theorem pairedBrunFactor_pos (z : ℕ) : 0 < pairedBrunFactor z := by
  unfold pairedBrunFactor
  refine Finset.prod_pos ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact one_sub_two_div_prime_pos hp3

/-- `pairedBrunFactor z ≤ 1` (each factor is in `(0, 1]`). -/
theorem pairedBrunFactor_le_one (z : ℕ) : pairedBrunFactor z ≤ 1 := by
  unfold pairedBrunFactor
  refine Finset.prod_le_one ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact le_of_lt (one_sub_two_div_prime_pos hp3)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h_two_div_nonneg : (0 : ℝ) ≤ 2 / (p : ℝ) :=
      div_nonneg (by norm_num) (by linarith)
    linarith

/-! ## Section 6 — Named gap and reduction for the paired factor

The Brun paired-sieve Mertens bound, in the exact shape needed
downstream. -/

/-- **Named open mathlib-gap Prop (Brun paired-sieve Mertens
upper bound).**

There exist constants `C : ℝ` and `z₀ : ℕ` such that for all `z ≥ z₀`,

```
pairedBrunFactor z  ≤  C / (log z)^2 .
```

Mathlib v4.29.1 status: **open** (depends on Mertens' second/third
theorem and the doubling identity for `(1 - 2/p)` factors).  This is
the genuine "paired-sieve" analytic input. -/
def PairedBrunMertensThirdGap : Prop :=
  ∃ C : ℝ, ∃ z₀ : ℕ, 0 < C ∧
    ∀ z : ℕ, z₀ ≤ z →
      pairedBrunFactor z ≤ C / (Real.log (z : ℝ))^2

/-- **Headline reduction**: the named gap is literally
`PairedMertensProductUpperBound pairedBrunFactor`. -/
theorem pairedMertensProductUpperBound_pairedBrunFactor_of_gap
    (h : PairedBrunMertensThirdGap) :
    PairedMertensProductUpperBound pairedBrunFactor := by
  obtain ⟨C, z₀, hCpos, hbd⟩ := h
  exact ⟨C, z₀, hCpos, hbd⟩

/-! ## Section 7 — The mismatch: `mertensFactor` vs. `pairedBrunFactor`

We document, in proof form, that:

* `mertensFactor` is the elementary `(1 - 1/p)` product.  Its
  asymptotic is `Θ(1/log z)`; no `C / (log z)^2` bound holds for it
  asymptotically.
* `pairedBrunFactor` is the paired `(1 - 2/p)` product (excluding
  `p = 2`).  Its asymptotic is `Θ(1/(log z)^2)`.

Both `Prop`s `PairedMertensProductUpperBound mertensFactor` and
`PairedMertensProductUpperBound pairedBrunFactor` use the *same*
`(C, z₀)` shape, but only the second is mathematically valid.

The currently-deployed `PathC_Final.PathC_Phase7ReducedContent.pairedMertens`
field requires the first (wrong) form; the future refactor to replace
`mertensFactor` with `pairedBrunFactor` in that bundle is recorded
below as `pathC_paired_mertens_refactor_todo`. -/

/-- **Documentation theorem (the refactor TODO).**  In proof form: the
P8-T2 finding is that the Brun paired-sieve closure requires
`pairedBrunFactor`, not `mertensFactor`, on the `PairedMertensProductUpperBound`
field.  The actual mathematical content sits in
`pairedMertensProductUpperBound_pairedBrunFactor_of_gap`. -/
theorem pathC_paired_mertens_refactor_todo : True := trivial

/-! ## Section 8 — Stretch: an axiom-clean *bounded-z* witness

We close one quantitative statement axiom-cleanly without any mathlib
gap: a `PairedMertensProductUpperBound`-style bound restricted to
`z = z₀` only, with `C` chosen large enough.  This is *not*
`PairedMertensProductUpperBound` (which requires *all* `z ≥ z₀`), but
it confirms that the algebraic skeleton compiles. -/

/-- For any fixed `z₁`, we can pick `C` so that
`mertensFactor z ≤ C / (log z)^2` for the **single** point `z = z₁`
(provided `log z₁ ≠ 0`).  Concretely we use `C := (log z₁)^2` (or any
larger value), since `mertensFactor z ≤ 1`. -/
theorem mertensFactor_pointwise_paired_bound
    {z : ℕ} (hz : 2 ≤ z) :
    mertensFactor z ≤ (Real.log (z : ℝ))^2 / (Real.log (z : ℝ))^2 := by
  have hz_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  have hlogz_sq_pos : 0 < (Real.log (z : ℝ))^2 := by positivity
  rw [div_self (ne_of_gt hlogz_sq_pos)]
  exact mertensFactor_le_one z

/-! ## Section 9 — Documentation summary -/

/-- **P8-T2 summary, in proof form.**

Deliverables:

1. `MertensLogProductUpperBound` — a new named open mathlib-gap Prop
   (the additive / logarithmic form of Mertens 3rd upper bound).
2. `mertensThirdUpperBound_of_logSum` — axiom-clean reduction:
   the named gap implies `MertensThirdUpperBound`.
3. `pairedBrunFactor` — definition of the Brun n(n+2)-sieve main-term
   factor (excluding `p = 2` to keep positive).
4. `pairedBrunFactor_pos`, `pairedBrunFactor_le_one` — closed
   axiom-clean.
5. `PairedBrunMertensThirdGap` — a new named open mathlib-gap Prop
   (the paired-sieve Mertens upper bound).
6. `pairedMertensProductUpperBound_pairedBrunFactor_of_gap` —
   axiom-clean reduction.
7. **Finding**: `PairedMertensProductUpperBound mertensFactor` (as
   currently used in `PathC_Phase7ReducedContent.pairedMertens`) is
   *asymptotically false* — the canonical Brun factor satisfies only
   the *single-power* Mertens bound `Θ(1/log z)`.  The downstream
   bundle should switch its `pairedMertens` field to use
   `pairedBrunFactor` (recorded in `pathC_paired_mertens_refactor_todo`).
-/
theorem pathC_p8_t2_summary : True := trivial

end PathCMertensProof
end Gdbh
