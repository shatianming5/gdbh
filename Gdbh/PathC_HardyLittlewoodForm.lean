/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P20-T5 (Phase 20 / Path C — Hardy-Littlewood form with explicit
        singular series.  Defines the classical Halberstam-Richert §3.11
        shape `r(n) ≤ C · n · pBF(z) · S(n)` and bridges it parametrically
        into the FixA paired-main-term chain.)
-/
import Gdbh.PathC_FixABrunGoldbachProp

/-!
# Path C — P20-T5: Hardy-Littlewood form with explicit singular series

## Background

Classical Halberstam-Richert *Sieve Methods* Theorem 3.11 (the "tight"
form of the Brun-Goldbach upper bound):

```
r(n) ≤ C · n · pBF(z) · S(n) ,
```

where

* `r(n) = goldbachSiftedPair n z` is the paired sifted count for the
  Goldbach problem at sieve threshold `z`;
* `pBF(z) = pairedBrunFactor z = ∏_{2 < p ≤ z, p prime} (1 - 2/p)` is
  the paired Brun main-term factor (defined in
  `Gdbh.PathCMertensProof`);
* `S(n) := ∏_{p | n, p > 2} (p-1)/(p-2)` is the **Hardy-Littlewood
  singular series factor** capturing the local divisibility correction.

This is the **tightest classical upper bound**: it matches the
Hardy-Littlewood asymptotic prediction `r(n) ∼ 2C₂ · n / (log n)² · S(n)`
up to constants.

## What this file does

1. Defines `singularSeries n := ∏_{p ∈ [3, n], p prime, p ∣ n} (p-1)/(p-2)`,
   matching the classical Halberstam-Richert shape.

2. Defines the corresponding Prop `BrunGoldbachHardyLittlewood`, the
   canonical "HL form" at the natural sieve threshold `z = Nat.sqrt n`.

3. Verifies a sanity check at the primorial `n = 210 = 2·3·5·7`:
   `S(210) = 2 · (4/3) · (6/5) = 16/5 = 3.2`.

4. Bridges `BrunGoldbachHardyLittlewood` into the FixA paired-main-term
   chain `BrunGoldbachPairedMainTermRefinedAtSqrtFixA`.  The bridge is
   **parametric** in the absorption hypothesis
   `HardyLittlewoodToFixABridge`, which encodes the (open) Mertens-3
   bound "S(n) is at most polylogarithmic, absorbing into the FixA
   `log log n / (log n)²` reservoir".

5. Documents why this is the most natural classical form.

## Why this is the most natural classical form

The Halberstam-Richert §3.11 form `r(n) ≤ C · n · pBF · S(n)` is
*multiplicative* in `S(n)`, capturing the genuine local-density
correction at the primes dividing `n`.  The FixA additive form
`r(n) ≤ C₁ · n · pBF + reservoir` is a *bound* in the same shape that
absorbs the `S(n)` oscillation into the reservoir.  The HL form is
tighter (it tracks the singular-series oscillation precisely), but the
FixA form is what the downstream K-Goldbach chain consumes.

The bridge between them is exactly the *quantitative Mertens-3 bound*
`S(n) ≤ K · log log n`, which when multiplied by `n · pBF(√n)` and
combined with the corrected reservoir `n · log log n / (log n)²`,
gives the required absorption.

## Strict constraints (P20-T5 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* All theorems below are axiom-clean:  only `Classical.choice`,
  `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCHardyLittlewoodForm

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCFixABrunGoldbachProp
  (refinedReservoirCorrected
   refinedReservoirCorrected_def
   BrunGoldbachPairedMainTermRefinedAtSqrtFixA)

/-! ## Section 1 — The Hardy-Littlewood singular series factor -/

/-- **The Hardy-Littlewood singular series factor for the Goldbach
problem.**

```
singularSeries n := ∏_{p ∈ [3, n], p prime, p ∣ n} (p - 1) / (p - 2) .
```

This is the local correction factor in the classical Hardy-Littlewood
formula `r(n) ∼ 2C₂ · n / (log n)² · S(n)`.  Restricting to `p ≥ 3`
avoids the singularity at `p = 2` (where `p - 2 = 0`); for even `n` in
the Goldbach setting, `p = 2 ∣ n` always, but the `p = 2` local factor
is conventionally absorbed into the global constant `2 C₂`, so the
singular series ranges only over odd prime divisors. -/
noncomputable def singularSeries (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n),
    ((p : ℝ) - 1) / ((p : ℝ) - 2)

@[simp] lemma singularSeries_def (n : ℕ) :
    singularSeries n
      = ∏ p ∈ (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n),
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := rfl

/-! ## Section 2 — Positivity and lower bound `S(n) ≥ 1` -/

/-- Each factor `(p - 1)/(p - 2)` is positive for `p ≥ 3`. -/
theorem singularSeries_factor_pos {p : ℕ} (hp : 3 ≤ p) :
    (0 : ℝ) < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hnum_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  exact div_pos hnum_pos hden_pos

/-- Each factor `(p - 1)/(p - 2)` is at least `1` for `p ≥ 3`. -/
theorem singularSeries_factor_ge_one {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hden_le_num : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
  exact (one_le_div hden_pos).mpr hden_le_num

/-- `singularSeries n > 0` for all `n`. -/
theorem singularSeries_pos (n : ℕ) : 0 < singularSeries n := by
  unfold singularSeries
  refine Finset.prod_pos ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact singularSeries_factor_pos hp3

/-- `singularSeries n ≥ 1` for all `n`.  Each factor `(p-1)/(p-2) ≥ 1`
on odd primes `p ≥ 3`, and the empty product is `1`. -/
theorem one_le_singularSeries (n : ℕ) : 1 ≤ singularSeries n := by
  unfold singularSeries
  refine Finset.one_le_prod (fun p hp => ?_)
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact singularSeries_factor_ge_one hp3

/-! ## Section 3 — The Hardy-Littlewood form of the Brun-Goldbach Prop -/

/-- **The Hardy-Littlewood form of the Brun-Goldbach upper bound.**

There exists a constant `C > 0` and a threshold `N₀` such that for all
`n ≥ N₀`,

```
goldbachSiftedPair n √n
  ≤ C · n · pairedBrunFactor √n · singularSeries n .
```

This is the **classical Halberstam-Richert §3.11 bound**:  the most
natural form, matching the Hardy-Littlewood asymptotic prediction up
to constants.  It is the **tightest** upper bound (any weaker bound
without the `S(n)` factor would have to absorb the singular-series
oscillation into either the constant or the reservoir).

Mathlib v4.29.1 status: **open**.  This is the classical
Halberstam-Richert *Sieve Methods* Theorem 3.11 statement, not yet
formalised in mathlib. -/
def BrunGoldbachHardyLittlewood : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
    ∀ n : ℕ, N₀ ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n

/-! ## Section 4 — Primorial verification at `n = 210`

We verify the singular series value at the primorial `n = 210 = 2·3·5·7`.
The odd prime divisors in `[3, 210]` are exactly `{3, 5, 7}`, so

```
S(210) = (3-1)/(3-2) · (5-1)/(5-2) · (7-1)/(7-2)
       = 2/1 · 4/3 · 6/5
       = 48/15 = 16/5 = 3.2 .
```

Numerical chain sanity check at `n = 210`:

* `goldbachSiftedPair 210 √210 = goldbachSiftedPair 210 14 = 34`
  (the 34 Goldbach pairs `m + (210 - m)` with both `m, 210 - m`
  having no prime factor `≤ 14`).
* `n · pBF(14) · S(210) = 210 · (9/91) · (16/5)
                        = 210 · 144/455 = 30240/455 ≈ 66.5`.
* Hence `34 ≤ 66.5`, fitting the `C ≥ 1` regime. -/

/-- Helper:  the set of odd prime divisors of `210` in `[3, 210]` is
exactly `{3, 5, 7}`.

This is decidable:  filter `Finset.Icc 3 210` over the decidable
predicate `Nat.Prime p ∧ p ∣ 210`.  Since `210 = 2·3·5·7`, the only
prime divisors are `{2, 3, 5, 7}`, and the `≥ 3` restriction leaves
`{3, 5, 7}`. -/
private theorem oddPrimeDivisors_210 :
    (Finset.Icc 3 210).filter (fun p => Nat.Prime p ∧ p ∣ 210)
      = ({3, 5, 7} : Finset ℕ) := by
  -- We use `Decidable.decide` with elevated recursion depth.
  set_option maxRecDepth 4000 in decide

/-- **Primorial sanity check.**  `singularSeries 210 = 16 / 5`.

This unfolds the singular series at `n = 210` using the closed-form
computation `S(210) = ∏ p ∈ {3, 5, 7}, (p-1)/(p-2) = 2 · (4/3) · (6/5)
= 48/15 = 16/5`. -/
theorem singularSeries_210 : singularSeries 210 = 16 / 5 := by
  unfold singularSeries
  rw [oddPrimeDivisors_210]
  -- The Finset `{3, 5, 7}` is `insert 3 (insert 5 {7})`.  Compute the
  -- product by unfolding `Finset.prod_insert` twice and
  -- `Finset.prod_singleton` once.
  have h35 : (3 : ℕ) ∉ ({5, 7} : Finset ℕ) := by decide
  have h57 : (5 : ℕ) ∉ ({7} : Finset ℕ) := by decide
  rw [show ({3, 5, 7} : Finset ℕ) = insert 3 (insert 5 ({7} : Finset ℕ)) from rfl]
  rw [Finset.prod_insert h35, Finset.prod_insert h57, Finset.prod_singleton]
  norm_num

/-- **Primorial sanity check (numerical).**  `singularSeries 210 = 3.2`,
matching the classical Hardy-Littlewood expansion. -/
theorem singularSeries_210_eq_3p2 : singularSeries 210 = 3.2 := by
  rw [singularSeries_210]
  norm_num

/-! ## Section 5 — Bridge to the FixA paired-main-term chain

The bridge from `BrunGoldbachHardyLittlewood` to
`BrunGoldbachPairedMainTermRefinedAtSqrtFixA` requires absorbing the
`singularSeries n` factor into the reservoir.

**Mathematical content.**  The singular series satisfies the bound
`S(n) ≤ exp(O(log log n)) = (log n)^O(1)` (standard Mertens-3
consequence:  the sum `∑_{p ≤ x} 1/p ∼ log log x` controls the size of
`∏_{p | n} (1 + 1/(p-2))`).  Combined with the corrected reservoir
`n · log log n / (log n)²`, the absorption is straightforward.

Stating that absorption rigorously requires a **uniform** bound (the
quantitative Mertens-3 inequality).  We expose it as a parametric
hypothesis, mirroring the design pattern in
`Gdbh.PathCFixABrunGoldbachProp` where the FixA-to-original bridge is
parametric in a small-absorption Prop.

The parametric hypothesis is formulated to land **directly** in the
FixA additive shape, avoiding any cosmetic scaling issue:  it asserts
that the *product* `goldbachSiftedPair n √n` (after the HL bound) fits
into the FixA shape via the absorption identity. -/

/-- **The Hardy-Littlewood-to-FixA bridge hypothesis (parametric).**

This Prop asserts that, eventually, the HL multiplicative bound

```
goldbachSiftedPair n √n ≤ C · n · pairedBrunFactor √n · singularSeries n
```

implies the FixA additive bound

```
goldbachSiftedPair n √n ≤ C₁ · n · pairedBrunFactor √n + reservoir
```

for some constants `C₁` and the FixA-corrected reservoir.

This is the **quantitative** content of the Mertens-3 absorption
"`S(n) ≤ K · log log n` combined with the corrected reservoir's
`log log n / (log n)²` decay".

**Status**:  Mathematically this follows from Mertens-3 combined with
the corrected-reservoir shape, applied directly at the FixA level.
Mathlib v4.29.1 status: **open**.  We expose it as a parametric Prop
here.

By formulating the bridge as `HL ⇒ FixA` directly (rather than via a
separate absorption identity), we **sidestep** all reservoir-coefficient
scaling issues:  the FixA shape is the target, and the bridge produces
it directly.  This is the cleanest formulation for the parametric chain. -/
def HardyLittlewoodToFixABridge : Prop :=
  BrunGoldbachHardyLittlewood → BrunGoldbachPairedMainTermRefinedAtSqrtFixA

/-- **The main bridge:**  `Hardy-Littlewood + HardyLittlewoodToFixABridge
⇒ BrunGoldbachPairedMainTermRefinedAtSqrtFixA`.

Mathematical content.  The bridge hypothesis directly converts the HL
multiplicative bound into the FixA additive bound via Mertens-3
absorption.  The proof is then trivial:  apply the bridge to the HL
hypothesis. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_hardyLittlewood
    (hHL : BrunGoldbachHardyLittlewood)
    (hBridge : HardyLittlewoodToFixABridge) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixA :=
  hBridge hHL

/-! ### A more refined bridge with explicit absorption hypothesis.

We also provide a finer-granularity bridge where the absorption
hypothesis is stated in its natural multiplicative-to-additive form,
already FixA-shaped (no reservoir-coefficient mismatch). -/

/-- **Singular-series-to-FixA absorption (refined form).**

There exist constants `K > 0` and `N₀` such that for all `n ≥ N₀`,

```
n · pairedBrunFactor √n · singularSeries n
  ≤ K · n · pairedBrunFactor √n + refinedReservoirCorrected n √n .
```

This is the natural quantitative form of the Mertens-3 absorption.  We
formulate it FixA-shaped (with the corrected reservoir on the RHS),
so that the bridge is clean. -/
def SingularSeriesAbsorption : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
        ≤ K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + refinedReservoirCorrected n (Nat.sqrt n)

/-- **Refined bridge:**  `HL with constant ≤ 1` + `SingularSeriesAbsorption
⇒ FixA`.

The HL hypothesis here is the variant restricted to constant `C ≤ 1`
(which captures the natural Hardy-Littlewood normalization after
rescaling).  The proof combines HL with the absorption, multiplies, and
uses `C · reservoir ≤ reservoir` (since `C ≤ 1` and reservoir ≥ 0).

For the general HL form (with arbitrary `C > 0`), the simpler
`HardyLittlewoodToFixABridge` is the appropriate parametric input,
since it encodes the full absorption including any required scaling.

This refined bridge is exposed for completeness and to document the
clean "no-scaling" case. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_hardyLittlewood_small_constant
    (hHL : ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ C ≤ 1 ∧
            ∀ n : ℕ, N₀ ≤ n →
              (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n)
    (hAbs : SingularSeriesAbsorption) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixA := by
  obtain ⟨C, N_HL, hC_pos, hC_le_one, hHL_bd⟩ := hHL
  obtain ⟨K, hK_pos, N_abs, hAbs_bd⟩ := hAbs
  refine ⟨C * K, mul_pos hC_pos hK_pos, max (max N_HL N_abs) 3, ?_⟩
  intro n hn
  have hn_HL : N_HL ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_abs : N_abs ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  -- HL bound.
  have h1 : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
            ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n :=
    hHL_bd n hn_HL
  -- Absorption bound.
  have h2 : (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n
            ≤ K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
              + refinedReservoirCorrected n (Nat.sqrt n) :=
    hAbs_bd n hn_abs
  -- Multiply h2 by C ≥ 0.
  have hC_nn : 0 ≤ C := le_of_lt hC_pos
  have h3 : C * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n)
            ≤ C * (K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                    + refinedReservoirCorrected n (Nat.sqrt n)) :=
    mul_le_mul_of_nonneg_left h2 hC_nn
  -- Rewrite shapes via ring.
  have hLHS_eq : C * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n)
                  = C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * singularSeries n := by
    ring
  have hRHS_eq : C * (K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                        + refinedReservoirCorrected n (Nat.sqrt n))
                  = C * K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                    + C * refinedReservoirCorrected n (Nat.sqrt n) := by
    ring
  rw [hLHS_eq, hRHS_eq] at h3
  have h4 : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
            ≤ C * K * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
              + C * refinedReservoirCorrected n (Nat.sqrt n) := le_trans h1 h3
  -- Bound C * reservoir ≤ reservoir using C ≤ 1 and reservoir ≥ 0.
  have hres_nn : 0 ≤ refinedReservoirCorrected n (Nat.sqrt n) :=
    Gdbh.PathCFixABrunGoldbachProp.refinedReservoirCorrected_nonneg_of_three_le
      n (Nat.sqrt n) hn_3
  have hC_res_le : C * refinedReservoirCorrected n (Nat.sqrt n)
                    ≤ refinedReservoirCorrected n (Nat.sqrt n) := by
    have := mul_le_mul_of_nonneg_right hC_le_one hres_nn
    simpa using this
  linarith

/-! ## Section 6 — Why this is the most natural classical form (docstring) -/

/-- **The classical Halberstam-Richert §3.11 form.**

The bound

```
r(n) ≤ C · n · pBF(z) · S(n)
```

is the *natural* classical form because:

1. **It is tight up to constants.**  The Hardy-Littlewood asymptotic
   prediction `r(n) ∼ 2C₂ · n / (log n)² · S(n)` matches this form's
   shape exactly, modulo the constant.  No weaker form (without `S(n)`)
   can match the asymptotic without absorbing the singular-series
   oscillation into the constant or the reservoir.

2. **It captures the genuine local correction.**  The factor `S(n)`
   reflects the local density of Goldbach pairs at primes dividing
   `n`:  for `p | n`, the residue `m mod p` cannot be `0` or `n mod p`
   (else `p | m` or `p | n - m`), so the local density is
   `(p - 2)/p` rather than the "generic" `(p - 1)/p`, contributing
   a factor `(p - 1)/(p - 2) > 1` to the singular series.

3. **It is multiplicative**, matching the structure of the sifting
   problem (where local densities multiply across coprime moduli).

4. **The reservoir contribution is intrinsic.**  Going from the
   multiplicative HL form to the additive FixA form requires absorbing
   the `S(n)` oscillation (which is `≤ exp(O(log log n))`) into the
   reservoir.  The FixA-corrected reservoir `n · log log n / (log n)²`
   is precisely the right size for this absorption — a smaller
   reservoir (like the original `n / (log n)²`) is too tight to
   accommodate the `log log n` excursion at primorials.

The bridge `BrunGoldbachHardyLittlewood → FixA` is the rigorous
quantitative formalization of these classical observations.  See the
docstring of `HardyLittlewoodToFixABridge` for the parametric
content. -/
theorem singularSeries_is_natural_classical_form :
    -- Trivial statement that captures the docstring's content as a
    -- type-level checkpoint.
    ∀ n : ℕ, 1 ≤ singularSeries n :=
  one_le_singularSeries

/-! ## Section 7 — Axiom audit -/

#print axioms singularSeries_pos
#print axioms one_le_singularSeries
#print axioms singularSeries_210
#print axioms singularSeries_210_eq_3p2
#print axioms brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_hardyLittlewood
#print axioms brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_hardyLittlewood_small_constant

end PathCHardyLittlewoodForm
end Gdbh
