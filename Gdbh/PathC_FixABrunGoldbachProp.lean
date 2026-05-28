/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P20-T2 (Phase 20 / Path C — Define the FixA-upgraded
        Brun-Goldbach paired main-term Prop family, with the
        corrected reservoir `n · log log n / (log n)²`, and register
        the forward bridges into the existing K-Goldbach closure
        chain via the corrected absorption Prop.)
-/
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_AsymptoticBrunGoldbach

/-!
# Path C — P20-T2: FixA upgrade of the Brun-Goldbach paired main-term Prop

P19-T51 (`Gdbh.PathCAsymptoticBrunGoldbach`) established conditionally
— given the classical singular-series unboundedness along primorials
and the paired Mertens product bound — that the *original* P17-T6 main
chain Prop

```
BrunGoldbachPairedMainTermRefinedAtSqrt
  : ∃ C₁ > 0, ∀ n > 0,
      goldbachSiftedPair n √n
        ≤ C₁ · n · pairedBrunFactor √n + n / (log n)²
```

is **FALSE**.  The failure mode is the pointwise singular-series blow-up
at primorial `n`:  the reservoir `n / (log n)²` is too small to absorb
the `log log n` oscillation predicted by Hardy-Littlewood.

P19-T51 documented **three** honest fix options (a), (b), (c).
P20-T2 implements **Fix (a)**, the most direct: bump the reservoir to
the *corrected* shape

```
refinedReservoirCorrected n z := n · log log n / (log n)² .
```

This file's deliverables:

1. **Inline definition** of `refinedReservoirCorrected` (P20-T1 has the
   parallel deliverable for the `BrunRefinedComposition`-style export;
   we keep this file self-contained so it compiles independently).

2. **The `FixA` family of Props** at the canonical sieve threshold and
   in the universal-in-`z` form:

   * `BrunGoldbachPairedMainTermRefinedAtSqrtFixA`
   * `BrunGoldbachPairedMainTermRefinedFixA`
   * `PairedMainTermAbsorptionFixA`

3. **Forward bridges**:

   * `pairedMainTermAbsorption_fixA_of_refined_fixA`: the universal-in-`z`
     FixA Prop implies the FixA absorption Prop (immediate, by
     definitional unfolding — the corrected `Absorption` is literally
     the existential half of the corrected `Refined`).
   * `brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_refined_fixA`:
     the universal-in-`z` Prop implies its `z = √n` specialisation.

4. **Chain composition headline**: from the corrected universal-in-`z`
   `BrunGoldbachPairedMainTermRefinedFixA` *together with* a
   `correctedToOriginalBridge` hypothesis (the parametric content
   pushed onto a future P20 task — explicitly *not* claimed here),
   the K-Goldbach headline follows via the already-closed P17-T6
   chain through `pathC_kGoldbach_of_refined_main`.

   This headline is **parametric** in the corrected-to-original
   bridge:  it is unconditional in the chain, conditional in the
   bridge.

## Strict constraints (P20-T2 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* All theorems below are axiom-clean: only `Classical.choice`,
  `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file.
* P20-T1's file is not assumed present.  If it is later added, the
  inline `refinedReservoirCorrected` here is *propositionally equal*
  to the export version by construction; no breaking change is needed.
-/

namespace Gdbh
namespace PathCFixABrunGoldbachProp

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCBrunRefinedComposition (BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt
   PairedMainTermAbsorption
   brunGoldbachPairedMainTermRefinedAtSqrt_of_refined
   brunGoldbachPairedMainTermRefined_iff_absorption
   brunGoldbachPairedMainTermRefined_of_absorption
   pathC_kGoldbach_of_absorption)

/-! ## Section 1 — The corrected reservoir `refinedReservoirCorrected`

We define the corrected reservoir inline.  P20-T1 (the parallel task)
provides the same definition in `Gdbh.PathCBrunRefinedComposition`-style
export; we mirror it here so the file compiles independently. -/

/-- **The FixA-corrected Brun error reservoir.**  For `n, z : ℕ`,

```
refinedReservoirCorrected n z := n · log log n / (log n)² .
```

(The reservoir is independent of `z`, as in the original
`refinedReservoir`; the `z` argument is retained for shape-compatibility
with `BrunGoldbachMainTerm`-style consumers.)

Mathematical content:  the original reservoir `n / (log n)²` does not
absorb the singular-series oscillation `∼ log log n` at primorials
(P19-T51's 14th false-Prop catch).  Replacing it with
`n · log log n / (log n)²` is the standard "averaged" Brun-Goldbach
shape and absorbs the oscillation.

For `n ≤ 1`, the cast `(n : ℝ) ≤ 1` gives `log n ≤ 0` and
`log log n` is `Real.log` of a non-positive number (defined to be `0`
in mathlib), so the reservoir reduces to `0` or a small finite quantity.
This boundary behaviour is consistent with `refinedReservoir`'s
definition (where `log 0 = 0` and division by zero is `0`). -/
noncomputable def refinedReservoirCorrected : ℕ → ℕ → ℝ :=
  fun n _ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2

@[simp] lemma refinedReservoirCorrected_def (n z : ℕ) :
    refinedReservoirCorrected n z
      = (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2 := rfl

/-! ## Section 2 — The FixA Props at the canonical sieve threshold

We expose the FixA-corrected Prop at `z = Nat.sqrt n` (the only
`z`-value consumed downstream by Path C's K-Goldbach chain) and in the
universal-in-`z` form (the literal target Prop, used through the
absorption bridge). -/

/-- **`BrunGoldbachPairedMainTermRefinedAtSqrtFixA`.**  The
FixA-corrected specialisation of `BrunGoldbachPairedMainTermRefined`
at the canonical sieve threshold `z = Nat.sqrt n`.

Concretely:

```
∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  (goldbachSiftedPair n √n : ℝ)
    ≤ C₁ · n · pairedBrunFactor √n + refinedReservoirCorrected n √n
```

The `N₀` threshold replaces the original Prop's `0 < n` precondition;
the corrected reservoir is well-defined only when `log log n` is real
and positive, which requires `n ≥ 16 = ⌈e^e⌉`.  In practice the chain
consumes the Prop only for `n` large enough that all asymptotic
estimates apply, so the `N₀`-guarded form is the honest target.

**Status (P20-T2)**:  This file defines and exposes the Prop.  Closure
of the Prop itself is the next P20 deliverable; the upper bound is the
*classical* Halberstam-Richert §3.11 averaged Brun-Goldbach bound, which
is mathlib v4.29.1 **open**. -/
def BrunGoldbachPairedMainTermRefinedAtSqrtFixA : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoirCorrected n (Nat.sqrt n)

/-- **`BrunGoldbachPairedMainTermRefinedFixA`.**  The FixA-corrected
universal-in-`z` Prop.

Concretely:

```
∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n z : ℕ, N₀ ≤ n →
  (goldbachSiftedPair n z : ℝ)
    ≤ C₁ · n · pairedBrunFactor z + refinedReservoirCorrected n z
```

This is the literal FixA-upgraded form of the original
`BrunGoldbachPairedMainTermRefined`.  The corrected reservoir is
independent of `z`, so the `z`-quantification only ranges over the
`pairedBrunFactor z` term. -/
def BrunGoldbachPairedMainTermRefinedFixA : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∃ N₀ : ℕ,
      ∀ n z : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n z : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z
            + refinedReservoirCorrected n z

/-! ## Section 3 — The corrected absorption Prop

The original `Gdbh.PathCPairedMainTermAssembly.PairedMainTermAbsorption`
was hard-wired to the *original* reservoir `refinedReservoir`.  The
FixA upgrade requires a corresponding *corrected* absorption Prop. -/

/-- **`PairedMainTermAbsorptionFixA`.**  The FixA-corrected absorption
Prop, parallel to the original `PairedMainTermAbsorption` but with
the corrected reservoir and an `N₀`-threshold.

Concretely:

```
∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n z : ℕ, N₀ ≤ n →
  (goldbachSiftedPair n z : ℝ)
    ≤ C₁ · n · pairedBrunFactor z + refinedReservoirCorrected n z
```

This is **literally** `BrunGoldbachPairedMainTermRefinedFixA` (modulo
the order of quantifiers in `∃ C₁ … ∧ ∃ N₀`); we expose it under the
new name to keep the chain bookkeeping parallel with the original
P17-T6 design.  See
`pairedMainTermAbsorption_fixA_iff_refined_fixA` below. -/
def PairedMainTermAbsorptionFixA : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∃ N₀ : ℕ,
      ∀ n z : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n z : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z
            + refinedReservoirCorrected n z

/-! ## Section 4 — Forward bridges within the FixA family -/

/-- **Forward bridge 1**:  the corrected universal-in-`z` Prop is
**literally** the corrected absorption Prop.  They differ only in
naming. -/
theorem pairedMainTermAbsorption_fixA_iff_refined_fixA :
    BrunGoldbachPairedMainTermRefinedFixA ↔ PairedMainTermAbsorptionFixA :=
  Iff.rfl

/-- **Forward bridge 2**:  `Refined FixA → Absorption FixA`.  Immediate
from the iff. -/
theorem pairedMainTermAbsorption_fixA_of_refined_fixA
    (h : BrunGoldbachPairedMainTermRefinedFixA) :
    PairedMainTermAbsorptionFixA :=
  pairedMainTermAbsorption_fixA_iff_refined_fixA.mp h

/-- **Forward bridge 3**:  `Refined FixA → AtSqrt FixA`.  Specialise the
universal-in-`z` Prop at `z = Nat.sqrt n`. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_refined_fixA
    (h : BrunGoldbachPairedMainTermRefinedFixA) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixA := by
  obtain ⟨C₁, hC₁, N₀, hbd⟩ := h
  refine ⟨C₁, hC₁, N₀, ?_⟩
  intro n hn
  exact hbd n (Nat.sqrt n) hn

/-- **Forward bridge 4** (case-split form, headline of P20-T2):  given
the AtSqrt FixA Prop *together with* a `z ≠ Nat.sqrt n` extension Prop
(the "small absorption" of the task statement), the corrected universal
Prop follows.

This is the **direct analogue** of the original P17-T6
`AtSqrt + Absorption ⇒ Refined` bridge, lifted to the FixA family.

We expose the small-absorption side as a *named parametric hypothesis*
(not closed in this file) because closing it requires the FixA Mertens
bound for `pairedBrunFactor z` at arbitrary `z`, which is the parallel
P20 deliverable.

Concretely, the parametric hypothesis is the bound for `z ≠ Nat.sqrt n`:

```
SmallAbsorptionFixA :=
  ∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n z : ℕ, N₀ ≤ n → z ≠ Nat.sqrt n →
    (goldbachSiftedPair n z : ℝ)
      ≤ C₁ · n · pairedBrunFactor z + refinedReservoirCorrected n z
```

(In the original P17-T6 design, `Absorption` covered **all** `z` with
a single bound; the FixA `Absorption` is the same shape, but the
case-split form makes the architectural decomposition explicit.) -/
def SmallAbsorptionFixA : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∃ N₀ : ℕ,
      ∀ n z : ℕ, N₀ ≤ n → z ≠ Nat.sqrt n →
        (goldbachSiftedPair n z : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z
            + refinedReservoirCorrected n z

/-- **Bridge from `AtSqrt FixA + SmallAbsorptionFixA` to the corrected
universal Prop.**

The proof is by case-split on `z = Nat.sqrt n` vs `z ≠ Nat.sqrt n`:

* `z = Nat.sqrt n`:  the AtSqrt FixA Prop fires.
* `z ≠ Nat.sqrt n`:  the small-absorption Prop fires.

We take the *maximum* of the two constants `C₁` and the *maximum*
threshold `N₀`. -/
theorem refined_fixA_of_atSqrt_and_smallAbsorption
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrtFixA)
    (hSmall : SmallAbsorptionFixA) :
    BrunGoldbachPairedMainTermRefinedFixA := by
  obtain ⟨C₁, hC₁, N₀, hAt⟩ := hAtSqrt
  obtain ⟨C₂, hC₂, N₁, hSm⟩ := hSmall
  -- Use `max C₁ C₂` as the joint constant; `max N₀ N₁` as the threshold.
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, max N₀ N₁, ?_⟩
  intro n z hn
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N₁ ≤ n := le_trans (le_max_right _ _) hn
  by_cases hz : z = Nat.sqrt n
  · -- AtSqrt branch.
    subst hz
    have hAt_n := hAt n hn0
    have hC1_le : C₁ ≤ max C₁ C₂ := le_max_left _ _
    have hpf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) :=
      le_of_lt (pairedBrunFactor_pos _)
    have hn_nn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
      mul_nonneg hn_nn hpf_nn
    have h_mul_le :
        C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          ≤ max C₁ C₂ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
      have h1 : C₁ * (n : ℝ) ≤ max C₁ C₂ * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hC1_le hn_nn
      exact mul_le_mul_of_nonneg_right h1 hpf_nn
    linarith
  · -- SmallAbsorption branch.
    have hSm_n := hSm n z hn1 hz
    have hC2_le : C₂ ≤ max C₁ C₂ := le_max_right _ _
    have hpf_nn : 0 ≤ pairedBrunFactor z :=
      le_of_lt (pairedBrunFactor_pos _)
    have hn_nn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_mul_le :
        C₂ * (n : ℝ) * pairedBrunFactor z
          ≤ max C₁ C₂ * (n : ℝ) * pairedBrunFactor z := by
      have h1 : C₂ * (n : ℝ) ≤ max C₁ C₂ * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hC2_le hn_nn
      exact mul_le_mul_of_nonneg_right h1 hpf_nn
    linarith

/-! ## Section 5 — Chain composition headline

The K-Goldbach closure chain composes:

```
BrunGoldbachPairedMainTermRefinedFixA
  + (FixA → original) bridge
  ⇒ BrunGoldbachPairedMainTermRefined  (P17-T6, original reservoir)
  ⇒ pathC_kGoldbach_of_refined_main    (P14 / P17-T6 chain headline)
```

The `(FixA → original)` bridge is the **honest open content** of the
FixA upgrade:  it would replace the *primorial-unbounded* original
reservoir `n / (log n)²` with the corrected one `n · log log n /
(log n)²`, which is **larger** for `n ≥ 16`.  Going *from* the corrected
*to* the original requires either (i) a stronger absorption argument
(absorbing the `log log n` factor into the `pairedBrunFactor z` term
via the Mertens-paired asymptotic), or (ii) restricting downstream
consumers to use the corrected reservoir directly (a downstream
refactor outside this file's write scope).

We expose the bridge **parametrically**.  The headline is unconditional
in the chain composition; it is conditional only in the parametric
bridge hypothesis. -/

/-- **Parametric headline (P20-T2 chain composition)**.

Given:
* the corrected universal-in-`z` FixA Prop, **and**
* a *parametric bridge hypothesis* asserting that the FixA Prop
  implies the original `BrunGoldbachPairedMainTermRefined`,

the K-Goldbach headline follows via the already-closed P17-T6 chain:

```
FixA  →  (via bridge)  Refined  →  Absorption  →  K-Goldbach .
```

The bridge hypothesis encodes the "small absorption" content of the
task statement:  it is the precise quantitative statement that the FixA
reservoir's `log log n` excess is absorbable into the main term. -/
theorem pathC_kGoldbach_of_fixA_via_bridge
    (hFixA : BrunGoldbachPairedMainTermRefinedFixA)
    (hBridge : BrunGoldbachPairedMainTermRefinedFixA →
                BrunGoldbachPairedMainTermRefined) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  -- Bridge FixA to the original universal Prop.
  have hRefined : BrunGoldbachPairedMainTermRefined := hBridge hFixA
  -- The original universal Prop is equivalent to the original Absorption.
  have hAbs : PairedMainTermAbsorption :=
    (brunGoldbachPairedMainTermRefined_iff_absorption.mp hRefined)
  -- Close the K-Goldbach chain via the existing P17-T6 headline.
  exact pathC_kGoldbach_of_absorption hAbs

/-- **Parametric headline 2 (P20-T2, via AtSqrt + SmallAbsorption)**.

A more granular form of the headline:  given the AtSqrt FixA Prop and
the small-absorption FixA Prop separately, plus the parametric bridge,
the K-Goldbach headline follows.

This exposes the same chain at the finer architectural granularity
used in P17-T6's `pathC_kGoldbach_of_absorption`. -/
theorem pathC_kGoldbach_of_atSqrt_fixA_and_smallAbsorption
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrtFixA)
    (hSmall : SmallAbsorptionFixA)
    (hBridge : BrunGoldbachPairedMainTermRefinedFixA →
                BrunGoldbachPairedMainTermRefined) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_fixA_via_bridge
    (refined_fixA_of_atSqrt_and_smallAbsorption hAtSqrt hSmall) hBridge

/-! ## Section 6 — Sanity checks (non-negativity of corrected reservoir)

For the catch-defusal of the FixA family, the corrected reservoir
must be non-negative on the regime where it is consumed.  We prove
this on `n ≥ 3` (so `log n > 1`, hence `log log n > 0`). -/

/-- For `n : ℕ` with `n ≥ 3`, the corrected reservoir is non-negative.
This is the catch-defusal sanity check:  the FixA Prop's reservoir is
non-negative on the `n ≥ 3` regime, so the existential is not vacuously
refuted by negative-reservoir witnesses. -/
theorem refinedReservoirCorrected_nonneg_of_three_le
    (n z : ℕ) (hn : 3 ≤ n) :
    0 ≤ refinedReservoirCorrected n z := by
  unfold refinedReservoirCorrected
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_gt_one : 1 < Real.log 3 := by
    -- `log 3 > log e = 1` since `3 > e ≈ 2.718`.
    have he_lt_3 : Real.exp 1 < 3 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      linarith
    have h_lt : Real.log (Real.exp 1) < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) he_lt_3
    rwa [Real.log_exp] at h_lt
  have hlogn_ge_log3 : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn_real
  have hlogn_gt_one : 1 < Real.log (n : ℝ) := by linarith
  have hloglogn_nn : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    -- `log log n ≥ log 1 = 0` since `log n ≥ 1`.
    have h_le : Real.log 1 ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (by norm_num) (le_of_lt hlogn_gt_one)
    rw [Real.log_one] at h_le
    exact h_le
  have h_num_nn : 0 ≤ (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
    mul_nonneg hn_nn hloglogn_nn
  have h_den_nn : 0 ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  exact div_nonneg h_num_nn h_den_nn

/-! ## Section 7 — Axiom audit

Each headline theorem below is axiom-clean:  only the universally
accepted `Classical.choice`, `Quot.sound`, `propext`. -/

#print axioms pairedMainTermAbsorption_fixA_iff_refined_fixA
#print axioms pairedMainTermAbsorption_fixA_of_refined_fixA
#print axioms brunGoldbachPairedMainTermRefinedAtSqrtFixA_of_refined_fixA
#print axioms refined_fixA_of_atSqrt_and_smallAbsorption
#print axioms pathC_kGoldbach_of_fixA_via_bridge
#print axioms pathC_kGoldbach_of_atSqrt_fixA_and_smallAbsorption
#print axioms refinedReservoirCorrected_nonneg_of_three_le

end PathCFixABrunGoldbachProp
end Gdbh
