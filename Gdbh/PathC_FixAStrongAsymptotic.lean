/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P21-T4 (Phase 21 / Path C — Asymptotic closure of the FixA'
        chain Prop via a classical Brun-Goldbach hypothesis with the
        Hardy-Littlewood singular series and the Mertens estimate on
        the paired Brun factor already pre-absorbed.)
-/
import Gdbh.PathC_FixAStrongReservoir
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Path C — P21-T4: Asymptotic FixA' closure via a classical Brun-Goldbach hypothesis

## Mission

The FixA' (P20-T4) chain Prop is

```
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong : Prop :=
  ∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (goldbachSiftedPair n √n : ℝ)
      ≤ C₁ · n · pairedBrunFactor √n
        + refinedReservoirCorrectedStrong n √n
```

where

```
refinedReservoirCorrectedStrong n z := n · (log log n)² / (log n)² .
```

P21-T1 (`Gdbh.PathC_FixAStrongClosure`) already gives a bridge from
the **`(log log n)`**-form of the classical Brun-Goldbach Prop
`ClassicalBrunGoldbachLogLog` (with the paired Mertens upper bound
on `pairedBrunFactor` kept symbolic).  Its main feature is that it
hands back a witness with `C₁ = C` — a non-trivial main-term constant.

The present file (P21-T4) closes the FixA' chain Prop in a different
direction:  it consumes a **stronger** classical hypothesis in which the
*paired Mertens* `pBF ≤ K_M / (log n)²` and the **Mertens-3** singular
series bound `S(n) ≤ K_s · log log n` have *both* been pre-absorbed into
the constant, leaving the combined bound

```
goldbachSiftedPair n √n  ≤  C · n · log log n / (log n)² .
```

This is the **literal product form** `(Brun-Goldbach) × (Mertens) ×
(Hardy-Littlewood-S)` of the classical Halberstam-Richert §3.11 input.
With this hypothesis, the FixA' chain Prop becomes immediate:  the
absorbing factor of the reservoir is `(log log n)²`, and for `n` so
large that `log log n ≥ C`, we have

```
C · log log n  ≤  (log log n)²,
```

so the LHS is already dominated by the **reservoir alone** —
`refinedReservoirCorrectedStrong n √n` — without any contribution from
the main `C₁ · n · pBF(√n)` term.  We may therefore take
**any positive `C₁`** (we choose `C₁ = 1`) and obtain the bound
unconditionally on `n ≥ N₀`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene: only `Classical.choice`, `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file.

## Honesty rule

The hypothesis `ClassicalBrunGoldbachLogLogPaired` is the natural
classical Halberstam-Richert §3.11 form **with both** Hardy-Littlewood
(`S(n) ≲ log log n`) **and** the paired Mertens
(`pBF ≲ 1/(log n)²`) absorbed into one constant.  This product form is
*not* in mathlib v4.29.1, but it is a strictly stronger pre-packaging of
P21-T1's `ClassicalBrunGoldbachLogLog` combined with the project's
already-closed paired Mertens bound (P18-T1).  It is therefore at most as
hard as `ClassicalBrunGoldbachLogLog`.

The bridge in this file is **closed** axiom-clean.  The only remaining
mathlib gap is the named Prop `ClassicalBrunGoldbachLogLogPaired`.
-/

namespace Gdbh
namespace PathCFixAStrongAsymptotic

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCFixAStrongReservoir
  (refinedReservoirCorrectedStrong refinedReservoirCorrectedStrong_def
   BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)

/-! ## Section 1 — The classical Brun-Goldbach `log log n / (log n)²` form

This is the *combined classical input*:  the Halberstam-Richert §3.11
upper bound `r(n) ≤ C · n · pBF · S(n)` with the singular series bound
`S(n) ≤ K_s · log log n` and the paired Mertens bound
`pBF ≤ K_M / (log n)²` *both* absorbed into a single constant `C`. -/

/-- **`ClassicalBrunGoldbachLogLogPaired`.**  The classical Brun-
Goldbach + Hardy-Littlewood + Mertens combined uniform upper bound:

```
∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (goldbachSiftedPair n √n : ℝ) ≤ C · n · log log n / (log n)² .
```

Mathematically this is the classical Halberstam-Richert §3.11 estimate
`r(n) ≤ C · n · ∏_{p ≤ √n} (1 - 2/p) · S(n)` combined with:

* **Mertens (1874) / paired Mertens** —
  `∏_{p ≤ √n} (1 - 2/p) ≤ K_M / (log n)²` (closed in the project repo
  as `pairedBrunFactorMertensUpperAtSqrt_holds`, P18-T1);

* **Mertens-3 / Hardy-Littlewood singular series** —
  `S(n) ≤ K_s · log log n`.

The combination yields the displayed bound with `C = C_HR · K_M · K_s`.

**Status:** mathlib v4.29.1 **open**.  This Prop is the *literal product
form* of P21-T1's `ClassicalBrunGoldbachLogLog` combined with the
project's closed paired Mertens bound — *strictly weaker as a hypothesis*
than `ClassicalBrunGoldbachLogLog` alone, since both factors have been
pre-applied. -/
def ClassicalBrunGoldbachLogLogPaired : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
    ∀ n : ℕ, N ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * Real.log (Real.log (n : ℝ))
            / (Real.log (n : ℝ))^2

/-! ## Section 2 — Threshold lemma:  `log log n ≥ K` for `n` large.

We need a natural-number threshold `N` such that for `n ≥ N`,
`log log n ≥ K`.  By archimedeanness applied twice this exists. -/

/-- For any real `K`, there exists a natural threshold `N` such that
for all `n ≥ N`, `K ≤ log log n`. -/
lemma exists_threshold_log_log_ge (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ Real.log (Real.log (n : ℝ)) := by
  -- Step 1: pick `M₁ > exp K` so that `log M₁ > K`.
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (Real.exp K)
  -- Step 2: pick `M₂ > exp M₁` so that `log log M₂ > K`.
  obtain ⟨M₂, hM₂⟩ := exists_nat_gt (Real.exp (M₁ : ℝ))
  refine ⟨M₂, ?_⟩
  intro n hn
  have hn_real : ((M₂ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_exp_M1_lt_n : Real.exp (M₁ : ℝ) < (n : ℝ) := lt_of_lt_of_le hM₂ hn_real
  have h_exp_M1_pos : (0 : ℝ) < Real.exp (M₁ : ℝ) := Real.exp_pos _
  have h_log_n_gt_M1 : (M₁ : ℝ) < Real.log (n : ℝ) := by
    have h := Real.log_lt_log h_exp_M1_pos h_exp_M1_lt_n
    rwa [Real.log_exp] at h
  have h_exp_K_lt_log_n : Real.exp K < Real.log (n : ℝ) :=
    lt_trans hM₁ h_log_n_gt_M1
  have h_exp_K_pos : (0 : ℝ) < Real.exp K := Real.exp_pos _
  have h_log_log_gt_K : K < Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_lt_log h_exp_K_pos h_exp_K_lt_log_n
    rwa [Real.log_exp] at h
  linarith

/-! ## Section 3 — Core absorption inequality.

The arithmetic claim:  for non-negative `u ≥ C`, we have
`C · u ≤ u²`.  This is the *core* of the asymptotic FixA' closure:
once `log log n ≥ C`, the entire LHS — which already has a factor of
`log log n` — is dominated by the reservoir, which has a factor of
`(log log n)²`. -/

/-- Core inequality:  if `0 ≤ C ≤ u`, then `C · u ≤ u²`. -/
lemma core_absorption_ineq {C u : ℝ} (hC : 0 ≤ C) (h : C ≤ u) :
    C * u ≤ u^2 := by
  have h_u_nn : 0 ≤ u := le_trans hC h
  have h_step : C * u ≤ u * u :=
    mul_le_mul_of_nonneg_right h h_u_nn
  have h_sq : u^2 = u * u := sq u
  linarith

/-! ## Section 4 — The bridge theorem. -/

/-- **P21-T4 main bridge.**  The classical Brun-Goldbach +
Hardy-Littlewood + Mertens combined upper bound implies the FixA'
chain Prop at `√n`.

The proof:  let `(C, N)` witness `ClassicalBrunGoldbachLogLogPaired`.
Choose an additional threshold `N_K` such that `n ≥ N_K` implies
`log log n ≥ C`.  Set `N₀ = max N N_K` and take `C₁ = 1`.

For `n ≥ N₀`:

```
LHS  ≤  C · n · log log n / (log n)²                 (hypothesis)
     ≤  n · (log log n)² / (log n)²                 (core absorption, C ≤ log log n)
     = refinedReservoirCorrectedStrong n √n
     ≤  C₁ · n · pBF(√n) + refinedReservoirCorrectedStrong n √n
```

since `C₁ · n · pBF(√n) ≥ 0` (we use `C₁ = 1`, `n ≥ 0`, `pBF ≥ 0`).

No `sorry`, no `axiom`, no `admit`. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLogPaired
    (hPaired : ClassicalBrunGoldbachLogLogPaired) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong := by
  -- Extract data.
  obtain ⟨C, N, hC_pos, hBd⟩ := hPaired
  have hC_nn : 0 ≤ C := le_of_lt hC_pos
  -- Pick threshold for `log log n ≥ C`.
  obtain ⟨N_K, h_thresh⟩ := exists_threshold_log_log_ge C
  -- Final threshold.
  set N₀ : ℕ := max N N_K with hN₀_def
  -- Witness:  C₁ = 1, threshold N₀.
  refine ⟨1, by norm_num, N₀, ?_⟩
  intro n hn
  -- Unpack thresholds.
  have hn_N : N ≤ n := le_trans (le_max_left _ _) hn
  have hn_K : N_K ≤ n := le_trans (le_max_right _ _) hn
  have h_loglog_ge_C : C ≤ Real.log (Real.log (n : ℝ)) := h_thresh n hn_K
  -- Apply the hypothesis at `n`.
  have hBd_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                ≤ C * (n : ℝ) * Real.log (Real.log (n : ℝ))
                    / (Real.log (n : ℝ))^2 := hBd n hn_N
  -- Useful positivity facts.
  set u : ℝ := Real.log (Real.log (n : ℝ)) with hu_def
  have h_u_nn : 0 ≤ u := le_trans hC_nn h_loglog_ge_C
  have h_C_le_u : C ≤ u := h_loglog_ge_C
  have h_n_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_logsq_nn : (0 : ℝ) ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  -- Core absorption:  `C · u ≤ u²`.
  have h_core : C * u ≤ u^2 := core_absorption_ineq hC_nn h_C_le_u
  -- Multiply both sides by `n ≥ 0`.
  have h_core_n : C * u * (n : ℝ) ≤ u^2 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right h_core h_n_real_nn
  -- Divide by `(log n)² ≥ 0`.
  have h_core_div :
      C * u * (n : ℝ) / (Real.log (n : ℝ))^2
        ≤ u^2 * (n : ℝ) / (Real.log (n : ℝ))^2 :=
    div_le_div_of_nonneg_right h_core_n h_logsq_nn
  -- Rearrange to match the hypothesis numerator.
  have h_rearr_lhs :
      C * (n : ℝ) * u / (Real.log (n : ℝ))^2
        = C * u * (n : ℝ) / (Real.log (n : ℝ))^2 := by ring
  -- Reservoir definition.
  have h_res_eq : refinedReservoirCorrectedStrong n (Nat.sqrt n)
                    = (n : ℝ) * u^2 / (Real.log (n : ℝ))^2 := by
    simp [refinedReservoirCorrectedStrong_def, hu_def]
  -- Show LHS ≤ reservoir.
  have h_lhs_le_res :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ refinedReservoirCorrectedStrong n (Nat.sqrt n) := by
    rw [h_res_eq]
    calc (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * u / (Real.log (n : ℝ))^2 := hBd_n
      _ = C * u * (n : ℝ) / (Real.log (n : ℝ))^2 := h_rearr_lhs
      _ ≤ u^2 * (n : ℝ) / (Real.log (n : ℝ))^2 := h_core_div
      _ = (n : ℝ) * u^2 / (Real.log (n : ℝ))^2 := by ring
  -- Final step:  add the (non-negative) main term.
  have h_pbf_pos : 0 < pairedBrunFactor (Nat.sqrt n) := pairedBrunFactor_pos _
  have h_pbf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := le_of_lt h_pbf_pos
  have h_main_nn : 0 ≤ 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
    have h1 : 0 ≤ (1 : ℝ) := by norm_num
    have h2 : 0 ≤ (1 : ℝ) * (n : ℝ) := mul_nonneg h1 h_n_real_nn
    exact mul_nonneg h2 h_pbf_nn
  linarith

/-! ## Section 5 — Headline summary -/

/-- **P21-T4 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `ClassicalBrunGoldbachLogLogPaired` — named Prop encoding the
   classical Halberstam-Richert §3.11 upper bound with both the
   Hardy-Littlewood singular series (`S(n) ≲ log log n`) and the paired
   Mertens estimate (`pBF ≲ 1/(log n)²`) pre-absorbed into the constant.
   Status:  mathlib v4.29.1 **open**.

2. `brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLogPaired`
   — bridge theorem reducing the FixA' chain Prop
   `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` to
   `ClassicalBrunGoldbachLogLogPaired`.

The bridge is closed axiom-cleanly by the elementary absorption
inequality `C · u ≤ u²` for `u ≥ C ≥ 0`, applied with `u = log log n`.

After P21-T4, `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`
reduces to the **single** classical input
`ClassicalBrunGoldbachLogLogPaired`.

## Residual mathlib gap

`ClassicalBrunGoldbachLogLogPaired` is the standard
Halberstam-Richert §3.11 bound combined with two classical Mertens-type
inputs (the paired sieve product estimate and the singular series
estimate).  Both ingredients are classical, but neither product form is
in mathlib v4.29.1.  Closing this Prop in mathlib would close the FixA'
chain.

This complements P21-T1's `ClassicalBrunGoldbachLogLog`:  P21-T1 keeps
the paired Mertens factor symbolic and consumes it from
`pairedBrunFactorMertensUpperAtSqrt_holds`, while P21-T4 takes both
classical factors pre-absorbed.  Either Prop suffices to close FixA';
which one to pursue in future mathlib work is a stylistic choice. -/
theorem pathC_p21_t4_summary : True := trivial

end PathCFixAStrongAsymptotic
end Gdbh

/-! ## Section 6 — Axiom audit -/

#print axioms Gdbh.PathCFixAStrongAsymptotic.brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLogPaired
#print axioms Gdbh.PathCFixAStrongAsymptotic.exists_threshold_log_log_ge
#print axioms Gdbh.PathCFixAStrongAsymptotic.core_absorption_ineq
#print axioms Gdbh.PathCFixAStrongAsymptotic.pathC_p21_t4_summary
