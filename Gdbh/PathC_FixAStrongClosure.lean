/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P21-T1 (Phase 21 / Path C — Reduce
        `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` axiom-clean
        to the single named open mathlib gap
        `ClassicalBrunGoldbachLogLog`, via the closed paired Mertens
        upper bound and an AM-GM-style `log log n` absorption.)
-/
import Gdbh.PathC_FixAStrongReservoir
import Gdbh.PathC_PairedBrunMertensUpper
import Gdbh.PathC_PairedBrunLargeZ
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Path C — P21-T1: Closure of the FixA' chain Prop via a single Brun gap

## Mission

The FixA' (P20-T4) Prop

```
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (goldbachSiftedPair n √n : ℝ)
      ≤ C₁ · n · pairedBrunFactor √n
        + refinedReservoirCorrectedStrong n √n
```

with reservoir `refinedReservoirCorrectedStrong n z = n · (log log n)² /
(log n)²` is the canonical "FixA'-upgraded" chain Prop.  P20-T4 verified
it numerically at primorials `n ∈ {210, 2310}`.

This file **reduces** the Prop axiom-cleanly to the **single** named
classical input

```
ClassicalBrunGoldbachLogLog : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n ≥ N₀,
    (goldbachSiftedPair n √n : ℝ)
      ≤ C · n · pairedBrunFactor √n · log log n .
```

This is the classical Halberstam-Richert §3.11 form, *with the Mertens-3
absorption of the singular series already performed*: the multiplicative
correction `S(n) ≤ K · log log n` is baked into the constant.

Mathlib v4.29.1 status: **open** — `ClassicalBrunGoldbachLogLog` is
not formally available in the library.  It is, however, the standard
and most natural Brun-Goldbach form expressed with the
Mertens-singular-series absorption pre-applied.

## Mathematical strategy

The bridge consumes one closed input from the project's existing
infrastructure:

* `Gdbh.PathCPairedBrunMertensUpper.pairedBrunFactorMertensUpperAtSqrt_holds`
  — the paired Mertens upper bound
  `pairedBrunFactor √n ≤ C' / (log n)²` for `n ≥ N_M`, closed via M1 +
  Abel + paired specialisation.

Given:

```
(H1) (LogLog Brun-Goldbach)  LHS ≤ C · n · pBF · log log n   (n ≥ N_BG)
(H2) (Mertens upper)         pBF ≤ C' / (log n)²              (n ≥ N_M)
```

We prove:

```
LHS  ≤  C · n · pBF + n · (log log n)² / (log n)²
       = C · n · pBF + refinedReservoirCorrectedStrong n √n .
```

The split is `log log n = 1 + (log log n - 1)`:

```
C · n · pBF · log log n
  =  C · n · pBF
   + C · n · pBF · (log log n - 1) .
```

For the second piece, apply (H2) (valid since `log log n - 1 ≥ 0` by
threshold choice):

```
C · n · pBF · (log log n - 1)
  ≤ C · C' · n · (log log n - 1) / (log n)²
  ≤ n · (log log n)² / (log n)²    (whenever  log log n ≥ C · C').
```

The penultimate `≤` uses `C · C' · (u - 1) ≤ u²` for `u ≥ C · C'` and
`u ≥ 0`:  from `u ≥ C C' ≥ 0`, `u² ≥ u · C C' ≥ (u - 1) · C C'`
(since `u ≥ u - 1`).

The threshold `n` such that `log log n ≥ max(C · C', 1)` ensures both
`log log n - 1 ≥ 0` AND `log log n ≥ C · C'`, simultaneously absorbing
the `log log n - 1` factor.  We obtain such an `N₀` via
`exists_nat_gt` applied to `exp (exp (max(C · C', 1)))`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* All theorems axiom-clean:  only `Classical.choice`, `Quot.sound`,
  `propext`.
* This file **only adds**; it does not modify any other file.

## Honesty rule

The bridge is **closed** axiom-clean.  The remaining mathlib gap is the
**single** named Prop `ClassicalBrunGoldbachLogLog`, which is the
Halberstam-Richert §3.11 form with the standard Mertens-3 singular
series absorption pre-applied.  This is *mathematically classical*
(Mertens 1874 + Halberstam-Richert *Sieve Methods* §3.11), but is
**not** in mathlib v4.29.1.

The other infrastructure consumed (`pairedBrunFactorMertensUpperAtSqrt_holds`)
is **closed in the project repo** (P18-T1), traceable through M1
(Mertens' 1st theorem) and Abel summation.
-/

namespace Gdbh
namespace PathCFixAStrongClosure

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCFixAStrongReservoir
  (refinedReservoirCorrectedStrong refinedReservoirCorrectedStrong_def
   BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)
open Gdbh.PathCPairedBrunLargeZ (PairedBrunFactorMertensUpperAtSqrt)
open Gdbh.PathCPairedBrunMertensUpper (pairedBrunFactorMertensUpperAtSqrt_holds)

/-! ## Section 1 — The classical Brun-Goldbach Prop with `log log n`

This is the *named open* classical input.  Mathematically:  classical
Halberstam-Richert §3.11 combined with the standard Mertens-3 bound
`S(n) ≤ K · log log n` on the singular series. -/

/-- **`ClassicalBrunGoldbachLogLog`.**  The classical Brun-Goldbach
upper bound with the singular series already absorbed via Mertens-3:

```
∃ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  (goldbachSiftedPair n √n : ℝ)
    ≤ C · n · pairedBrunFactor √n · log log n .
```

**Status**: mathlib v4.29.1 **open**.

This is the *most natural* form for the FixA' closure:  the classical
Halberstam-Richert §3.11 bound `r(n) ≤ C · n · pBF · S(n)` combined with
the Mertens-3 bound `S(n) ≤ K · log log n` (with the constant `K`
absorbed into `C`).

Once this Prop is closed (in mathlib or in a future project deliverable),
the FixA' chain Prop
`BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` follows
axiom-cleanly via `brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog`
below. -/
def ClassicalBrunGoldbachLogLog : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
    ∀ n : ℕ, N₀ ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            * Real.log (Real.log (n : ℝ))

/-! ## Section 2 — Threshold lemma for `log log n ≥ K ∧ log log n ≥ 1`

We need a natural-number threshold `N₀` such that `n ≥ N₀` implies
`max(K, 1) ≤ log log n`.  By archimedeanness applied twice, this exists. -/

/-- For any real `K`, there exists a natural threshold `N₀` such that
for all `n ≥ N₀`, both `1 ≤ log log n` and `K ≤ log log n`. -/
lemma exists_threshold_log_log_ge_max_one (K : ℝ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 ≤ Real.log (Real.log (n : ℝ))) ∧
      (K ≤ Real.log (Real.log (n : ℝ))) := by
  set K' : ℝ := max K 1 with hK'_def
  have hK'_ge_1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'_ge_K : K ≤ K' := le_max_left _ _
  -- Step 1: pick `M₁ > exp K'` so that `log M₁ > K'`.
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (Real.exp K')
  -- Step 2: pick `M₂ > exp M₁` so that `log log M₂ > K'`.
  obtain ⟨M₂, hM₂⟩ := exists_nat_gt (Real.exp (M₁ : ℝ))
  refine ⟨M₂, ?_⟩
  intro n hn
  have hn_real : ((M₂ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_exp_M1_lt_n : Real.exp (M₁ : ℝ) < (n : ℝ) := lt_of_lt_of_le hM₂ hn_real
  have h_exp_M1_pos : (0 : ℝ) < Real.exp (M₁ : ℝ) := Real.exp_pos _
  have h_log_n_gt_M1 : (M₁ : ℝ) < Real.log (n : ℝ) := by
    have h := Real.log_lt_log h_exp_M1_pos h_exp_M1_lt_n
    rwa [Real.log_exp] at h
  have h_exp_K'_lt_log_n : Real.exp K' < Real.log (n : ℝ) :=
    lt_trans hM₁ h_log_n_gt_M1
  have h_exp_K'_pos : (0 : ℝ) < Real.exp K' := Real.exp_pos _
  have h_log_log_gt_K' : K' < Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_lt_log h_exp_K'_pos h_exp_K'_lt_log_n
    rwa [Real.log_exp] at h
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-! ## Section 3 — Core inequality `B · (u - 1) ≤ u²` -/

/-- The core absorption inequality:  for `0 ≤ B ≤ u`, we have
`B · (u - 1) ≤ u²`. -/
lemma core_absorption_ineq {B u : ℝ} (hB : 0 ≤ B) (h : B ≤ u) :
    B * (u - 1) ≤ u^2 := by
  have h_u_nn : 0 ≤ u := le_trans hB h
  -- u² ≥ u · B ≥ (u - 1) · B = B · (u - 1).
  have h_u_sq : u^2 = u * u := sq u
  have h1 : u * B ≤ u * u :=
    mul_le_mul_of_nonneg_left h h_u_nn
  have h2 : (u - 1) * B ≤ u * B := by
    have h_le : u - 1 ≤ u := by linarith
    exact mul_le_mul_of_nonneg_right h_le hB
  have h_eq : B * (u - 1) = (u - 1) * B := by ring
  rw [h_eq, h_u_sq]
  linarith

/-! ## Section 4 — The bridge theorem -/

/-- **P21-T1 main bridge.**  The classical Brun-Goldbach upper bound
with `log log n` absorption implies the FixA' chain Prop at `√n`.

The proof combines:

* the assumed multiplicative bound
  `LHS ≤ C · n · pBF · log log n` (from `ClassicalBrunGoldbachLogLog`),
* the **closed** Mertens upper bound
  `pBF ≤ C' / (log n)²` (from `pairedBrunFactorMertensUpperAtSqrt_holds`),

via the additive split `log log n = 1 + (log log n - 1)` and the
elementary absorption `C · C' · (u - 1) ≤ u²` for `u ≥ C · C'`.

No `sorry`, no `axiom`, no `admit`. -/
theorem brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog
    (hLogLog : ClassicalBrunGoldbachLogLog) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong := by
  -- Extract `ClassicalBrunGoldbachLogLog` data.
  obtain ⟨C, N_BG, hC_pos, hBG_bd⟩ := hLogLog
  -- Extract the closed Mertens upper bound.
  obtain ⟨C', N_M, hC'_pos, hM_bd⟩ := pairedBrunFactorMertensUpperAtSqrt_holds
  -- Define B := C · C' (the absorption constant).
  set B : ℝ := C * C' with hB_def
  have hB_pos : 0 < B := mul_pos hC_pos hC'_pos
  have hB_nn : 0 ≤ B := le_of_lt hB_pos
  -- Get a threshold N_K such that for n ≥ N_K, log log n ≥ B and ≥ 1.
  obtain ⟨N_K, h_thresh⟩ := exists_threshold_log_log_ge_max_one B
  -- The final threshold:  max of all three.
  set N₀ : ℕ := max (max N_BG N_M) N_K with hN₀_def
  -- Witness:  C₁ := C, threshold N₀.
  refine ⟨C, hC_pos, N₀, ?_⟩
  intro n hn
  -- Unpack thresholds.
  have hn_BG : N_BG ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_M : N_M ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_K : N_K ≤ n := le_trans (le_max_right _ _) hn
  -- From threshold lemma:  log log n ≥ 1, log log n ≥ B.
  obtain ⟨h_loglog_ge_1, h_loglog_ge_B⟩ := h_thresh n hn_K
  -- Useful positivity facts.
  have h_pbf_pos : 0 < pairedBrunFactor (Nat.sqrt n) := pairedBrunFactor_pos _
  have h_pbf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := le_of_lt h_pbf_pos
  have h_n_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Apply Brun-Goldbach LogLog at `n`.
  have hBG_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                    * Real.log (Real.log (n : ℝ)) := hBG_bd n hn_BG
  -- Apply Mertens upper at `n`.
  have hM_n : pairedBrunFactor (Nat.sqrt n) ≤ C' / (Real.log (n : ℝ))^2 :=
    hM_bd n hn_M
  -- Algebraic identity.
  set u : ℝ := Real.log (Real.log (n : ℝ)) with hu_def
  have h_u_nn : 0 ≤ u := by linarith
  have h_u_minus_one_nn : 0 ≤ u - 1 := by linarith
  have h_u_ge_B : B ≤ u := h_loglog_ge_B
  -- Multiplicative split of u.
  have h_split :
      C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * u
        = C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1) := by
    ring
  -- Apply Mertens upper to the second piece (valid since u - 1 ≥ 0).
  have h_pbf_le : pairedBrunFactor (Nat.sqrt n) * (u - 1)
                    ≤ C' / (Real.log (n : ℝ))^2 * (u - 1) :=
    mul_le_mul_of_nonneg_right hM_n h_u_minus_one_nn
  -- Multiply by C · n ≥ 0.
  have hCn_nn : 0 ≤ C * (n : ℝ) := mul_nonneg (le_of_lt hC_pos) h_n_real_nn
  have h_second_piece_le_1 :
      C * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * (u - 1))
        ≤ C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2 * (u - 1)) := by
    exact mul_le_mul_of_nonneg_left h_pbf_le hCn_nn
  -- Rearrange to:  C · n · pBF · (u - 1) ≤ C · C' · n · (u - 1) / (log n)².
  have h_eq_lhs :
      C * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * (u - 1))
        = C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1) := by ring
  have h_eq_rhs :
      C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2 * (u - 1))
        = B * (n : ℝ) * (u - 1) / (Real.log (n : ℝ))^2 := by
    rw [hB_def]; ring
  have h_second_piece_le :
      C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1)
        ≤ B * (n : ℝ) * (u - 1) / (Real.log (n : ℝ))^2 := by
    -- Use the chain:  LHS = (C·n) · (pBF · (u-1)) ≤ (C·n) · (C'/(log n)² · (u-1)) = RHS.
    calc C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1)
        = C * (n : ℝ) * (pairedBrunFactor (Nat.sqrt n) * (u - 1)) := by ring
      _ ≤ C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2 * (u - 1)) := h_second_piece_le_1
      _ = B * (n : ℝ) * (u - 1) / (Real.log (n : ℝ))^2 := by rw [hB_def]; ring
  -- Now apply core absorption:  B · (u - 1) ≤ u².  Multiply by n / (log n)² ≥ 0.
  have h_core : B * (u - 1) ≤ u^2 := core_absorption_ineq hB_nn h_u_ge_B
  have h_logsq_nn : 0 ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
  -- n / (log n)² ≥ 0.
  have h_n_div_nn : 0 ≤ (n : ℝ) / (Real.log (n : ℝ))^2 :=
    div_nonneg h_n_real_nn h_logsq_nn
  -- B · (u - 1) · n / (log n)²  ≤  u² · n / (log n)² = reservoir.
  have h_core_mul :
      B * (u - 1) * (n : ℝ) / (Real.log (n : ℝ))^2
        ≤ u^2 * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    have h_n_logsq_nn : 0 ≤ (n : ℝ) / (Real.log (n : ℝ))^2 := h_n_div_nn
    have h_step : B * (u - 1) * (n : ℝ) ≤ u^2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h_core h_n_real_nn
    -- Divide by (log n)² ≥ 0.
    exact div_le_div_of_nonneg_right h_step h_logsq_nn
  -- Rearrange numerator.
  have h_rearr : B * (n : ℝ) * (u - 1) / (Real.log (n : ℝ))^2
                  = B * (u - 1) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    ring
  -- The reservoir's value at n, √n.
  have h_res_eq : refinedReservoirCorrectedStrong n (Nat.sqrt n)
                    = u^2 * (n : ℝ) / (Real.log (n : ℝ))^2 := by
    simp [refinedReservoirCorrectedStrong_def, hu_def]
    ring
  -- Combine.
  have h_second_piece_le_res :
      C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1)
        ≤ refinedReservoirCorrectedStrong n (Nat.sqrt n) := by
    rw [h_res_eq]
    -- Chain:  C·n·pBF·(u-1) ≤ B·n·(u-1)/(log n)² = B·(u-1)·n/(log n)² ≤ u²·n/(log n)².
    calc C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * (u - 1)
        ≤ B * (n : ℝ) * (u - 1) / (Real.log (n : ℝ))^2 := h_second_piece_le
      _ = B * (u - 1) * (n : ℝ) / (Real.log (n : ℝ))^2 := by ring
      _ ≤ u^2 * (n : ℝ) / (Real.log (n : ℝ))^2 := h_core_mul
  -- Final step:  combine the split with the second-piece bound.
  rw [h_split] at hBG_n
  linarith

/-! ## Section 5 — Headline summary -/

/-- **P21-T1 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `ClassicalBrunGoldbachLogLog` — named Prop encoding the classical
   uniform Brun-Goldbach upper bound with the Mertens-3 singular
   series absorption pre-applied.  Status:  mathlib v4.29.1 **open**.

2. `brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog`
   — bridge theorem reducing
   `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` (the P20-T4 FixA'
   chain Prop) to `ClassicalBrunGoldbachLogLog`.

The bridge uses the closed Mertens upper bound
`pairedBrunFactorMertensUpperAtSqrt_holds` (P18-T1) and the elementary
absorption inequality `C · C' · (u - 1) ≤ u²` for `u ≥ C · C'`.

After P21-T1, `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`
reduces to the **single** classical input `ClassicalBrunGoldbachLogLog`.

## Residual mathlib gap

`ClassicalBrunGoldbachLogLog` is the classical Halberstam-Richert
§3.11 bound `r(n) ≤ C · n · pBF · S(n)` combined with the Mertens-3
bound `S(n) ≤ K · log log n` on the singular series.  Both ingredients
are classical, but neither is in mathlib v4.29.1.  Closing this Prop
would close the FixA' chain.  -/
theorem pathC_p21_t1_summary : True := trivial

end PathCFixAStrongClosure
end Gdbh

/-! ## Section 6 — Axiom audit -/

#print axioms Gdbh.PathCFixAStrongClosure.brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog
#print axioms Gdbh.PathCFixAStrongClosure.exists_threshold_log_log_ge_max_one
#print axioms Gdbh.PathCFixAStrongClosure.core_absorption_ineq
#print axioms Gdbh.PathCFixAStrongClosure.pathC_p21_t1_summary
