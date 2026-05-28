/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P18-T2-real (Phase 18 / Path C — real-valued Paired-Brun
        Mertens lower bound + honest absorption bridge)
-/
import Gdbh.PathC_PairedBrunMertensLowerProof
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_BrunGoldbachComposition

/-!
# Path C — P18-T2-real: Real-valued paired-Brun Mertens lower bound

This file is the **P18-T2-real deliverable** (the honest follow-up to
P18-T2's 12th false-Prop catch).

## Context

P18-T2 established that the natural-valued Prop
`Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensLower` (with
`K : ℕ, 0 < K`) is **mathematically impossible**: the paired Mertens
limit forces `pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂ ≈ 0.8326`,
which is `< 1`, so no positive natural witness exists.

The honest refactor exposes the *real-valued* analog
`Gdbh.PathCPairedBrunMertensLowerProof.PairedBrunFactorRealMertensLower`,
where the lower-bound constant is `C : ℝ, 0 < C`.  This Prop IS
classically true (witness `C = 4 e^(-2γ) C₂ - ε ≈ 0.83 - ε`).

## Outputs of this file

1. **`PairedBrunMertensThirdLowerGap`** — named open mathlib-gap Prop:
   the **lower-bound** companion of the existing upper-bound
   `PairedBrunMertensThirdGap`.  Specifically:

   ```
   ∃ C : ℝ, ∃ z₀ : ℕ, 0 < C ∧
     ∀ z : ℕ, z₀ ≤ z →  C / (Real.log z)^2 ≤ pairedBrunFactor z .
   ```

   Mathlib v4.29.1 status: **open**.  Classically a direct consequence
   of the sharp paired Mertens asymptotic
   `pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂ > 0`.

2. **`pairedBrunFactorRealMertensLower_of_thirdLowerGap`** — axiom-clean
   reduction: the lower-bound gap implies
   `PairedBrunFactorRealMertensLower` (specialised at `z ∈ [√n, n)`,
   `n ≥ N₀`).

   The reduction uses the antitonicity of `pairedBrunFactor` and the
   monotonicity of `Real.log` to convert `(log z)^2` into `(log n)^2`.

3. **`absorption_of_atSqrt_and_realResiduals`** — the **wrapper bridge**:
   uses `PairedBrunFactorRealMertensLower` (real-valued) instead of the
   impossible nat-valued `PairedBrunFactorMertensLower` to close
   `PairedMainTermAbsorption`.  This is the honest companion to
   `Gdbh.PathCPairedBrunLargeZ.absorption_of_atSqrt_and_residuals`.

## Strategy for (2)

For `n ≥ N₀'` (with `N₀'` chosen so `n ≥ 3`), `z ∈ [√n, n)`:

* By antitonicity in `z`: `pairedBrunFactor(z) ≥ pairedBrunFactor(n - 1)`.
* By the lower gap at `z = n - 1` (assuming `n - 1 ≥ z₀`):
  `C / (log (n - 1))^2 ≤ pairedBrunFactor(n - 1)`.
* By monotonicity of `log`: `log (n - 1) ≤ log n`, so
  `(log (n - 1))^2 ≤ (log n)^2`, hence
  `C / (log n)^2 ≤ C / (log (n - 1))^2`.
* Chain: `C / (log n)^2 ≤ pairedBrunFactor(n - 1) ≤ pairedBrunFactor(z)`.

Caveat: the division step requires `(log (n - 1))^2 > 0`, i.e.
`n - 1 ≥ 2`, i.e. `n ≥ 3`.  This is absorbed in the threshold.

## Strategy for (3)

The proof is a verbatim adaptation of
`Gdbh.PathCPairedBrunLargeZ.absorption_of_atSqrt_and_residuals` with
the natural `K : ℕ` replaced by `K_real : ℝ, 0 < K_real`.  The single
algebraic step that breaks is the bridge constant
`C_bridge = C * C' / (K : ℝ)`, which becomes
`C_bridge = C * C' / K_real`; positivity follows from `0 < K_real`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie* (1874).
* G. H. Hardy, J. E. Littlewood, *Some problems of "Partitio
  numerorum"; III* (1923).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, §1.4.
-/

namespace Gdbh
namespace PathCPairedBrunMertensLowerReal

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (refinedReservoir_nonneg)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt
   PairedMainTermAbsorption
   goldbachSiftedPair_antitone_z_real)
open Gdbh.PathCPairedBrunLargeZ
  (PairedBrunFactorMertensUpperAtSqrt
   PairedMainTermResidualLowRegion
   pairedBrunFactor_antitone
   goldbachSiftedPair_eq_zero_of_large_z_real)
open Gdbh.PathCPairedBrunMertensLowerProof
  (PairedBrunFactorRealMertensLower)

/-! ## Section 1 — Named open Prop: paired-Brun Mertens third *lower* gap

The lower-bound companion of the existing
`Gdbh.PathCMertensProof.PairedBrunMertensThirdGap` (which gives the
matching upper bound).  Both are direct consequences of the sharp
paired-Mertens asymptotic
`pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂ > 0`. -/

/-- **Named open mathlib-gap Prop (paired-Brun Mertens third
*lower* bound).**

There exist constants `C : ℝ` and `z₀ : ℕ` such that for all `z ≥ z₀`,

```
C / (log z)^2  ≤  pairedBrunFactor z .
```

Mathlib v4.29.1 status: **open**.  Reduces to the sharp paired
Mertens asymptotic (Hardy-Littlewood twin-prime constant `C₂`),
specifically `pairedBrunFactor(z) · (log z)^2 → 4 e^(-2γ) C₂ ≈ 0.83`,
which gives the lower bound with `C = 4 e^(-2γ) C₂ - ε` for any small
`ε > 0`.

This is the **real-valued** analog of the natural-valued
`Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensLower` (which is
mathematically impossible — see P18-T2's honesty finding). -/
def PairedBrunMertensThirdLowerGap : Prop :=
  ∃ C : ℝ, ∃ z₀ : ℕ, 0 < C ∧
    ∀ z : ℕ, z₀ ≤ z →
      C / (Real.log (z : ℝ))^2 ≤ pairedBrunFactor z

/-! ## Section 2 — Reduction: lower gap ⇒ `PairedBrunFactorRealMertensLower`

Given the named open lower gap (asymptotic at `z`), we obtain the
real-valued residual at `(n, z)` for `z ∈ [√n, n)`, `n` large. -/

/-- **Reduction lemma.**  The `PairedBrunMertensThirdLowerGap` implies
`PairedBrunFactorRealMertensLower`.

For `n ≥ N₀ := max(z₀ + 1, 3)` and `z ∈ [√n, n)`:

* `pairedBrunFactor(z) ≥ pairedBrunFactor(n - 1)` (antitonicity).
* `n - 1 ≥ z₀` (since `n ≥ z₀ + 1`), so the lower gap applies at
  `z' = n - 1`: `C / (log (n - 1))^2 ≤ pairedBrunFactor(n - 1)`.
* `log (n - 1) ≤ log n` (monotonicity), so
  `(log (n - 1))^2 ≤ (log n)^2`.  Together with `(log (n - 1))^2 > 0`
  (since `n - 1 ≥ 2 ⇒ log (n - 1) > 0`), this gives
  `C / (log n)^2 ≤ C / (log (n - 1))^2`. -/
theorem pairedBrunFactorRealMertensLower_of_thirdLowerGap
    (h : PairedBrunMertensThirdLowerGap) :
    PairedBrunFactorRealMertensLower := by
  obtain ⟨C, z₀, hCpos, hbd⟩ := h
  -- Threshold: n - 1 ≥ z₀ requires n ≥ z₀ + 1, AND n ≥ 3 (so log (n - 1) > 0).
  refine ⟨C, max (z₀ + 1) 3, hCpos, ?_⟩
  intro n z hn _hz_sqrt hz_lt
  -- Setup: n ≥ z₀ + 1 and n ≥ 3.
  have hn_ge_z0_succ : z₀ + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_ge_three : 3 ≤ n := le_trans (le_max_right _ _) hn
  -- So z' = n - 1 ≥ z₀ AND n - 1 ≥ 2.
  have hz0_le_n_sub : z₀ ≤ n - 1 := by omega
  have h_n_sub_ge_two : 2 ≤ n - 1 := by omega
  -- z ≤ n - 1.
  have hz_le_n_sub_one : z ≤ n - 1 := by omega
  -- Antitonicity: pairedBrunFactor (n - 1) ≤ pairedBrunFactor z.
  have h_antitone : pairedBrunFactor (n - 1) ≤ pairedBrunFactor z :=
    pairedBrunFactor_antitone hz_le_n_sub_one
  -- Lower gap at z' = n - 1.
  have h_lower_n_sub :
      C / (Real.log ((n - 1 : ℕ) : ℝ))^2 ≤ pairedBrunFactor (n - 1) :=
    hbd (n - 1) hz0_le_n_sub
  -- log (n - 1) > 0: since n - 1 ≥ 2 > 1.
  have h_n_sub_real : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h_n_sub_ge_two
  have h_n_sub_gt_one : (1 : ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
  have h_log_n_sub_pos : 0 < Real.log ((n - 1 : ℕ) : ℝ) :=
    Real.log_pos h_n_sub_gt_one
  have h_log_n_sub_sq_pos : 0 < (Real.log ((n - 1 : ℕ) : ℝ))^2 := by positivity
  -- log n > 0 too.
  have h_n_real_ge_three : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_three
  have h_n_real_gt_one : (1 : ℝ) < (n : ℝ) := by linarith
  have h_log_n_pos : 0 < Real.log (n : ℝ) := Real.log_pos h_n_real_gt_one
  have h_log_n_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
  -- log (n - 1) ≤ log n (monotonicity).
  have h_n_sub_le_n : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : (n - 1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have h_log_mono : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log
    · linarith
    · exact h_n_sub_le_n
  -- (log (n - 1))^2 ≤ (log n)^2 (squaring; both sides nonneg).
  have h_log_sq_mono :
      (Real.log ((n - 1 : ℕ) : ℝ))^2 ≤ (Real.log (n : ℝ))^2 := by
    have h_nn : 0 ≤ Real.log ((n - 1 : ℕ) : ℝ) := le_of_lt h_log_n_sub_pos
    nlinarith [h_log_mono, h_nn]
  -- C / (log n)^2 ≤ C / (log (n - 1))^2.
  have h_div_le :
      C / (Real.log (n : ℝ))^2 ≤ C / (Real.log ((n - 1 : ℕ) : ℝ))^2 := by
    apply div_le_div_of_nonneg_left (le_of_lt hCpos) h_log_n_sub_sq_pos h_log_sq_mono
  -- Chain.
  exact le_trans h_div_le (le_trans h_lower_n_sub h_antitone)

/-! ## Section 3 — Inlined residual-enlargement helper

Since the original `residual_enlarged_helper` in
`Gdbh/PathC_PairedBrunLargeZ.lean` is `private`, we re-prove it here
in the form required by `absorption_of_atSqrt_and_realResiduals`.

The proof is a verbatim adaptation of the private original
(no Mertens lower bound is needed for the helper itself). -/

/-- **Residual-enlargement helper (inlined).**  From `AtSqrt` and the
residual, produce an enlarged residual covering `n < M ∨ z < √n` for
any user-chosen `M`.

For bounded `n` in `[N₀_resid, M)` with `z ≥ √n`, we use AtSqrt
combined with the elementary bound
`pairedBrunFactor(√n) ≤ 1` and the lower bound
`pairedBrunFactor(z) ≥ pairedBrunFactor(M) > 0` (antitone for `z ≤ M`),
plus sift collapse for `z ≥ n - 1`, plus boundary case analysis for
`n ∈ {1, 2}`. -/
private lemma residual_enlarged_helper_inlined
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hResid : PairedMainTermResidualLowRegion)
    (M : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ n z : ℕ, 0 < n → (n < M ∨ z < Nat.sqrt n) →
        (goldbachSiftedPair n z : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
  classical
  obtain ⟨C, hCpos, hAtSqrtBd⟩ := hAtSqrt
  obtain ⟨C_resid, N₀_resid, hC_resid_pos, hResidBd⟩ := hResid
  set pBF_min : ℝ := pairedBrunFactor M with hpBF_min_def
  have hpBF_min_pos : 0 < pBF_min := pairedBrunFactor_pos M
  set C_bd : ℝ := C / pBF_min with hC_bd_def
  have hC_bd_pos : 0 < C_bd := div_pos hCpos hpBF_min_pos
  set C₁ : ℝ := max C_resid C_bd + 1 with hC₁_def
  have hC₁_pos : 0 < C₁ := by
    rw [hC₁_def]
    have : 0 ≤ max C_resid C_bd := le_max_of_le_left (le_of_lt hC_resid_pos)
    linarith
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn hcond
  by_cases h_n_resid : n < N₀_resid
  · have h := hResidBd n z hn (Or.inl h_n_resid)
    have h_resid_le_C₁ : C_resid ≤ C₁ := by
      rw [hC₁_def]
      have : C_resid ≤ max C_resid C_bd := le_max_left _ _
      linarith
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
    have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
      mul_nonneg h_n_nn h_pf_nn
    have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
        ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
      have : C_resid * ((n : ℝ) * pairedBrunFactor z)
          ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
        mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
      linarith [this]
    linarith
  · push_neg at h_n_resid
    rcases hcond with h_n_lt_M | h_z_lt_sqrt
    · by_cases h_z_sqrt : z < Nat.sqrt n
      · have h := hResidBd n z hn (Or.inr h_z_sqrt)
        have h_resid_le_C₁ : C_resid ≤ C₁ := by
          rw [hC₁_def]
          have : C_resid ≤ max C_resid C_bd := le_max_left _ _
          linarith
        have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
        have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
        have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
          mul_nonneg h_n_nn h_pf_nn
        have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
          have : C_resid * ((n : ℝ) * pairedBrunFactor z)
              ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
            mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
          linarith [this]
        linarith
      · push_neg at h_z_sqrt
        rcases Nat.lt_or_ge n 3 with h_n_small | h_n_ge_3
        · interval_cases n
          · -- n = 1: sift = 0.
            unfold goldbachSiftedPair Gdbh.PathCGoldbachRBound.goldbachSiftedPairSet
            have h_empty : (Finset.Icc 1 (1 - 1) : Finset ℕ) = ∅ := by
              apply Finset.Icc_eq_empty; omega
            rw [h_empty]
            simp
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_main_nn : 0 ≤ C₁ * 1 * pairedBrunFactor z := by
              apply mul_nonneg
              · exact mul_nonneg (le_of_lt hC₁_pos) (by norm_num)
              · exact h_pf_nn
            have h_res_nn : 0 ≤ refinedReservoir 1 z := refinedReservoir_nonneg 1 z
            linarith
          · -- n = 2: sift ≤ 1, reservoir > 1.
            have h_sift_le_one : (goldbachSiftedPair 2 z : ℝ) ≤ 1 := by
              have h_card : goldbachSiftedPair 2 z ≤ 1 := by
                unfold goldbachSiftedPair Gdbh.PathCGoldbachRBound.goldbachSiftedPairSet
                refine le_trans (Finset.card_filter_le _ _) ?_
                simp
              exact_mod_cast h_card
            have h_res_gt_one : (1 : ℝ) < refinedReservoir 2 z := by
              show (1 : ℝ) < (2 : ℝ) / (Real.log 2)^2
              have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
              have hlog2_lt_one : Real.log 2 < 1 := by
                have : Real.log 2 < Real.log (Real.exp 1) := by
                  apply Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
                  have h1 : (2 : ℝ) < Real.exp 1 := by
                    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
                    linarith
                  exact h1
                rwa [Real.log_exp] at this
              have hsq_lt_one : (Real.log 2)^2 < 1 := by
                have : (Real.log 2)^2 < 1^2 := by
                  exact sq_lt_sq' (by linarith) hlog2_lt_one
                simpa using this
              have hsq_pos : 0 < (Real.log 2)^2 := by positivity
              rw [lt_div_iff₀ hsq_pos]
              linarith
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_main_nn : 0 ≤ C₁ * ((2 : ℕ) : ℝ) * pairedBrunFactor z := by
              apply mul_nonneg
              · exact mul_nonneg (le_of_lt hC₁_pos) (by norm_num)
              · exact h_pf_nn
            linarith
        · -- n ≥ 3.
          by_cases h_z_collapse : n - 1 ≤ z
          · have h_sift_zero : (goldbachSiftedPair n z : ℝ) = 0 :=
              goldbachSiftedPair_eq_zero_of_large_z_real h_n_ge_3 h_z_collapse
            rw [h_sift_zero]
            have h_main_nn : 0 ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
              apply mul_nonneg
              · apply mul_nonneg (le_of_lt hC₁_pos)
                exact_mod_cast Nat.zero_le _
              · exact le_of_lt (pairedBrunFactor_pos z)
            have h_res_nn : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
            linarith
          · push_neg at h_z_collapse
            have hz_lt_n : z < n := by omega
            have hz_le_M : z ≤ M := by omega
            have h_pf_z_ge_min : pBF_min ≤ pairedBrunFactor z :=
              pairedBrunFactor_antitone hz_le_M
            have hAtSqrt_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  + refinedReservoir n (Nat.sqrt n) := hAtSqrtBd n hn
            have h_anti : (goldbachSiftedPair n z : ℝ) ≤
                (goldbachSiftedPair n (Nat.sqrt n) : ℝ) :=
              goldbachSiftedPair_antitone_z_real n h_z_sqrt
            have h_pf_sqrt_le_one : pairedBrunFactor (Nat.sqrt n) ≤ 1 :=
              pairedBrunFactor_le_one _
            have h_res_eq : refinedReservoir n (Nat.sqrt n) = refinedReservoir n z := by
              simp [refinedReservoir_def]
            have hCnn : 0 ≤ C := le_of_lt hCpos
            have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
            have h_main_chain :
                C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤ C * (n : ℝ) := by
              have : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  ≤ C * (n : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left h_pf_sqrt_le_one
                  (mul_nonneg hCnn h_n_nn)
              linarith [this]
            have h_C_n_eq : C * (n : ℝ) = C_bd * (n : ℝ) * pBF_min := by
              rw [hC_bd_def]
              have hne : pBF_min ≠ 0 := ne_of_gt hpBF_min_pos
              field_simp
            have h_bridge : C * (n : ℝ) ≤ C_bd * (n : ℝ) * pairedBrunFactor z := by
              rw [h_C_n_eq]
              apply mul_le_mul_of_nonneg_left h_pf_z_ge_min
              exact mul_nonneg (le_of_lt hC_bd_pos) h_n_nn
            have h_main_bd : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                ≤ C_bd * (n : ℝ) * pairedBrunFactor z :=
              le_trans h_main_chain h_bridge
            have h_C_bd_le_C₁ : C_bd ≤ C₁ := by
              rw [hC₁_def]
              have : C_bd ≤ max C_resid C_bd := le_max_right _ _
              linarith
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
              mul_nonneg h_n_nn h_pf_nn
            have h_C_to_C₁ : C_bd * (n : ℝ) * pairedBrunFactor z
                ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
              have : C_bd * ((n : ℝ) * pairedBrunFactor z)
                  ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
                mul_le_mul_of_nonneg_right h_C_bd_le_C₁ h_n_pf_nn
              linarith [this]
            calc (goldbachSiftedPair n z : ℝ)
                ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ) := h_anti
              _ ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  + refinedReservoir n (Nat.sqrt n) := hAtSqrt_n
              _ ≤ C_bd * (n : ℝ) * pairedBrunFactor z
                  + refinedReservoir n (Nat.sqrt n) := by linarith
              _ ≤ C₁ * (n : ℝ) * pairedBrunFactor z
                  + refinedReservoir n (Nat.sqrt n) := by linarith
              _ = C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
                  rw [h_res_eq]
    · -- z < √n.
      have h := hResidBd n z hn (Or.inr h_z_lt_sqrt)
      have h_resid_le_C₁ : C_resid ≤ C₁ := by
        rw [hC₁_def]
        have : C_resid ≤ max C_resid C_bd := le_max_left _ _
        linarith
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : C_resid * ((n : ℝ) * pairedBrunFactor z)
            ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
        linarith [this]
      linarith

/-! ## Section 4 — Wrapper bridge: `absorption_of_atSqrt_and_realResiduals`

This replicates `Gdbh.PathCPairedBrunLargeZ.absorption_of_atSqrt_and_residuals`
with the impossible nat-valued `PairedBrunFactorMertensLower` replaced
by the achievable real-valued `PairedBrunFactorRealMertensLower`. -/

/-- **Wrapper bridge: `AtSqrt + RealLower + UpperAtSqrt + Residual ⇒ Absorption`.**

The honest companion of
`Gdbh.PathCPairedBrunLargeZ.absorption_of_atSqrt_and_residuals`
using the real-valued `PairedBrunFactorRealMertensLower` (achievable)
instead of the impossible nat-valued `PairedBrunFactorMertensLower`.

Proof: verbatim adaptation, with `(K : ℝ)` replaced by `K_real > 0`. -/
theorem absorption_of_atSqrt_and_realResiduals
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hLower : PairedBrunFactorRealMertensLower)
    (hUpperSqrt : PairedBrunFactorMertensUpperAtSqrt)
    (hResid : PairedMainTermResidualLowRegion) :
    PairedMainTermAbsorption := by
  classical
  -- Unpack the Mertens hypotheses.
  obtain ⟨C, hCpos, hAtSqrtBd⟩ := hAtSqrt
  obtain ⟨K_real, N₀_lower, hK_real_pos, hLowerBd⟩ := hLower
  obtain ⟨C', N₀_upper, hC'pos, hUpperBd⟩ := hUpperSqrt
  -- Threshold: max of all three plus 3, plus 1.
  set M : ℕ := max (max N₀_lower N₀_upper) 3 + 1 with hM_def
  -- Use the inlined helper to extend the residual to threshold M.
  obtain ⟨C_resid', hC_resid'_pos, hResidBd'⟩ :=
    residual_enlarged_helper_inlined
      ⟨C, hCpos, hAtSqrtBd⟩ hResid M
  -- Bridge constant for the Region II step.
  set C_bridge : ℝ := C * C' / K_real with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge := by
    rw [hC_bridge_def]
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hCpos) (le_of_lt hC'pos)
    · exact le_of_lt hK_real_pos
  -- Uniform absorption constant.
  set C₁ : ℝ := max C_resid' C_bridge + 1 with hC₁_def
  have hC₁pos : 0 < C₁ := by
    rw [hC₁_def]
    have : 0 ≤ max C_resid' C_bridge :=
      le_max_of_le_left (le_of_lt hC_resid'_pos)
    linarith
  refine ⟨C₁, hC₁pos, ?_⟩
  intro n z hn
  by_cases h_low : n < M ∨ z < Nat.sqrt n
  · -- Region: n < M OR z < √n.  Use the enlarged residual.
    have h := hResidBd' n z hn h_low
    have h_resid_le_C₁ : C_resid' ≤ C₁ := by
      rw [hC₁_def]
      have : C_resid' ≤ max C_resid' C_bridge := le_max_left _ _
      linarith
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
    have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
      mul_nonneg h_n_nn h_pf_nn
    have h_main_le : C_resid' * (n : ℝ) * pairedBrunFactor z
        ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
      have : C_resid' * ((n : ℝ) * pairedBrunFactor z)
          ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
        mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
      linarith [this]
    linarith
  · -- Region: n ≥ M AND z ≥ √n.
    push_neg at h_low
    obtain ⟨hn_ge_M, hz_ge_sqrt⟩ := h_low
    have hn_ge_3 : 3 ≤ n := by
      have h3 : 3 ≤ M := by
        rw [hM_def]
        have : 3 ≤ max (max N₀_lower N₀_upper) 3 := le_max_right _ _
        omega
      omega
    have hn_ge_lower : N₀_lower ≤ n := by
      have : N₀_lower ≤ M := by
        rw [hM_def]
        have : N₀_lower ≤ max (max N₀_lower N₀_upper) 3 :=
          le_max_of_le_left (le_max_left _ _)
        omega
      omega
    have hn_ge_upper : N₀_upper ≤ n := by
      have : N₀_upper ≤ M := by
        rw [hM_def]
        have : N₀_upper ≤ max (max N₀_lower N₀_upper) 3 :=
          le_max_of_le_left (le_max_right _ _)
        omega
      omega
    -- Split on z ≥ n - 1 (sift collapse) vs z < n - 1 (Region II).
    by_cases h_z_collapse : n - 1 ≤ z
    · -- Sift collapse.
      have h_sift_zero : (goldbachSiftedPair n z : ℝ) = 0 :=
        goldbachSiftedPair_eq_zero_of_large_z_real hn_ge_3 h_z_collapse
      rw [h_sift_zero]
      have h_main_nn : 0 ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        apply mul_nonneg
        · apply mul_nonneg (le_of_lt hC₁pos) (by exact_mod_cast Nat.zero_le _)
        · exact le_of_lt (pairedBrunFactor_pos z)
      have h_res_nn : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
      linarith
    · -- Region II: √n ≤ z < n - 1.  Use AtSqrt + Mertens.
      push_neg at h_z_collapse
      have hz_lt_n : z < n := by omega
      have hAtSqrt_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n) := hAtSqrtBd n hn
      have h_anti : (goldbachSiftedPair n z : ℝ) ≤
          (goldbachSiftedPair n (Nat.sqrt n) : ℝ) :=
        goldbachSiftedPair_antitone_z_real n hz_ge_sqrt
      have h_upper : pairedBrunFactor (Nat.sqrt n) ≤
          C' / (Real.log (n : ℝ))^2 := hUpperBd n hn_ge_upper
      have h_lower : K_real / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z :=
        hLowerBd n z hn_ge_lower hz_ge_sqrt hz_lt_n
      have h_res_eq : refinedReservoir n (Nat.sqrt n) = refinedReservoir n z := by
        simp [refinedReservoir_def]
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_3
        linarith
      have hlog_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
      have hC'nn : 0 ≤ C' := le_of_lt hC'pos
      have hCnn : 0 ≤ C := le_of_lt hCpos
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_main_chain :
          C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤
            C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) := by
        apply mul_le_mul_of_nonneg_left h_upper
        exact mul_nonneg hCnn h_n_nn
      have h_bridge_le : C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) ≤
          C_bridge * (n : ℝ) * pairedBrunFactor z := by
        have h_lhs_eq : C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) =
            C_bridge * (n : ℝ) * (K_real / (Real.log (n : ℝ))^2) := by
          rw [hC_bridge_def]
          have hKne : K_real ≠ 0 := ne_of_gt hK_real_pos
          field_simp
        rw [h_lhs_eq]
        apply mul_le_mul_of_nonneg_left h_lower
        apply mul_nonneg hC_bridge_nn h_n_nn
      have h_main_bound : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤
          C_bridge * (n : ℝ) * pairedBrunFactor z :=
        le_trans h_main_chain h_bridge_le
      have hC_bridge_le_C₁ : C_bridge ≤ C₁ := by
        rw [hC₁_def]
        have : C_bridge ≤ max C_resid' C_bridge := le_max_right _ _
        linarith
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_C_to_C₁ : C_bridge * (n : ℝ) * pairedBrunFactor z ≤
          C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : C_bridge * ((n : ℝ) * pairedBrunFactor z) ≤
            C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right hC_bridge_le_C₁ h_n_pf_nn
        linarith [this]
      calc (goldbachSiftedPair n z : ℝ)
          ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ) := h_anti
        _ ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n) := hAtSqrt_n
        _ ≤ C_bridge * (n : ℝ) * pairedBrunFactor z
            + refinedReservoir n (Nat.sqrt n) := by linarith
        _ ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n (Nat.sqrt n) := by
            linarith
        _ = C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
            rw [h_res_eq]

/-! ## Section 4 — Honest report / status

The named open `PairedBrunMertensThirdLowerGap` is the **single**
remaining mathlib-gap input.  It is symmetric to the (closed) upper
gap `PairedBrunMertensThirdGap`, but requires a Mertens 2nd *upper*
bound (rather than the lower bound that gives the existing closure).

After P18-T2-real:

* `PairedBrunFactorRealMertensLower` is now reducible to a single
  named open `PairedBrunMertensThirdLowerGap`.

* `PairedMainTermAbsorption` can be closed from
  `BrunGoldbachPairedMainTermRefinedAtSqrt`,
  `PairedBrunFactorRealMertensLower`,
  `PairedBrunFactorMertensUpperAtSqrt` (closed by P18-T1),
  and `PairedMainTermResidualLowRegion`.

* The impossible nat-valued `PairedBrunFactorMertensLower` is no
  longer a bottleneck.

## Documentation summary -/

/-- **P18-T2-real summary marker** (no content theorem). -/
theorem pathC_p18_t2_real_summary : True := trivial

end PathCPairedBrunMertensLowerReal
end Gdbh
