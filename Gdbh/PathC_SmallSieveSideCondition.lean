import Gdbh.PathC_BrunRefinedComposition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Gdbh
namespace PathCSmallSieveSideCondition

open Real Filter Asymptotics

private lemma natSqrt_le_realSqrt (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h_sq_pow : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  have h_sq_real_pow : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast h_sq_pow
  have h_nn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le _
  exact (Real.le_sqrt h_nn h_n_nn).mpr h_sq_real_pow

private lemma one_le_sqrt_natCast {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hsqrt : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h1
  simpa using hsqrt

theorem smallSieveSideCondition_holds :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
      2 * ((Nat.sqrt n : ℝ) + 1) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
  have hLittleReal :
      (fun x : ℝ => (4 : ℝ) * (Real.log x) ^ (2 : ℝ)) =o[atTop]
        (fun x : ℝ => x ^ ((1 : ℝ) / 2)) := by
    exact
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).const_mul_left 4
  have hLittleNat := hLittleReal.comp_tendsto tendsto_natCast_atTop_atTop
  have hEventually := hLittleNat.eventuallyLE
  have hEventually' : ∀ᶠ n : ℕ in atTop,
      ‖(4 : ℝ) * (Real.log (n : ℝ)) ^ (2 : ℝ)‖
        ≤ ‖((n : ℝ) ^ ((1 : ℝ) / 2))‖ ∧ 2 ≤ n :=
    hEventually.and (eventually_ge_atTop 2)
  rcases eventually_atTop.1 hEventually' with ⟨N₁, hN₁⟩
  refine ⟨N₁, ?_⟩
  intro n hn _hn2
  rcases hN₁ n hn with ⟨hlog_norm, hn2⟩
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hleft_nonneg : 0 ≤ (4 : ℝ) * (Real.log (n : ℝ)) ^ (2 : ℝ) := by
    positivity
  have hright_nonneg : 0 ≤ ((n : ℝ) ^ ((1 : ℝ) / 2)) :=
    Real.rpow_nonneg hn_nonneg _
  have hlog_le_sqrt : (4 : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ Real.sqrt (n : ℝ) := by
    have hleft_norm :
        ‖(4 : ℝ) * (Real.log (n : ℝ)) ^ (2 : ℝ)‖
          = (4 : ℝ) * (Real.log (n : ℝ)) ^ (2 : ℝ) :=
      Real.norm_of_nonneg hleft_nonneg
    have hright_norm :
        ‖((n : ℝ) ^ ((1 : ℝ) / 2))‖ = ((n : ℝ) ^ ((1 : ℝ) / 2)) :=
      Real.norm_of_nonneg hright_nonneg
    have h : (4 : ℝ) * (Real.log (n : ℝ)) ^ (2 : ℝ)
        ≤ ((n : ℝ) ^ ((1 : ℝ) / 2)) := by
      have h' := hlog_norm
      rw [hleft_norm, hright_norm] at h'
      exact h'
    simpa [Real.sqrt_eq_rpow] using h
  have hsqrt_sum : (Nat.sqrt n : ℝ) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by
    have hNat := natSqrt_le_realSqrt n
    have hOne : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
      one_le_sqrt_natCast (by omega : 1 ≤ n)
    linarith
  calc
    2 * ((Nat.sqrt n : ℝ) + 1)
        ≤ 2 * (2 * Real.sqrt (n : ℝ)) := by
          nlinarith [hsqrt_sum]
    _ = 4 * Real.sqrt (n : ℝ) := by
          ring
    _ ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
          rw [le_div_iff₀ hlog_sq_pos]
          calc
            4 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2
                = ((4 : ℝ) * (Real.log (n : ℝ)) ^ 2) * Real.sqrt (n : ℝ) := by
                  ring
            _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
                  exact mul_le_mul_of_nonneg_right hlog_le_sqrt (Real.sqrt_nonneg _)
            _ = (n : ℝ) := by
                  rw [Real.mul_self_sqrt hn_nonneg]

end PathCSmallSieveSideCondition
end Gdbh
