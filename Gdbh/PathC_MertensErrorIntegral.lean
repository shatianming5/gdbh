/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Wave 2 / Path C Abel error-integral closure
-/
import Gdbh.PathC_AbelInversion
import Gdbh.PathC_MertensFirstClosure
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Path C -- Mertens error-integral bound

This file closes the named Abel-inversion component
`Gdbh.PathCAbelInversion.MertensErrorIntegralBound`.

The proof uses the already closed integer Mertens-1 bound
`Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds`.
We first extend the integer-point estimate to a uniform real-variable
bound for `mertensFirstSum t - log t` on `t ≥ 2`; the finitely many
pre-asymptotic integer floors are absorbed into an explicit finite
maximum.  The integral is then dominated by
`K / (t * log t ^ 2)`, whose integral from `2` to `z` is bounded by
`K / log 2`.
-/

namespace Gdbh
namespace PathCMertensErrorIntegral

open Real Finset MeasureTheory Set
open Gdbh.PathCAbelInversion

/-- A uniform real-variable envelope for the Mertens-1 error. -/
noncomputable def mertensErrorEnvelope (B : ℝ) (z₀ : ℕ) : ℝ :=
  max (B + Real.log 2)
    ((∑ p ∈ (Finset.Icc 2 (max z₀ 2)).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ))
      + Real.log (max z₀ 2 : ℝ))

private lemma log_floor_sub_log_le_log_two {t : ℝ} (ht : (2 : ℝ) ≤ t) :
    |Real.log (Nat.floor t : ℝ) - Real.log t| ≤ Real.log 2 := by
  let n := Nat.floor t
  have hn2 : 2 ≤ n := Nat.le_floor ht
  have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htlt : t < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one t
  have hnpos_nat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htpos : 0 < t := lt_of_lt_of_le hnpos hnt
  have hlogn_le_logt : Real.log (n : ℝ) ≤ Real.log t :=
    Real.log_le_log hnpos hnt
  have hn1_le_2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have ht_le_2n : t ≤ 2 * (n : ℝ) := (le_of_lt htlt).trans hn1_le_2n
  have hlogt_le_log2n : Real.log t ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log htpos ht_le_2n
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne']
  have hdiff_nonpos : Real.log (n : ℝ) - Real.log t ≤ 0 := by linarith
  rw [abs_of_nonpos hdiff_nonpos]
  linarith

private lemma mertensFirstSum_sub_log_bound_of_m1_large
    {B : ℝ} {z₀ : ℕ}
    (hM1 : ∀ z : ℕ, z₀ ≤ z →
      |(∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ)) - Real.log (z : ℝ)| ≤ B)
    {t : ℝ} (hz₀t : (z₀ : ℝ) ≤ t) (ht2 : (2 : ℝ) ≤ t) :
    |mertensFirstSum t - Real.log t| ≤ B + Real.log 2 := by
  let n := Nat.floor t
  have hz₀n : z₀ ≤ n := Nat.le_floor hz₀t
  have hMn :
      |(∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ)) - Real.log (n : ℝ)| ≤ B :=
    hM1 n hz₀n
  have hM_eq : mertensFirstSum t =
      ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
    simp [mertensFirstSum, n]
  have hlogdiff : |Real.log (n : ℝ) - Real.log t| ≤ Real.log 2 := by
    simpa [n] using log_floor_sub_log_le_log_two ht2
  calc
    |mertensFirstSum t - Real.log t|
        = |((∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
              Real.log (p : ℝ) / (p : ℝ)) - Real.log (n : ℝ))
            + (Real.log (n : ℝ) - Real.log t)| := by
          rw [hM_eq]
          ring_nf
    _ ≤ |(∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
            Real.log (p : ℝ) / (p : ℝ)) - Real.log (n : ℝ)|
          + |Real.log (n : ℝ) - Real.log t| := abs_add_le _ _
    _ ≤ B + Real.log 2 := add_le_add hMn hlogdiff

private lemma prime_log_div_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

private lemma mertensFirstSum_nonneg (t : ℝ) : 0 ≤ mertensFirstSum t := by
  unfold mertensFirstSum
  refine Finset.sum_nonneg ?_
  intro p hp
  exact prime_log_div_nonneg (by simpa using (Finset.mem_filter.mp hp).2)

private lemma mertensFirstSum_le_prefix {t : ℝ} {N : ℕ}
    (hfloorN : Nat.floor t ≤ N) :
    mertensFirstSum t ≤
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
  unfold mertensFirstSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hfloorN⟩, hp.2⟩
  · intro p hp _hnot
    exact prime_log_div_nonneg (by simpa using (Finset.mem_filter.mp hp).2)

private lemma mertensFirstSum_sub_log_bound_of_m1
    {B : ℝ} {z₀ : ℕ}
    (hM1 : ∀ z : ℕ, z₀ ≤ z →
      |(∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ)) - Real.log (z : ℝ)| ≤ B)
    {t : ℝ} (ht2 : (2 : ℝ) ≤ t) :
    |mertensFirstSum t - Real.log t| ≤ mertensErrorEnvelope B z₀ := by
  let n := Nat.floor t
  by_cases hlarge : z₀ ≤ n
  · have hz₀t : (z₀ : ℝ) ≤ t := by
      have hzn : (z₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlarge
      have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
      exact hzn.trans hnt
    exact (mertensFirstSum_sub_log_bound_of_m1_large hM1 hz₀t ht2).trans
      (le_max_left _ _)
  · have hn_le_z₀ : n ≤ z₀ := by omega
    have hfloorN : Nat.floor t ≤ max z₀ 2 := by
      simpa [n] using le_trans hn_le_z₀ (le_max_left z₀ 2)
    have hMle := mertensFirstSum_le_prefix (t := t) (N := max z₀ 2) hfloorN
    have hMnonneg := mertensFirstSum_nonneg t
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have habs : |mertensFirstSum t - Real.log t| ≤
        mertensFirstSum t + Real.log t := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have ht_le_N : t ≤ (max z₀ 2 : ℝ) := by
      have htlt : t < (n : ℝ) + 1 := by
        simpa [n] using Nat.lt_floor_add_one t
      have hnlt : n < z₀ := Nat.lt_of_not_ge hlarge
      have hn1_le_z₀ : n + 1 ≤ z₀ := by omega
      have hz₀_le_N : (z₀ : ℝ) ≤ (max z₀ 2 : ℝ) := by
        exact_mod_cast le_max_left z₀ 2
      have htmp : (n : ℝ) + 1 ≤ (z₀ : ℝ) := by exact_mod_cast hn1_le_z₀
      exact (le_of_lt htlt).trans (htmp.trans hz₀_le_N)
    have hlog_le : Real.log t ≤ Real.log (max z₀ 2 : ℝ) :=
      Real.log_le_log (by linarith) ht_le_N
    have hfinite : |mertensFirstSum t - Real.log t| ≤
        (∑ p ∈ (Finset.Icc 2 (max z₀ 2)).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ)) + Real.log (max z₀ 2 : ℝ) := by
      linarith
    exact hfinite.trans (le_max_right _ _)

private lemma mertensErrorEnvelope_nonneg {B : ℝ} {z₀ : ℕ} (hB : 0 ≤ B) :
    0 ≤ mertensErrorEnvelope B z₀ := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  exact le_trans (add_nonneg hB hlog2) (le_max_left _ _)

private lemma error_integrand_norm_le_envelope
    {B : ℝ} {z₀ : ℕ}
    (hM1 : ∀ z : ℕ, z₀ ≤ z →
      |(∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ)) - Real.log (z : ℝ)| ≤ B)
    {t : ℝ} (ht2 : (2 : ℝ) ≤ t) :
    ‖(mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)‖
      ≤ mertensErrorEnvelope B z₀ * (1 / (t * (Real.log t)^2)) := by
  have hpt := mertensFirstSum_sub_log_bound_of_m1 hM1 ht2
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hdenpos : 0 < t * (Real.log t)^2 := mul_pos htpos (sq_pos_of_pos hlogpos)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
  calc
    |mertensFirstSum t - Real.log t| / (t * Real.log t ^ 2)
        ≤ mertensErrorEnvelope B z₀ / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right hpt hdenpos.le
    _ = mertensErrorEnvelope B z₀ * (1 / (t * Real.log t ^ 2)) := by ring

private lemma hasDerivAt_neg_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => -(Real.log x)⁻¹)
      (1 / (t * (Real.log t)^2)) t := by
  have htpos : 0 < t := lt_trans Real.zero_lt_one ht
  have htne : t ≠ 0 := htpos.ne'
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogne : Real.log t ≠ 0 := hlogpos.ne'
  have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
  have h2 : HasDerivAt (fun x : ℝ => (Real.log x)⁻¹)
      (-(t⁻¹) / (Real.log t)^2) t := h1.inv hlogne
  have h3 : HasDerivAt (fun x : ℝ => -(Real.log x)⁻¹)
      (- (-(t⁻¹) / (Real.log t)^2)) t := h2.neg
  convert h3 using 1
  field_simp

private lemma continuousOn_neg_inv_log {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun x : ℝ => -(Real.log x)⁻¹) (Set.Icc a b) := by
  refine ContinuousOn.neg ?_
  refine ContinuousOn.inv₀ ?_ ?_
  · refine Real.continuousOn_log.mono ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (lt_trans Real.zero_lt_one ha) hx.1
    exact hxpos.ne'
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
    exact (Real.log_pos hx1).ne'

private lemma continuousOn_one_div_t_log_sq {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Icc a b) := by
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.mul continuousOn_id ?_
    refine ContinuousOn.pow ?_ 2
    refine Real.continuousOn_log.mono ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (lt_trans Real.zero_lt_one ha) hx.1
    exact hxpos.ne'
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (lt_trans Real.zero_lt_one ha) hx.1
    have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
    have hlogne : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    exact mul_ne_zero hxpos.ne' (pow_ne_zero _ hlogne)

private lemma intervalIntegral_one_div_t_log_sq_eq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * (Real.log t)^2)) =
      1 / Real.log a - 1 / Real.log b := by
  have hcontF : ContinuousOn (fun x : ℝ => -(Real.log x)⁻¹) (Set.Icc a b) :=
    continuousOn_neg_inv_log ha
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun x : ℝ => -(Real.log x)⁻¹)
        (1 / (t * (Real.log t)^2)) t := by
    intro t ht
    exact hasDerivAt_neg_inv_log (lt_of_lt_of_le ha (le_of_lt ht.1))
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * (Real.log t)^2))
      volume a b :=
    (continuousOn_one_div_t_log_sq ha).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => -(Real.log x)⁻¹)
    (f' := fun t : ℝ => 1 / (t * (Real.log t)^2))
    hab hcontF hderiv hint
  rw [hftc]
  ring

private lemma intervalIntegral_one_div_t_log_sq_le_two {z : ℕ} (hz : 2 ≤ z) :
    (∫ t in (2 : ℝ)..(z : ℝ), 1 / (t * (Real.log t)^2)) ≤
      1 / Real.log 2 := by
  have hzreal : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  rw [intervalIntegral_one_div_t_log_sq_eq (by norm_num : (1 : ℝ) < 2) hzreal]
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this hzreal)
  have hnonneg : 0 ≤ 1 / Real.log (z : ℝ) := by positivity
  linarith

/-- The Mertens-1 error integral in the Abel inversion is uniformly bounded. -/
theorem mertensErrorIntegralBound_holds : MertensErrorIntegralBound := by
  obtain ⟨B₁, z₁, hM1⟩ :=
    Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds
  have hB₁_nonneg : 0 ≤ B₁ := by
    have hz : z₁ ≤ max z₁ 2 := le_max_left _ _
    exact le_trans (abs_nonneg _) (hM1 (max z₁ 2) hz)
  let K := mertensErrorEnvelope B₁ z₁
  have hK_nonneg : 0 ≤ K := by
    simpa [K] using (mertensErrorEnvelope_nonneg (B := B₁) (z₀ := z₁) hB₁_nonneg)
  intro _B _hB
  refine ⟨K * (1 / Real.log 2), 2, ?_⟩
  intro z hz
  have hzreal : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  rw [← intervalIntegral.integral_of_le hzreal]
  have hpoint : ∀ᵐ t ∂volume, t ∈ Set.Ioc (2 : ℝ) (z : ℝ) →
      ‖(mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)‖
        ≤ K * (1 / (t * (Real.log t)^2)) := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_of_lt ht.1
    simpa [K] using error_integrand_norm_le_envelope (B := B₁) (z₀ := z₁) hM1 ht2
  have hbound : IntervalIntegrable
      (fun t : ℝ => K * (1 / (t * (Real.log t)^2))) volume (2 : ℝ) (z : ℝ) := by
    have hcont : ContinuousOn
        (fun t : ℝ => K * (1 / (t * (Real.log t)^2)))
        (Set.Icc (2 : ℝ) (z : ℝ)) := by
      exact (continuousOn_one_div_t_log_sq (a := (2 : ℝ)) (b := (z : ℝ))
        (by norm_num : (1 : ℝ) < 2)).const_mul K
    exact hcont.intervalIntegrable_of_Icc hzreal
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (a := (2 : ℝ)) (b := (z : ℝ))
    (f := fun t : ℝ => (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2))
    (g := fun t : ℝ => K * (1 / (t * (Real.log t)^2)))
    hzreal hpoint hbound
  rw [Real.norm_eq_abs] at hnorm
  have hgint_le :
      (∫ t in (2 : ℝ)..(z : ℝ), K * (1 / (t * (Real.log t)^2)))
        ≤ K * (1 / Real.log 2) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (intervalIntegral_one_div_t_log_sq_le_two hz) hK_nonneg
  exact hnorm.trans hgint_le

end PathCMertensErrorIntegral
end Gdbh
