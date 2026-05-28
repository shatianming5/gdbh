/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P16-T4 (Phase 16 / closure of `LogReciprocalIntegralAsymptotic`)
-/
import Gdbh.PathC_AbelInversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Path C — `LogReciprocalIntegralAsymptotic` closure (P16-T4)

This file closes the named open Prop
`Gdbh.PathCAbelInversion.LogReciprocalIntegralAsymptotic`:

```
∃ C : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
  |(∫ t in Set.Ioc (2 : ℝ) (z : ℝ), 1 / (t * Real.log t))
      - Real.log (Real.log (z : ℝ))| ≤ C
```

The integrand `1 / (t · log t)` admits the elementary antiderivative
`log (log t)` on `(1, ∞)`.  By the Fundamental Theorem of Calculus,

```
∫_2^z 1/(t · log t) dt  =  log (log z)  −  log (log 2)
```

for `z ≥ 2`.  Consequently the bound holds with
`C := |Real.log (Real.log 2)|` and `z₀ := 3`.

## Axiom budget

Only `Classical.choice, Quot.sound, propext`.
-/

namespace Gdbh
namespace PathCLogRecipIntegral

open Real MeasureTheory Set

/-- The key derivative identity: `d/dt log(log t) = 1/(t · log t)` on
`(1, ∞)`.  Stated as a `HasDerivAt`. -/
lemma hasDerivAt_log_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => Real.log (Real.log x))
      (1 / (t * Real.log t)) t := by
  have htpos : 0 < t := lt_trans Real.zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
  -- inner derivative: `d/dt log t = 1/t = t⁻¹`
  have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
  -- chain rule: derivative of `log ∘ log` at `t` is `(t⁻¹) / log t`
  have h2 : HasDerivAt (fun x : ℝ => Real.log (Real.log x))
      (t⁻¹ / Real.log t) t := h1.log hlog_ne
  -- rewrite the derivative value as `1 / (t · log t)`
  have heq : t⁻¹ / Real.log t = 1 / (t * Real.log t) := by
    field_simp
  rw [heq] at h2
  exact h2

/-- The integrand `1 / (t · log t)` is continuous on `Set.Icc 2 z`
whenever `2 ≤ z` (since on this interval `t ≥ 2 > 1` so both `t` and
`log t` are positive, hence nonzero). -/
lemma continuousOn_one_div_t_log_t {z : ℝ} (_hz : 2 ≤ z) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Icc 2 z) := by
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · -- t · log t is continuous on the interval (log is continuous on `{x ≠ 0}`)
    refine ContinuousOn.mul continuousOn_id ?_
    refine Real.continuousOn_log.mono ?_
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht2
    exact ne_of_gt ht_pos
  · -- nonzero on the interval
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le one_lt_two ht2
    have htpos : 0 < t := lt_trans Real.zero_lt_one ht1
    have hlogpos : 0 < Real.log t := Real.log_pos ht1
    exact ne_of_gt (mul_pos htpos hlogpos)

/-- **Fundamental Theorem of Calculus** evaluation: for `2 ≤ z`,

`∫_2^z 1 / (t · log t) dt = log (log z) − log (log 2)`. -/
lemma intervalIntegral_one_div_t_log_t_eq {z : ℝ} (hz : 2 ≤ z) :
    (∫ t in (2 : ℝ)..z, 1 / (t * Real.log t))
      = Real.log (Real.log z) - Real.log (Real.log 2) := by
  -- Use FTC on [2, z]; the antiderivative is `F(t) = log (log t)`,
  -- with derivative `F'(t) = 1/(t · log t)` on `(1, ∞)`.
  have hcont_F : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.Icc 2 z) := by
    refine ContinuousOn.comp (t := {x : ℝ | x ≠ 0}) Real.continuousOn_log ?_ ?_
    · -- inner: log is continuous on Icc 2 z since 2 > 0
      refine Real.continuousOn_log.mono ?_
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht_pos : 0 < t :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht2
      exact ne_of_gt ht_pos
    · -- mapsTo: log t ≠ 0 for t ∈ Icc 2 z
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le one_lt_two ht2
      exact ne_of_gt (Real.log_pos ht1)
  have hderiv : ∀ t ∈ Set.Ioo (2 : ℝ) z,
      HasDerivAt (fun x : ℝ => Real.log (Real.log x))
        (1 / (t * Real.log t)) t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le one_lt_two (le_of_lt ht.1)
    exact hasDerivAt_log_log ht1
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 z :=
    (continuousOn_one_div_t_log_t hz).intervalIntegrable_of_Icc hz
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t : ℝ => Real.log (Real.log t))
    (f' := fun t : ℝ => 1 / (t * Real.log t))
    hz hcont_F hderiv hint

/-- The Lebesgue integral over `Set.Ioc 2 z` equals the interval
integral `∫ 2..z` when `2 ≤ z`. -/
lemma integral_Ioc_eq_intervalIntegral {z : ℝ} (hz : 2 ≤ z)
    (f : ℝ → ℝ) :
    (∫ t in Set.Ioc (2 : ℝ) z, f t) = ∫ t in (2 : ℝ)..z, f t := by
  rw [intervalIntegral.integral_of_le hz]

/-- **Exact evaluation** of the Lebesgue integral form. -/
lemma integral_Ioc_one_div_t_log_t_eq {z : ℝ} (hz : 2 ≤ z) :
    (∫ t in Set.Ioc (2 : ℝ) z, 1 / (t * Real.log t))
      = Real.log (Real.log z) - Real.log (Real.log 2) := by
  rw [integral_Ioc_eq_intervalIntegral hz, intervalIntegral_one_div_t_log_t_eq hz]

/-- **P16-T4 deliverable**: closure of
`Gdbh.PathCAbelInversion.LogReciprocalIntegralAsymptotic`.

The bound is in fact an exact identity (modulo the constant
`log log 2`), so the asymptotic bound holds with the explicit constant
`C := |log (log 2)|` for all `z ≥ 3`. -/
theorem logReciprocalIntegralAsymptotic_closed :
    Gdbh.PathCAbelInversion.LogReciprocalIntegralAsymptotic := by
  refine ⟨|Real.log (Real.log 2)|, 3, ?_⟩
  intro z hz
  -- z ≥ 3 ≥ 2, so the FTC evaluation applies.
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by
    have : (2 : ℝ) ≤ 3 := by norm_num
    refine this.trans ?_
    have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    exact this
  -- Rewrite the LHS as `log(log z) - log(log 2) - log(log z)`.
  have hI : (∫ t in Set.Ioc (2 : ℝ) (z : ℝ), 1 / (t * Real.log t))
      = Real.log (Real.log (z : ℝ)) - Real.log (Real.log 2) :=
    integral_Ioc_one_div_t_log_t_eq hz2
  rw [hI]
  -- |(log log z - log log 2) - log log z| = |- log log 2| = |log log 2|
  have hcalc :
      (Real.log (Real.log (z : ℝ)) - Real.log (Real.log 2))
        - Real.log (Real.log (z : ℝ))
        = -Real.log (Real.log 2) := by ring
  rw [hcalc, abs_neg]

end PathCLogRecipIntegral
end Gdbh
