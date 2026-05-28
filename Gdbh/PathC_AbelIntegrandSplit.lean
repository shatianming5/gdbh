/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Wave 1 / Path C Abel split closure
-/
import Gdbh.PathC_AbelInversion
import Gdbh.PathC_AbelPrimeRecipIdentity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Path C -- Abel integrand split

This file closes the purely linear integrand split used in the Abel
inversion bridge.  The only non-pointwise work is proving the finite
interval integrability needed for `integral_add`; this reuses
mathlib's `integrableOn_mul_sum_Icc` from Abel summation.
-/

namespace Gdbh
namespace PathCAbelIntegrandSplit

open Real Finset MeasureTheory
open Gdbh.PathCAbelInversion
open Gdbh.PathCAbelPrimeRecipIdentity

private lemma one_div_mul_log_integrableOn_Ioc (z : ℝ) :
    IntegrableOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Ioc (2 : ℝ) z) := by
  rw [← integrableOn_Icc_iff_integrableOn_Ioc]
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Icc (2 : ℝ) z) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ?_
      refine Real.continuousOn_log.mono ?_
      intro t ht
      have htpos : (0 : ℝ) < t := by linarith [ht.1]
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using htpos.ne'
    · intro t ht
      have htpos : (0 : ℝ) < t := by linarith [ht.1]
      have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact mul_ne_zero htpos.ne' hlogpos.ne'
  exact hcont.integrableOn_Icc

private lemma inv_mul_log_sq_integrableOn_Icc (z : ℝ) :
    IntegrableOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Icc (2 : ℝ) z) := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Icc (2 : ℝ) z) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ?_
      refine ContinuousOn.pow ?_ 2
      refine Real.continuousOn_log.mono ?_
      intro t ht
      have htpos : (0 : ℝ) < t := by linarith [ht.1]
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using htpos.ne'
    · intro t ht
      have htpos : (0 : ℝ) < t := by linarith [ht.1]
      have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact mul_ne_zero htpos.ne' (pow_ne_zero 2 hlogpos.ne')
  exact hcont.integrableOn_Icc

private lemma mertens_integrand_integrableOn_Icc (z : ℝ) :
    IntegrableOn
      (fun t : ℝ => mertensFirstSum t / (t * (Real.log t)^2))
      (Set.Icc (2 : ℝ) z) := by
  have hg := inv_mul_log_sq_integrableOn_Icc z
  have hmul : IntegrableOn
      (fun t : ℝ =>
        (1 / (t * (Real.log t)^2)) *
          ∑ k ∈ Finset.Icc 0 (Nat.floor t), cFn k)
      (Set.Icc (2 : ℝ) z) := by
    exact integrableOn_mul_sum_Icc
      (c := cFn) (m := 0) (a := (2 : ℝ)) (b := z) (by norm_num) hg
  refine hmul.congr_fun ?_ measurableSet_Icc
  intro t _ht
  change (1 / (t * Real.log t ^ 2)) *
      (∑ k ∈ Finset.Icc 0 (Nat.floor t), cFn k)
        = mertensFirstSum t / (t * Real.log t ^ 2)
  rw [sum_cFn_eq_mertensFirstSum t]
  ring

private lemma mertens_integrand_integrableOn_Ioc (z : ℝ) :
    IntegrableOn
      (fun t : ℝ => mertensFirstSum t / (t * (Real.log t)^2))
      (Set.Ioc (2 : ℝ) z) :=
  (mertens_integrand_integrableOn_Icc z).mono_set Set.Ioc_subset_Icc_self

private lemma error_integrand_integrableOn_Ioc (z : ℝ) :
    IntegrableOn
      (fun t : ℝ => (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2))
      (Set.Ioc (2 : ℝ) z) := by
  have hf := mertens_integrand_integrableOn_Ioc z
  have hg := one_div_mul_log_integrableOn_Ioc z
  have hsub : IntegrableOn
      (fun t : ℝ =>
        mertensFirstSum t / (t * (Real.log t)^2) - 1 / (t * Real.log t))
      (Set.Ioc (2 : ℝ) z) := hf.sub hg
  refine hsub.congr_fun ?_ measurableSet_Ioc
  intro t ht
  have htpos : (0 : ℝ) < t := by linarith [ht.1]
  have htne : t ≠ 0 := htpos.ne'
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  have hlogne : Real.log t ≠ 0 := hlogpos.ne'
  have hsqne : (Real.log t)^2 ≠ 0 := pow_ne_zero _ hlogne
  field_simp [htne, hlogne, hsqne]

/-- The Abel integrand splits into the elementary log integral plus the
Mertens-error integral. -/
theorem abelIntegrandSplit_holds : AbelIntegrandSplit := by
  intro z _hz
  have hg := one_div_mul_log_integrableOn_Ioc z
  have hh := error_integrand_integrableOn_Ioc z
  have hpoint : ∀ t ∈ Set.Ioc (2 : ℝ) z,
      mertensFirstSum t / (t * (Real.log t)^2)
        = 1 / (t * Real.log t)
          + (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have htne : t ≠ 0 := htpos.ne'
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlogne : Real.log t ≠ 0 := hlogpos.ne'
    have hsqne : (Real.log t)^2 ≠ 0 := pow_ne_zero _ hlogne
    field_simp [htne, hlogne, hsqne]
    ring
  have hcongr :
      (∫ t in Set.Ioc (2 : ℝ) z,
          mertensFirstSum t / (t * (Real.log t)^2))
        = ∫ t in Set.Ioc (2 : ℝ) z,
            (1 / (t * Real.log t)
              + (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    exact hpoint t ht
  rw [hcongr]
  exact MeasureTheory.integral_add hg hh

end PathCAbelIntegrandSplit
end Gdbh
