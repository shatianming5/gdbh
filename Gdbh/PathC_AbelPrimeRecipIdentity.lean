/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P16-T3 (Phase 16 / Abel-summation prime-reciprocal identity)
-/
import Gdbh.PathC_AbelInversion
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Path C — Abel summation prime-reciprocal identity (P16-T3)

This file closes **unconditionally** the named open Prop
`Gdbh.PathCAbelInversion.AbelPrimeReciprocalIdentity` introduced in
`Gdbh/PathC_AbelInversion.lean`.

## Mathematical content

We instantiate mathlib's `sum_mul_eq_sub_integral_mul₁` (from
`Mathlib.NumberTheory.AbelSummation`) with
* `c(k) = if k.Prime then log k / k else 0` (so `c 0 = c 1 = 0`),
* `f(t) = (log t)⁻¹` (smooth on `[2, z]` since `log 2 > 0`),
* `deriv f (t) = -1/(t · (log t)^2)`.

The resulting Abel-summation identity reads
```
Σ_{2 ≤ p ≤ z, p prime} 1/p
  = mertensFirstSum z / log z
    + ∫ t in Ioc 2 z, mertensFirstSum t / (t · (log t)^2) ,
```
which is exactly `AbelPrimeReciprocalIdentity` (with witness `z₀ = 2`).

## Axiom budget

The theorem `abelPrimeReciprocalIdentity` below is closed using only
`[Classical.choice, Quot.sound, propext]`.
-/

namespace Gdbh
namespace PathCAbelPrimeRecipIdentity

open Real Finset MeasureTheory
open Gdbh.PathCAbelInversion

/-! ## Section 1 — The Abel coefficient sequence -/

/-- The Abel coefficient sequence: `cFn k = log k / k` if `k` is prime,
otherwise `0`.  This is the natural sequence to feed into
Abel-summation for the prime-reciprocal sum. -/
noncomputable def cFn (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0

lemma cFn_zero : cFn 0 = 0 := by
  unfold cFn; simp [Nat.not_prime_zero]

lemma cFn_one : cFn 1 = 0 := by
  unfold cFn; simp [Nat.not_prime_one]

/-- The Abel coefficient sequence summed over `Icc 0 n` recovers
`mertensFirstSum` at integer points. -/
lemma sum_cFn_eq_mertensFirstSum_nat (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, cFn k = mertensFirstSum (n : ℝ) := by
  classical
  unfold mertensFirstSum cFn
  rw [Nat.floor_natCast]
  -- Now both sides are sums of `if Nat.Prime k then log k / k else ?`.
  -- Use `sum_filter` (← direction) to turn the RHS into an `if`-sum.
  rw [show (∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
      = ∑ p ∈ Finset.Icc 2 n,
          (if p.Prime then Real.log (p : ℝ) / (p : ℝ) else 0) from
      Finset.sum_filter _ _]
  -- LHS is on `Icc 0 n`, RHS on `Icc 2 n`. Both differ only on {0, 1},
  -- where the integrand is 0 (since 0, 1 are not prime).
  symm
  -- Drop the `[0, 1]` portion of the sum (the integrand is 0 there).
  have hsub : Finset.Icc 2 n ⊆ Finset.Icc 0 n :=
    Finset.Icc_subset_Icc (Nat.zero_le _) le_rfl
  refine
    Finset.sum_subset (f := fun p : ℕ =>
      if p.Prime then Real.log (p : ℝ) / (p : ℝ) else 0) hsub ?_
  intro k hk hkne
  rw [Finset.mem_Icc] at hk
  -- k ∈ Icc 0 n but k ∉ Icc 2 n, so k ≤ 1.
  have hk_le_one : k ≤ 1 := by
    by_contra h
    apply hkne
    rw [Finset.mem_Icc]
    refine ⟨?_, hk.2⟩
    omega
  interval_cases k
  · simp [Nat.not_prime_zero]
  · simp [Nat.not_prime_one]

/-- For any real `t ≥ 0`, the partial sum of `cFn` up to `⌊t⌋₊` equals
`mertensFirstSum t`. -/
lemma sum_cFn_eq_mertensFirstSum (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 (Nat.floor t), cFn k = mertensFirstSum t := by
  -- Reduce to the natural-number version with `n = ⌊t⌋₊`.
  have h := sum_cFn_eq_mertensFirstSum_nat (Nat.floor t)
  -- Note: mertensFirstSum (n : ℝ) uses ⌊(n : ℝ)⌋₊ = n, while
  -- mertensFirstSum t uses ⌊t⌋₊. We need to unfold and match.
  unfold mertensFirstSum at h ⊢
  rw [Nat.floor_natCast] at h
  exact h

/-! ## Section 2 — The weight function and its derivative -/

/-- The Abel-summation weight: `fFn t = (log t)⁻¹`.  On `[2, z]` this
is `1/log t`. -/
noncomputable def fFn (t : ℝ) : ℝ := (Real.log t)⁻¹

/-- For `t ≥ 2`, `log t ≥ log 2 > 0`. -/
lemma log_pos_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : 0 < Real.log t := by
  apply Real.log_pos
  linarith

lemma log_ne_zero_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : Real.log t ≠ 0 :=
  (log_pos_of_two_le ht).ne'

/-- `fFn` is differentiable on `[2, b]` for any `b`. -/
lemma fFn_differentiableAt {t : ℝ} (ht : (2 : ℝ) ≤ t) :
    DifferentiableAt ℝ fFn t := by
  unfold fFn
  have hlog : Real.log t ≠ 0 := log_ne_zero_of_two_le ht
  have htpos : (0 : ℝ) < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have h1 : DifferentiableAt ℝ Real.log t :=
    (Real.differentiableAt_log htne)
  exact h1.inv hlog

/-- The derivative of `fFn` at `t ≥ 2`: `deriv fFn t = -1/(t * (log t)^2)`. -/
lemma fFn_hasDerivAt {t : ℝ} (ht : (2 : ℝ) ≤ t) :
    HasDerivAt fFn (-(1 / (t * (Real.log t)^2))) t := by
  unfold fFn
  have hlog : Real.log t ≠ 0 := log_ne_zero_of_two_le ht
  have htpos : (0 : ℝ) < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have h1 : HasDerivAt Real.log (t⁻¹) t := Real.hasDerivAt_log htne
  have h2 : HasDerivAt (fun x => (Real.log x)⁻¹) (-(t⁻¹) / (Real.log t) ^ 2) t :=
    h1.inv hlog
  -- Massage `-(t⁻¹) / (log t)^2` to `-(1 / (t * (log t)^2))`.
  convert h2 using 1
  field_simp

/-- The derivative function `t ↦ -1/(t · (log t)^2)` is continuous on
`Icc 2 b`. -/
lemma derivFFn_continuousOn_Icc (b : ℝ) :
    ContinuousOn (fun t => -(1 / (t * (Real.log t)^2))) (Set.Icc (2 : ℝ) b) := by
  -- t * (log t)^2 ≠ 0 on Icc 2 b.
  refine ContinuousOn.neg ?_
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.mul continuousOn_id ?_
    refine ContinuousOn.pow ?_ 2
    -- `Real.log` is continuous away from 0; on Icc 2 b, t ≥ 2 > 0.
    refine Real.continuousOn_log.mono ?_
    intro t ht
    have h2t : (2 : ℝ) ≤ t := ht.1
    have : t ≠ 0 := by
      have : (0 : ℝ) < t := by linarith
      exact this.ne'
    exact this
  · intro t ht
    have h2t : (2 : ℝ) ≤ t := ht.1
    have htpos : (0 : ℝ) < t := by linarith
    have hlogne : Real.log t ≠ 0 := log_ne_zero_of_two_le h2t
    have hsqne : Real.log t ^ 2 ≠ 0 := pow_ne_zero _ hlogne
    exact mul_ne_zero htpos.ne' hsqne

/-- Differentiability of `fFn` on `Icc 2 b`. -/
lemma fFn_diff_on_Icc (b : ℝ) :
    ∀ t ∈ Set.Icc (2 : ℝ) b, DifferentiableAt ℝ fFn t := by
  intro t ht
  exact fFn_differentiableAt ht.1

/-- `deriv fFn` agrees pointwise with `t ↦ -1/(t · (log t)^2)` on
`Icc 2 b`. -/
lemma derivFFn_eq (b : ℝ) :
    ∀ t ∈ Set.Icc (2 : ℝ) b,
      deriv fFn t = -(1 / (t * (Real.log t)^2)) := by
  intro t ht
  exact (fFn_hasDerivAt ht.1).deriv

/-- Integrability of `deriv fFn` on `Icc 2 b`. -/
lemma derivFFn_integrableOn (b : ℝ) :
    IntegrableOn (deriv fFn) (Set.Icc (2 : ℝ) b) := by
  -- (deriv fFn) agrees with `t ↦ -1/(t · log² t)` on Icc 2 b, which is
  -- continuous, hence integrable on a compact set.
  have hcont : ContinuousOn (fun t => -(1 / (t * (Real.log t)^2)))
      (Set.Icc (2 : ℝ) b) := derivFFn_continuousOn_Icc b
  have hint : IntegrableOn (fun t => -(1 / (t * (Real.log t)^2)))
      (Set.Icc (2 : ℝ) b) :=
    hcont.integrableOn_Icc
  refine hint.congr_fun ?_ measurableSet_Icc
  intro t ht
  symm
  exact derivFFn_eq b t ht

/-! ## Section 3 — The Abel identity (main result) -/

/-- For a prime `p ≥ 2`, `(log p)⁻¹ * (log p / p) = 1/p`. -/
lemma fFn_mul_cFn_at_prime {p : ℕ} (hp : p.Prime) :
    fFn (p : ℝ) * cFn p = 1 / (p : ℝ) := by
  unfold fFn cFn
  have h2le : (2 : ℕ) ≤ p := hp.two_le
  have h2le_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2le
  have hlogne : Real.log (p : ℝ) ≠ 0 := log_ne_zero_of_two_le h2le_real
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by linarith
    exact_mod_cast this
  have hpne : (p : ℝ) ≠ 0 := hppos.ne'
  simp [if_pos hp]
  field_simp

/-- For a non-prime `k`, `fFn k * cFn k = 0`. -/
lemma fFn_mul_cFn_at_nonprime {k : ℕ} (hp : ¬ k.Prime) :
    fFn (k : ℝ) * cFn k = 0 := by
  unfold cFn
  simp [if_neg hp]

/-- The LHS of the Abel-summation lemma, applied to our `cFn` and `fFn`,
equals the prime-reciprocal sum `∑_{2 ≤ p ≤ z, prime} 1/p`. -/
lemma lhs_eq_prime_recip_sum (z : ℕ) :
    ∑ k ∈ Finset.Icc 0 z, fFn (k : ℝ) * cFn k
      = ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  classical
  -- Restrict the LHS to primes (non-prime terms are 0).
  have hLHS_filter :
      ∑ k ∈ Finset.Icc 0 z, fFn (k : ℝ) * cFn k
        = ∑ k ∈ (Finset.Icc 0 z).filter Nat.Prime, fFn (k : ℝ) * cFn k := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro k _ hne
    by_contra hnp
    apply hne
    exact fFn_mul_cFn_at_nonprime hnp
  rw [hLHS_filter]
  -- Restrict the index range from Icc 0 z to Icc 2 z (primes are ≥ 2).
  have hindex : (Finset.Icc 0 z).filter Nat.Prime
                  = (Finset.Icc 2 z).filter Nat.Prime := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨fun ⟨⟨_, hkz⟩, hp⟩ => ⟨⟨hp.two_le, hkz⟩, hp⟩, ?_⟩
    rintro ⟨⟨h2k, hkz⟩, hp⟩
    exact ⟨⟨Nat.zero_le _, hkz⟩, hp⟩
  rw [hindex]
  -- Rewrite each prime term as 1/p.
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter] at hp
  exact fFn_mul_cFn_at_prime hp.2

/-- **Headline (P16-T3)**: `AbelPrimeReciprocalIdentity` is true,
unconditionally.

We use witness `z₀ = 2`.  The identity is the direct instantiation of
`sum_mul_eq_sub_integral_mul₁` with `c k = log k / k · [k prime]` and
`f t = 1/log t`. -/
theorem abelPrimeReciprocalIdentity : AbelPrimeReciprocalIdentity := by
  refine ⟨2, ?_⟩
  intro z hz
  have hz_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  -- Step 1: apply Abel summation.
  have habel := sum_mul_eq_sub_integral_mul₁ (f := fFn) cFn cFn_zero cFn_one
    (z : ℝ) (fFn_diff_on_Icc (z : ℝ)) (derivFFn_integrableOn (z : ℝ))
  rw [Nat.floor_natCast] at habel
  -- LHS of `habel`: `∑ k ∈ Icc 0 z, fFn k * cFn k = ∑ p prime, 1/p`.
  rw [lhs_eq_prime_recip_sum z] at habel
  -- RHS: rewrite `fFn z` and the integrand.
  -- First, `fFn z = 1 / log z`.
  have hfFn_z : fFn (z : ℝ) = 1 / Real.log (z : ℝ) := by
    unfold fFn; rw [one_div]
  -- And `∑ k ∈ Icc 0 z, cFn k = mertensFirstSum z`.
  have hsumCk : (∑ k ∈ Finset.Icc 0 z, cFn k) = mertensFirstSum (z : ℝ) :=
    sum_cFn_eq_mertensFirstSum_nat z
  rw [hsumCk, hfFn_z] at habel
  -- The integral term: rewrite using `deriv fFn t = -1/(t · log² t)` and
  -- `∑ k ∈ Icc 0 ⌊t⌋₊, cFn k = mertensFirstSum t`.
  have hInt :
      ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
          deriv fFn t * ∑ k ∈ Finset.Icc 0 (Nat.floor t), cFn k
        = - ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
              mertensFirstSum t / (t * (Real.log t)^2) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    simp only -- beta-reduce
    have h2t : (2 : ℝ) ≤ t := le_of_lt ht.1
    have htpos : (0 : ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := log_pos_of_two_le h2t
    have hlogne : Real.log t ≠ 0 := hlogpos.ne'
    have hsqne : Real.log t ^ 2 ≠ 0 := pow_ne_zero _ hlogne
    have htne : t ≠ 0 := htpos.ne'
    have hprod_ne : t * (Real.log t)^2 ≠ 0 := mul_ne_zero htne hsqne
    -- deriv fFn t = -(1/(t · log² t)) on Icc 2 z, in particular on Ioc.
    have hderiv : deriv fFn t = -(1 / (t * (Real.log t)^2)) :=
      (fFn_hasDerivAt h2t).deriv
    have hsumE : ∑ k ∈ Finset.Icc 0 (Nat.floor t), cFn k = mertensFirstSum t :=
      sum_cFn_eq_mertensFirstSum t
    rw [hderiv, hsumE]
    ring
  rw [hInt] at habel
  -- Now habel reads:
  --   ∑ 1/p = (1/log z) * M(z) - (-∫ M(t)/(t · log² t))
  --         = M(z)/log z + ∫ M(t)/(t · log² t).
  -- Goal: ∑ 1/p = M(z)/log z + ∫ M(t)/(t · log² t).
  rw [habel]
  ring

end PathCAbelPrimeRecipIdentity
end Gdbh
