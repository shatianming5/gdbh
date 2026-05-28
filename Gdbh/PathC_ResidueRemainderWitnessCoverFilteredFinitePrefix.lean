/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredEnvelopeApplications
import Gdbh.PathC_BrunErrorDecayProof
import Mathlib.Tactic.Ring

/-!
# Path C -- finite-prefix log-squared absorption for filtered witness covers

Round 85 turns the Round84 finite-prefix linear envelope into a
log-squared envelope on each bounded square-root prefix.  The price is the
finite loss `(log ((N + 1)^2))^2`, coming from
`n < (N + 1)^2` whenever `Nat.sqrt n ≤ N`.

This is deliberately a finite-prefix bridge.  It does not assert any global
or eventual log-squared improvement.
-/

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredFinitePrefix

open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelopeApplications
  (ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt
   residueFilteredCoverSqrtAtMostEnvelope
   residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit)

/-! ## Finite-prefix log-loss -/

/-- The log-loss needed to absorb a linear `n` bound into
`n / (log n)^2` on the finite prefix `Nat.sqrt n ≤ N`. -/
noncomputable def residueFilteredCoverFinitePrefixLogLoss (N : ℕ) : ℝ :=
  (Real.log (((N + 1) * (N + 1) : ℕ) : ℝ))^2

/-- If `Nat.sqrt n ≤ N`, then `n < (N + 1)^2`. -/
theorem nat_lt_succ_sq_of_sqrt_le {n N : ℕ} (hsqrt_le_N : Nat.sqrt n ≤ N) :
    n < (N + 1) * (N + 1) := by
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) :=
    Nat.lt_succ_sqrt n
  have hle :
      (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (N + 1) * (N + 1) := by
    exact Nat.mul_le_mul
      (Nat.succ_le_succ hsqrt_le_N)
      (Nat.succ_le_succ hsqrt_le_N)
  exact lt_of_lt_of_le hlt hle

/-- On a fixed square-root prefix, `(log n)^2` is bounded by the
finite-prefix log-loss. -/
theorem log_nat_sq_le_finitePrefixLogLoss {n N : ℕ}
    (hn : 16 ≤ n) (hsqrt_le_N : Nat.sqrt n ≤ N) :
    (Real.log (n : ℝ))^2 ≤ residueFilteredCoverFinitePrefixLogLoss N := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_lt_upper_nat : n < (N + 1) * (N + 1) :=
    nat_lt_succ_sq_of_sqrt_le hsqrt_le_N
  have hn_le_upper :
      (n : ℝ) ≤ (((N + 1) * (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast (le_of_lt hn_lt_upper_nat)
  have hlog_le :
      Real.log (n : ℝ) ≤ Real.log (((N + 1) * (N + 1) : ℕ) : ℝ) :=
    Real.log_le_log hn_pos hn_le_upper
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact le_of_lt
      (Gdbh.PathCBrunErrorDecayProof.log_natCast_pos (by omega : 3 ≤ n))
  have hsq :=
    pow_le_pow_left₀ hlogn_nonneg hlog_le 2
  simpa [residueFilteredCoverFinitePrefixLogLoss] using hsq

/-! ## Linear finite-prefix worker to log-squared finite-prefix worker -/

/-- Fixed-coefficient finite-prefix worker after log-squared absorption. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt
    (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n ≤ N →
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Existential coefficient form of the log-squared finite-prefix worker. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixWithConstant
    (N : ℕ) : Prop :=
  ∃ A : ℝ,
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt N A

/-- Any linear filtered-cover finite-prefix worker yields a log-squared
finite-prefix worker after multiplying by the explicit finite log-loss. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_of_linear
    {N : ℕ} {A : ℝ}
    (hLinear : ResidueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt N A) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt N
      (A * residueFilteredCoverFinitePrefixLogLoss N) := by
  rcases hLinear with ⟨hA_nonneg, hLinear_bound⟩
  refine ⟨?_, ?_⟩
  · unfold residueFilteredCoverFinitePrefixLogLoss
    positivity
  · intro n hn hsqrt_le_N
    have hlin :=
      hLinear_bound n hn hsqrt_le_N
    have hlog_sq_le_loss :
        (Real.log (n : ℝ))^2 ≤ residueFilteredCoverFinitePrefixLogLoss N :=
      log_nat_sq_le_finitePrefixLogLoss hn hsqrt_le_N
    have hlog_sq_pos :
        0 < (Real.log (n : ℝ))^2 :=
      Gdbh.PathCBrunErrorDecayProof.log_natCast_sq_pos (by omega : 3 ≤ n)
    have hAn_nonneg : 0 ≤ A * (n : ℝ) :=
      mul_nonneg hA_nonneg (by positivity)
    have hmul :
        (A * (n : ℝ)) * (Real.log (n : ℝ))^2 ≤
          (A * (n : ℝ)) * residueFilteredCoverFinitePrefixLogLoss N :=
      mul_le_mul_of_nonneg_left hlog_sq_le_loss hAn_nonneg
    have htarget :
        (A * (n : ℝ)) * (Real.log (n : ℝ))^2 ≤
          (A * residueFilteredCoverFinitePrefixLogLoss N) * (n : ℝ) := by
      calc
        (A * (n : ℝ)) * (Real.log (n : ℝ))^2
            ≤ (A * (n : ℝ)) * residueFilteredCoverFinitePrefixLogLoss N := hmul
        _ = (A * residueFilteredCoverFinitePrefixLogLoss N) * (n : ℝ) := by
              ring
    have hscale :
        A * (n : ℝ) ≤
          (A * residueFilteredCoverFinitePrefixLogLoss N) * (n : ℝ) /
            (Real.log (n : ℝ))^2 := by
      exact (le_div_iff₀ hlog_sq_pos).mpr htarget
    exact hlin.trans hscale

/-- Explicit log-squared finite-prefix filtered-cover envelope. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt N
      (residueFilteredCoverSqrtAtMostEnvelope N *
        residueFilteredCoverFinitePrefixLogLoss N) :=
  residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_of_linear
    (residueSharedPrimeWitnessFilteredCoverLinearFinitePrefixAtSqrt_explicit N)

/-- Existential explicit log-squared finite-prefix filtered-cover envelope. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixWithConstant_explicit
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixWithConstant N :=
  ⟨residueFilteredCoverSqrtAtMostEnvelope N *
      residueFilteredCoverFinitePrefixLogLoss N,
    residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit N⟩

/-- Specialization of the log-squared filtered-cover finite-prefix envelope
to the existing `Nat.sqrt n ≤ 10000` boundary. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_ten_thousand :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt 10000
      (residueFilteredCoverSqrtAtMostEnvelope 10000 *
        residueFilteredCoverFinitePrefixLogLoss 10000) :=
  residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit 10000

end PathCResidueRemainderWitnessCoverFilteredFinitePrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredFinitePrefix.nat_lt_succ_sq_of_sqrt_le
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredFinitePrefix.log_nat_sq_le_finitePrefixLogLoss
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredFinitePrefix.residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_of_linear
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredFinitePrefix.residueSharedPrimeWitnessFilteredCoverLogSquaredFinitePrefixAtSqrt_explicit
