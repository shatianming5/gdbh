/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T6 (Phase 19 / Path C — Mertens 2nd UPPER + paired-Brun lower gap)
-/
import Gdbh.PathC_MertensFirstUpper
import Gdbh.PathC_MertensSecondProof
import Gdbh.PathC_MertensThirdProof
import Gdbh.PathC_AbelInversion
import Gdbh.PathC_AbelIntegrandSplit
import Gdbh.PathC_AbelPrimeRecipIdentity
import Gdbh.PathC_LogRecipIntegral
import Gdbh.PathC_MertensErrorIntegral
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_PairedBrunMertensLowerProof
import Gdbh.PathC_PairedBrunMertensLowerReal

/-!
# Path C — Mertens 2nd UPPER bound and paired-Brun Mertens lower gap (P19-T6)

This file closes the **upper-bound** companion of the previously closed
lower-direction chain:

* `MertensFirstTheoremBound` (closed, two-sided)
  →  `MertensSecondLowerBoundFull` (closed, lower, via Abel inversion)
  →  `PairedBrunMertensThirdGap` (closed, upper)

The dual UPPER chain (new):

* `MertensFirstTheoremUpperBound` (closed by P19-T2)
  →  `MertensSecondUpperBound`     (closed here, **upper** direction)
  →  `PairedBrunMertensThirdLowerGap` (closed here, **lower** gap)

## Strategy — re-use the Abel inversion components

The four Abel-inversion sub-Props
(`AbelPrimeReciprocalIdentity`, `LogReciprocalIntegralAsymptotic`,
`MertensErrorIntegralBound`, `AbelIntegrandSplit`) are all closed
axiom-cleanly in the repo and are **two-sided** by construction:

* `AbelPrimeReciprocalIdentity` is an *equality* `Σ 1/p = Mz/log z + IntM`.
* `AbelIntegrandSplit` is an *equality* `IntM = IntLog + IntErr`.
* `LogReciprocalIntegralAsymptotic` is an *absolute-value* bound
  `|IntLog − log log z| ≤ C` ⇒ both directions.
* `MertensErrorIntegralBound` is an *absolute-value* bound
  `|IntErr| ≤ B'` ⇒ both directions.

Combined with the *upper* direction of Mertens 1st `Mz ≤ log z + B`
(which follows from the closed two-sided `MertensFirstTheoremBound`),
we get the upper direction of Mertens 2nd by linear arithmetic:

```
  Σ_{p ≤ z} 1/p  =  Mz/log z + IntLog + IntErr
                ≤  (1 + B/log 2)  +  (log log z + C)  +  B'
                =  log log z + (1 + B/log 2 + C + B') .
```

## Closing `PairedBrunMertensThirdLowerGap`

For prime `p ≥ 3`, mathlib's `Real.one_sub_inv_le_log_of_pos` gives

```
  log(1 − 2/p)  ≥  1 − 1/(1 − 2/p)  =  −2/(p − 2) .
```

We rewrite `1/(p − 2) = 1/p + 2/(p (p − 2))` and use `p (p − 2) ≥ p²/3`
(for `p ≥ 3`) to bound

```
  −2/(p − 2)  ≥  −2/p  −  12/p² .
```

Summing over primes `3 ≤ p ≤ z` and using

```
  ∑_{3 ≤ p ≤ z, prime} 1/p²  ≤  ∑_{n ≥ 3} 1/n²  ≤  1/2          (telescoping)
  ∑_{2 ≤ p ≤ z, prime} 1/p   ≤  log log z + B   (Mertens 2nd upper)
```

we obtain `log(pairedBrunFactor z) ≥ −2 log log z − 2B − 6`, whence
`pairedBrunFactor z ≥ exp(−2B − 6) / (log z)²`.  Setting
`C = exp(−2B − 6) > 0` matches `PairedBrunMertensThirdLowerGap`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCMertensSecondUpper

open Real Finset
open Gdbh.PathCMertensSecondProof
  (MertensFirstTheoremBound AbelInversionMertensSecondFromFirst)
open Gdbh.PathCMertensFirstUpper (MertensFirstTheoremUpperBound)
open Gdbh.PathCMertensThirdProof
  (log_pairedBrunFactor_eq_sum)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one
   one_sub_two_div_prime_pos)
open Gdbh.PathCAbelInversion
  (mertensFirstSum AbelPrimeReciprocalIdentity
   LogReciprocalIntegralAsymptotic
   MertensErrorIntegralBound AbelIntegrandSplit)
open Gdbh.PathCAbelPrimeRecipIdentity (abelPrimeReciprocalIdentity)
open Gdbh.PathCAbelIntegrandSplit (abelIntegrandSplit_holds)
open Gdbh.PathCLogRecipIntegral (logReciprocalIntegralAsymptotic_closed)
open Gdbh.PathCMertensErrorIntegral (mertensErrorIntegralBound_holds)
open Gdbh.PathCMertensFirstClosure (mertensFirstTheoremBound_holds)
open Gdbh.PathCPairedBrunMertensLowerReal (PairedBrunMertensThirdLowerGap)

/-! ## Section 1 — Named Prop: Mertens' 2nd theorem UPPER bound

The dual of `MertensSecondLowerBoundFull`, with the same indexing
`(Finset.Icc 2 z).filter Nat.Prime`. -/

/-- **Mertens' 2nd theorem UPPER bound.**

There exist constants `B : ℝ` and `z₀ : ℕ` such that for all `z ≥ z₀`,

```
∑_{2 ≤ p ≤ z, p prime} 1/p  ≤  log(log z) + B .
```

Classical content: `∑ 1/p = log log z + M + o(1)` (Mertens 1874).

The matching LOWER bound `MertensSecondLowerBoundFull` is closed via
`mertensSecondLowerBoundFull_of_abel_components` (Abel inversion).
Both bounds reuse the **same** four closed Abel-inversion sub-Props;
only the M1 direction differs. -/
def MertensSecondUpperBound : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (Real.log (z : ℝ)) + B

/-! ## Section 2 — Closure: the Abel-inversion upper arrow

The proof mirrors `abelInversionMertensSecondFromFirst_of_components`
in `PathC_AbelInversion.lean`, but extracts the **upper** direction of
the M1 absolute-value bound. -/

/-- **Closure of `MertensSecondUpperBound`** (P19-T6).

Reuses the closed Abel-inversion components:

* `abelPrimeReciprocalIdentity` (equality):
  `Σ_{2 ≤ p ≤ z} 1/p = mertensFirstSum z / log z + ∫_2^z M(t)/(t log²t) dt`.
* `abelIntegrandSplit_holds` (equality):
  `∫ M(t)/(t log²t) = ∫ 1/(t log t) + ∫ (M(t) − log t)/(t log²t)`.
* `logReciprocalIntegralAsymptotic_closed` (absolute-value bound).
* `mertensErrorIntegralBound_holds` (absolute-value bound, parameterised
  in the M1 constant).

Combined with the *upper* direction of `mertensFirstTheoremBound_holds`
(`Mz ≤ log z + B` follows from `|Mz − log z| ≤ B`) the upper bound
`Sum ≤ log log z + B''` follows by linear arithmetic. -/
theorem mertensSecondUpperBound_holds : MertensSecondUpperBound := by
  -- Extract M1 (two-sided absolute-value form).
  obtain ⟨B, z₀_M1, hM1bound⟩ := mertensFirstTheoremBound_holds
  -- B ≥ 0 since |·| ≥ 0.
  have hB_nonneg : 0 ≤ B := by
    have hz : z₀_M1 ≤ max z₀_M1 2 := le_max_left _ _
    exact le_trans (abs_nonneg _) (hM1bound (max z₀_M1 2) hz)
  -- Abel identity.
  obtain ⟨z₀_Id, hIdEq⟩ := abelPrimeReciprocalIdentity
  -- Log-reciprocal integral asymptotic.
  obtain ⟨C, z₀_Int, hIntBd⟩ := logReciprocalIntegralAsymptotic_closed
  -- Error-integral bound at the M1 constant B.
  obtain ⟨B', z₀_Err, hErrBound⟩ := mertensErrorIntegralBound_holds B hB_nonneg
  -- Final z₀: large enough for all four sub-Props + z ≥ 2.
  refine ⟨C + B' + B / Real.log 2 + 1,
    max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)), ?_⟩
  intro z hz
  -- Unpack nested max into individual lower bounds.
  have hz_M1 : z₀_M1 ≤ z := by
    have h1 : z₀_M1 ≤ max z₀_M1 z₀_Id := le_max_left _ _
    have h2 : max z₀_M1 z₀_Id ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Id : z₀_Id ≤ z := by
    have h1 : z₀_Id ≤ max z₀_M1 z₀_Id := le_max_right _ _
    have h2 : max z₀_M1 z₀_Id ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Int : z₀_Int ≤ z := by
    have h1 : z₀_Int ≤ max z₀_Int (max z₀_Err 2) := le_max_left _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_right _ _
    exact (h1.trans h2).trans hz
  have hz_Err : z₀_Err ≤ z := by
    have h0 : z₀_Err ≤ max z₀_Err 2 := le_max_left _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_right _ _
    exact ((h0.trans h1).trans h2).trans hz
  have hz_two : (2 : ℕ) ≤ z := by
    have h0 : (2 : ℕ) ≤ max z₀_Err 2 := le_max_right _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_right _ _
    exact ((h0.trans h1).trans h2).trans hz
  have hz_two_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_two
  -- Abbreviate the four quantities.
  set Sum := (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    with hSum_def
  set Mz := mertensFirstSum (z : ℝ) with hMz_def
  set IntM := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
                mertensFirstSum t / (t * (Real.log t)^2) with hIntM_def
  set IntLog := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ), 1 / (t * Real.log t)
    with hIntLog_def
  set IntErr := ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
                  (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)
    with hIntErr_def
  -- 1. Abel identity (equality).
  have hId : Sum = Mz / Real.log (z : ℝ) + IntM := hIdEq z hz_Id
  -- 2. Integrand split (equality).
  have hSplit_eq : IntM = IntLog + IntErr := by
    rw [hIntM_def, hIntLog_def, hIntErr_def]
    exact abelIntegrandSplit_holds (z : ℝ) hz_two_real
  -- 3. M1 absolute-value bound at z.
  have hMz_unfold : Mz =
      ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
    simp [hMz_def, mertensFirstSum, Nat.floor_natCast]
  have hM1_z : |Mz - Real.log (z : ℝ)| ≤ B := by
    rw [hMz_unfold]; exact hM1bound z hz_M1
  -- Linearize: Mz ≤ log z + B.
  have hMz_upper : Mz ≤ Real.log (z : ℝ) + B := by
    have hAbs := abs_le.mp hM1_z; linarith [hAbs.2]
  -- 4. IntLog ≤ log log z + C.
  have hIntLog_abs : |IntLog - Real.log (Real.log (z : ℝ))| ≤ C :=
    hIntBd z hz_Int
  have hIntLog_upper : IntLog ≤ Real.log (Real.log (z : ℝ)) + C := by
    have hAbs := abs_le.mp hIntLog_abs; linarith [hAbs.2]
  -- 5. IntErr ≤ B'.
  have hIntErr_abs : |IntErr| ≤ B' := hErrBound z hz_Err
  have hIntErr_upper : IntErr ≤ B' := by
    have hAbs := abs_le.mp hIntErr_abs; linarith [hAbs.2]
  -- 6. Boundary term: Mz/log z ≤ 1 + B/log 2.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz_pos : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hz_two_real
  have hlogz_ge : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) hz_two_real
  have hMz_over_logz : Mz / Real.log (z : ℝ) ≤ 1 + B / Real.log 2 := by
    -- Mz/log z ≤ (log z + B)/log z = 1 + B/log z ≤ 1 + B/log 2.
    have h_div : Mz / Real.log (z : ℝ)
                  ≤ (Real.log (z : ℝ) + B) / Real.log (z : ℝ) :=
      div_le_div_of_nonneg_right hMz_upper hlogz_pos.le
    have h_split : (Real.log (z : ℝ) + B) / Real.log (z : ℝ)
                    = 1 + B / Real.log (z : ℝ) := by
      field_simp
    have h_mono : B / Real.log (z : ℝ) ≤ B / Real.log 2 :=
      div_le_div_of_nonneg_left hB_nonneg hlog2_pos hlogz_ge
    linarith [h_div, h_split, h_mono]
  -- Combine: Sum = Mz/log z + IntM = Mz/log z + IntLog + IntErr
  --         ≤ (1 + B/log 2) + (log log z + C) + B'
  --         = log log z + (C + B' + B/log 2 + 1).
  rw [hSum_def] at hId
  linarith [hId, hSplit_eq, hMz_over_logz, hIntLog_upper, hIntErr_upper]

/-! ## Section 3 — Taylor lower bound for `log(1 − 2/p)`

For prime `p ≥ 3`, we obtain the Taylor lower bound

```
  log(1 − 2/p)  ≥  −2/p  −  12/p² .
```

The proof uses mathlib's `Real.one_sub_inv_le_log_of_pos`. -/

/-- For prime `p ≥ 3`, `log(1 − 2/p) ≥ −2/(p − 2)`.

This is the elementary half: applying `Real.one_sub_inv_le_log_of_pos`
at `x = 1 − 2/p` yields `1 − 1/(1 − 2/p) ≤ log(1 − 2/p)`, and
`1 − 1/(1 − 2/p) = 1 − p/(p − 2) = (p − 2 − p)/(p − 2) = −2/(p − 2)`. -/
theorem log_one_sub_two_div_prime_ge {p : ℕ} (hp : 3 ≤ p) :
    -(2 / ((p : ℝ) - 2)) ≤ Real.log (1 - 2 / (p : ℝ)) := by
  have hpos : (0 : ℝ) < 1 - 2 / (p : ℝ) := one_sub_two_div_prime_pos hp
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  -- one_sub_inv_le_log_of_pos: 1 − x⁻¹ ≤ log x.
  have h := Real.one_sub_inv_le_log_of_pos hpos
  -- h : 1 − (1 − 2/p)⁻¹ ≤ log(1 − 2/p).
  -- Simplify 1 − (1 − 2/p)⁻¹ = −2/(p − 2).
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_sub_ne : ((p : ℝ) - 2) ≠ 0 := ne_of_gt hp_sub_pos
  have h1msmp_ne : (1 - 2 / (p : ℝ)) ≠ 0 := ne_of_gt hpos
  have h_inv : (1 - 2 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 2) := by
    rw [inv_eq_one_div, div_eq_div_iff h1msmp_ne hp_sub_ne]
    field_simp
  rw [h_inv] at h
  -- h : 1 − p/(p−2) ≤ log(1 − 2/p).
  have h_simpl : (1 : ℝ) - (p : ℝ) / ((p : ℝ) - 2) = -(2 / ((p : ℝ) - 2)) := by
    field_simp
    ring
  linarith [h_simpl ▸ h]

/-- For prime `p ≥ 3`, `2/(p − 2) ≤ 2/p + 12/p²`.

Algebra: `2/(p − 2) − 2/p = 4/(p(p − 2))`, and `p(p − 2) ≥ p²/3` for
`p ≥ 3` (since `3(p − 2) ≥ p ↔ p ≥ 3`), so `4/(p(p − 2)) ≤ 12/p²`. -/
theorem two_div_p_sub_two_le {p : ℕ} (hp : 3 ≤ p) :
    (2 / ((p : ℝ) - 2)) ≤ 2 / (p : ℝ) + 12 / (p : ℝ)^2 := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hp_sq_pos : (0 : ℝ) < (p : ℝ)^2 := by positivity
  have hp_prod_pos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by positivity
  -- 2/(p−2) − 2/p = (2p − 2(p − 2)) / (p(p − 2)) = 4/(p(p − 2)).
  have h_diff : 2 / ((p : ℝ) - 2) - 2 / (p : ℝ)
                  = 4 / ((p : ℝ) * ((p : ℝ) - 2)) := by
    have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
    have hp_sub_ne : ((p : ℝ) - 2) ≠ 0 := ne_of_gt hp_sub_pos
    field_simp
    ring
  -- p(p − 2) ≥ p²/3:  3(p − 2) ≥ p  ↔  p ≥ 3.  So p²/3 ≤ p(p − 2).
  have h_prod_ge : (p : ℝ)^2 / 3 ≤ (p : ℝ) * ((p : ℝ) - 2) := by
    have h3sub : (p : ℝ) ≤ 3 * ((p : ℝ) - 2) := by linarith
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := le_of_lt hp_pos
    -- p² ≤ p · 3(p − 2) = 3 · p(p − 2).
    have : (p : ℝ)^2 ≤ 3 * ((p : ℝ) * ((p : ℝ) - 2)) := by
      have := mul_le_mul_of_nonneg_left h3sub hp_nn
      nlinarith [this]
    linarith
  -- 4/(p(p − 2)) ≤ 4/(p²/3) = 12/p².
  have h_div_le : 4 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 12 / (p : ℝ)^2 := by
    have hp_sq_div3_pos : (0 : ℝ) < (p : ℝ)^2 / 3 := by positivity
    have h1 : 4 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 4 / ((p : ℝ)^2 / 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) hp_sq_div3_pos h_prod_ge
    have h2 : 4 / ((p : ℝ)^2 / 3) = 12 / (p : ℝ)^2 := by
      rw [div_div_eq_mul_div]
      ring
    linarith [h1, h2]
  -- Chain: 2/(p−2) = 2/p + 4/(p(p−2)) ≤ 2/p + 12/p².
  linarith [h_diff, h_div_le]

/-- For prime `p ≥ 3`, `log(1 − 2/p) ≥ −2/p − 12/p²`. -/
theorem log_one_sub_two_div_prime_taylor_lower {p : ℕ} (hp : 3 ≤ p) :
    -(2 / (p : ℝ)) - 12 / (p : ℝ)^2 ≤ Real.log (1 - 2 / (p : ℝ)) := by
  have h_log := log_one_sub_two_div_prime_ge hp
  have h_div := two_div_p_sub_two_le hp
  -- log(1 − 2/p) ≥ −2/(p − 2) ≥ −(2/p + 12/p²) = −2/p − 12/p².
  have : -(2 / (p : ℝ) + 12 / (p : ℝ)^2) ≤ -(2 / ((p : ℝ) - 2)) := by linarith
  linarith [this, h_log]

/-! ## Section 4 — Telescoping bound on `Σ 1/p²` over primes ≥ 3

We bound `Σ_{3 ≤ p ≤ z, prime} 1/p² ≤ 1/2` by telescoping
`1/n² ≤ 1/(n(n−1)) = 1/(n−1) − 1/n` summed over all `n ≥ 3`. -/

/-- For natural `n ≥ 3`, `1/(n : ℝ)² ≤ 1/((n − 1 : ℝ) · (n : ℝ))`. -/
lemma one_div_sq_le_telescope {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / (n : ℝ)^2 ≤ 1 / (((n : ℝ) - 1) * (n : ℝ)) := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h_sq_pos : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have h_prod_pos : (0 : ℝ) < ((n : ℝ) - 1) * (n : ℝ) := by positivity
  -- (n − 1) · n ≤ n² ↔ n − 1 ≤ n, trivially true.
  have h_le : ((n : ℝ) - 1) * (n : ℝ) ≤ (n : ℝ)^2 := by
    have : ((n : ℝ) - 1) ≤ (n : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right this (le_of_lt hn_pos)
    nlinarith [this]
  apply div_le_div_of_nonneg_left (by norm_num) h_prod_pos h_le

/-- For natural `n ≥ 3`,
`1/((n − 1 : ℝ) · n) = 1/(n − 1) − 1/n` (algebraic identity). -/
lemma one_div_telescope {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / (((n : ℝ) - 1) * (n : ℝ))
      = 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_sub_ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn_sub_pos
  field_simp
  ring

/-- `Σ_{3 ≤ n ≤ z} 1/(n − 1) − 1/n  =  1/2 − 1/z` (telescoping). -/
lemma sum_telescope (z : ℕ) (hz : 3 ≤ z) :
    (∑ n ∈ Finset.Icc 3 z, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)))
      = 1 / 2 - 1 / (z : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base =>
      -- z = 3.  Icc 3 3 = {3}, and (1/2 − 1/3) = 1/2 − 1/3.
      rw [show Finset.Icc 3 3 = {3} from by
        ext; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega]
      rw [Finset.sum_singleton]
      norm_num
  | succ z hz ih =>
      -- z ≥ 3 → z + 1.
      rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ z + 1)]
      rw [ih]
      have hz_pos : (0 : ℝ) < (z : ℝ) := by
        have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
        linarith
      have hz_ne : (z : ℝ) ≠ 0 := ne_of_gt hz_pos
      have h_cast : (((z + 1 : ℕ) : ℝ) - 1) = (z : ℝ) := by push_cast; ring
      rw [h_cast]
      have h_cast2 : ((z + 1 : ℕ) : ℝ) = (z : ℝ) + 1 := by push_cast; ring
      rw [h_cast2]
      have hzp1_real_ne : (z : ℝ) + 1 ≠ 0 := by linarith
      field_simp
      ring

/-- **Telescoping bound**:
`Σ_{3 ≤ n ≤ z} 1/n²  ≤  1/2` for `z ≥ 3`. -/
lemma sum_one_div_sq_le_half (z : ℕ) (hz : 3 ≤ z) :
    (∑ n ∈ Finset.Icc 3 z, (1 : ℝ) / (n : ℝ)^2) ≤ 1 / 2 := by
  -- Termwise: 1/n² ≤ 1/((n − 1) · n) = 1/(n − 1) − 1/n.
  -- Sum: ≤ 1/2 − 1/z ≤ 1/2.
  have h_sum_le :
      (∑ n ∈ Finset.Icc 3 z, (1 : ℝ) / (n : ℝ)^2)
        ≤ ∑ n ∈ Finset.Icc 3 z, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn3, _⟩
    have h1 := one_div_sq_le_telescope hn3
    have h2 := one_div_telescope hn3
    linarith [h1, h2]
  have h_tele := sum_telescope z hz
  have h_z_pos : (0 : ℝ) < (z : ℝ) := by
    have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    linarith
  have h_one_div_z_nn : (0 : ℝ) ≤ 1 / (z : ℝ) := by positivity
  linarith [h_sum_le, h_tele]

/-- **Telescoping bound restricted to primes**:
`Σ_{3 ≤ p ≤ z, p prime} 1/p²  ≤  1/2` for `z ≥ 3`. -/
lemma sum_one_div_sq_prime_le_half (z : ℕ) (hz : 3 ≤ z) :
    (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
      ≤ 1 / 2 := by
  -- Drop the prime filter: filtered sum ≤ unfiltered sum (terms ≥ 0).
  have h_filter_le :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2)
        ≤ ∑ p ∈ Finset.Icc 3 z, (1 : ℝ) / (p : ℝ)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intros n _ _
      positivity
  exact le_trans h_filter_le (sum_one_div_sq_le_half z hz)

/-! ## Section 5 — Summed Taylor lower bound on `Σ log(1 − 2/p)`

Combining the per-prime Taylor lower bound with the telescoping
`Σ 1/p² ≤ 1/2` gives

```
  Σ_{3 ≤ p ≤ z, prime} log(1 − 2/p)
    ≥  −2 · (Σ_{3 ≤ p ≤ z, prime} 1/p)  −  6 .
``` -/

/-- **Summed Taylor lower bound on the paired Brun factor.**

For `z ≥ 3`,
`Σ_{3 ≤ p ≤ z, prime} log(1 − 2/p) ≥ −2·(Σ 1/p) − 6`. -/
theorem sum_log_pairedBrunFactor_ge (z : ℕ) (hz : 3 ≤ z) :
    -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) - 6
      ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ)) := by
  -- Termwise: log(1 − 2/p) ≥ −2/p − 12/p².
  -- Summing: Σ log ≥ −2·(Σ 1/p) − 12·(Σ 1/p²) ≥ −2·(Σ 1/p) − 6.
  have h_term_bd :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          (-(2 / (p : ℝ)) - 12 / (p : ℝ)^2))
        ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
            Real.log (1 - 2 / (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact log_one_sub_two_div_prime_taylor_lower hp3
  -- Rewrite LHS as −2 Σ 1/p − 12 Σ 1/p².
  have h_sum_split :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          (-(2 / (p : ℝ)) - 12 / (p : ℝ)^2))
        = -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            - 12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
    -- Split: Σ (-(2/p) - 12/p²) = Σ (-(2/p)) - Σ (12/p²)
    rw [Finset.sum_sub_distrib]
    -- Σ (-(2/p)) = -(Σ 2/p) = -(2 Σ 1/p):
    have h_neg :
        (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, -(2 / (p : ℝ)))
          = -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro p _
      ring
    -- Σ (12/p²) = 12 Σ 1/p²:
    have h_mul :
        (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (12 : ℝ) / (p : ℝ)^2)
          = 12 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro p _
      ring
    rw [h_neg, h_mul]
  -- Σ 1/p² over primes ≥ 3 ≤ 1/2; hence 12·(Σ 1/p²) ≤ 6.
  have h_p_sq_bd := sum_one_div_sq_prime_le_half z hz
  have h_12_le : (12 : ℝ) * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)^2
                  ≤ 6 := by
    have h := mul_le_mul_of_nonneg_left h_p_sq_bd (by norm_num : (0 : ℝ) ≤ 12)
    linarith [h]
  -- Combine.
  linarith [h_term_bd, h_sum_split, h_12_le]

/-! ## Section 6 — Mertens' 2nd upper, restricted to odd primes

For convenience, drop the `p = 2` term (`1/2`).  Since
`Σ_{p ≥ 3} 1/p = Σ_{p ≥ 2} 1/p − 1/2` (when `2 ≤ z`), the upper bound
shifts by `−1/2`, which only *improves* the upper bound. -/

/-- The full Mertens 2nd upper bound implies the restricted (odd-primes)
upper bound, with `B' = B − 1/2`.

```
Σ_{3 ≤ p ≤ z, prime} 1/p  =  Σ_{2 ≤ p ≤ z, prime} 1/p  −  1/2
                          ≤  log log z + B − 1/2 .
``` -/
theorem mertensSecondUpperBound_odd_of_full
    (h : MertensSecondUpperBound) :
    ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B := by
  obtain ⟨B, z₀, hbound⟩ := h
  refine ⟨B, max z₀ 2, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz2 : 2 ≤ z := le_trans (le_max_right _ _) hz
  -- Split the full sum: Σ_{2≤p≤z} = Σ_{3≤p≤z} + 1/2 (since 2 prime, 2 ∈ Icc 2 z).
  have hsplit :
      (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        = (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          + (1 : ℝ) / 2 := by
    have hIcc2 : Finset.Icc 2 z = insert 2 (Finset.Icc 3 z) := by
      ext n
      simp only [Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact Or.inl rfl
        · exact Or.inr ⟨h1', h2⟩
      · intro h
        rcases h with h | ⟨h1, h2⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, h2⟩
    have h2_not_mem : (2 : ℕ) ∉ Finset.Icc 3 z := by
      simp [Finset.mem_Icc]
    have hfilter_insert :
        (Finset.Icc 2 z).filter Nat.Prime
          = insert 2 ((Finset.Icc 3 z).filter Nat.Prime) := by
      rw [hIcc2]
      rw [Finset.filter_insert]
      simp [Nat.prime_two]
    have h2_not_in_filter :
        (2 : ℕ) ∉ (Finset.Icc 3 z).filter Nat.Prime := by
      intro hmem
      exact h2_not_mem (Finset.mem_filter.mp hmem).1
    rw [hfilter_insert, Finset.sum_insert h2_not_in_filter]
    have : (1 : ℝ) / ((2 : ℕ) : ℝ) = (1 : ℝ) / 2 := by norm_num
    linarith [this]
  -- Full ≤ log log z + B, so Σ_{3≤p≤z} = Full − 1/2 ≤ log log z + B − 1/2 ≤ log log z + B.
  have hfull := hbound z hz0
  linarith [hfull, hsplit]

/-! ## Section 7 — Closure: `PairedBrunMertensThirdLowerGap`

Combine the Taylor lower bound (Section 5) with the Mertens 2nd upper
bound restricted to odd primes (Section 6) and the log/sum identity
(`log_pairedBrunFactor_eq_sum`) to obtain

```
  log(pairedBrunFactor z)  ≥  −2·(log log z + B)  −  6
                          =  −2 log log z − 2B − 6 .
```

Exponentiating: `pairedBrunFactor z ≥ exp(−2B − 6) / (log z)²`. -/

/-- **Closure of `PairedBrunMertensThirdLowerGap`** (P19-T6).

Combines the Mertens 2nd UPPER bound (Section 2, closed via Abel
inversion) with the Taylor lower bound on `log(1 − 2/p)` (Section 5)
and the log/sum identity for the paired Brun factor.

The result: `pairedBrunFactor z ≥ exp(−2B − 6) / (log z)²` for `z`
large.  Setting `C = exp(−2B − 6) > 0` matches the signature of
`PairedBrunMertensThirdLowerGap`. -/
theorem pairedBrunMertensThirdLowerGap_holds : PairedBrunMertensThirdLowerGap := by
  -- Extract Mertens 2nd upper (odd primes form).
  obtain ⟨B, z₀, hsum_upper⟩ :=
    mertensSecondUpperBound_odd_of_full mertensSecondUpperBound_holds
  -- Exhibit C := exp(−2B − 6) and z₀' := max(z₀, 3).
  refine ⟨Real.exp (-(2 * B) - 6), max z₀ 3, Real.exp_pos _, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz3 : 3 ≤ z := le_trans (le_max_right _ _) hz
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  have hlogz_sq_pos : 0 < (Real.log (z : ℝ))^2 := by positivity
  -- Step (a): Mertens 2nd upper bound at z (odd-primes form).
  have hsum_upper_z :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ Real.log (Real.log (z : ℝ)) + B := hsum_upper z hz0
  -- Step (b): Taylor lower bound on Σ log(1 − 2/p).
  have hsum_log_lower := sum_log_pairedBrunFactor_ge z hz3
  -- Step (c): Combine — Σ log(1 − 2/p) ≥ −2 (log log z + B) − 6.
  have hcombined :
      -(2 * (Real.log (Real.log (z : ℝ)) + B)) - 6
        ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ)) := by
    have h_mul : 2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
                  ≤ 2 * (Real.log (Real.log (z : ℝ)) + B) := by
      have := mul_le_mul_of_nonneg_left hsum_upper_z (by norm_num : (0 : ℝ) ≤ 2)
      linarith [this]
    linarith [hsum_log_lower, h_mul]
  -- Step (d): rewrite as log(pairedBrunFactor z) ≥ −2 log log z − 2B − 6.
  have hlog_eq := log_pairedBrunFactor_eq_sum z
  have hlog_bd : -(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6
                  ≤ Real.log (pairedBrunFactor z) := by
    rw [hlog_eq]
    have : -(2 * (Real.log (Real.log (z : ℝ)) + B)) - 6
            = -(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6 := by ring
    linarith [hcombined, this]
  -- Step (e): exponentiate.
  have hmpos : 0 < pairedBrunFactor z := pairedBrunFactor_pos z
  have hexp_le :
      Real.exp (-(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6)
        ≤ pairedBrunFactor z := by
    have hexp_log : Real.exp (Real.log (pairedBrunFactor z)) = pairedBrunFactor z :=
      Real.exp_log hmpos
    have hmono : Real.exp (-(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6)
                  ≤ Real.exp (Real.log (pairedBrunFactor z)) :=
      Real.exp_le_exp.mpr hlog_bd
    rw [hexp_log] at hmono
    exact hmono
  -- Step (f): identify exp(−2 log log z − 2B − 6) = exp(−2B − 6) / (log z)².
  have h_exp_eq :
      Real.exp (-(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6)
        = Real.exp (-(2 * B) - 6) / (Real.log (z : ℝ))^2 := by
    -- exp(−2 log log z − 2B − 6) = exp(−2 log log z) · exp(−2B − 6)
    --                            = (1 / (log z)²) · exp(−2B − 6).
    have h_split :
        -(2 * Real.log (Real.log (z : ℝ))) - 2 * B - 6
          = -(2 * Real.log (Real.log (z : ℝ))) + (-(2 * B) - 6) := by ring
    rw [h_split, Real.exp_add]
    -- exp(−2 log log z) = 1 / (log z)².
    have h_neg : Real.exp (-(2 * Real.log (Real.log (z : ℝ))))
                  = 1 / (Real.log (z : ℝ))^2 := by
      rw [Real.exp_neg]
      have h2x : (2 : ℝ) * Real.log (Real.log (z : ℝ))
          = Real.log (Real.log (z : ℝ)) + Real.log (Real.log (z : ℝ)) := by ring
      rw [h2x, Real.exp_add, Real.exp_log hlogz_pos]
      ring
    rw [h_neg]
    field_simp
  rw [h_exp_eq] at hexp_le
  exact hexp_le

/-! ## Section 8 — Summary -/

/-- **P19-T6 summary marker** (no content theorem).

Deliverables (axiom-clean, only `Classical.choice, Quot.sound, propext`):

1. `MertensSecondUpperBound` — Prop: `Σ_{2 ≤ p ≤ z} 1/p ≤ log log z + B`.

2. `mertensSecondUpperBound_holds` — closure via re-using the four
   closed Abel-inversion sub-Props with the upper direction of M1.

3. `log_one_sub_two_div_prime_taylor_lower` — Taylor lower bound
   `log(1 − 2/p) ≥ −2/p − 12/p²` for prime `p ≥ 3` (via
   `Real.one_sub_inv_le_log_of_pos`).

4. `sum_one_div_sq_prime_le_half` — telescoping `Σ 1/p² ≤ 1/2`.

5. `sum_log_pairedBrunFactor_ge` — summed Taylor lower
   `Σ log(1 − 2/p) ≥ −2·(Σ 1/p) − 6`.

6. `pairedBrunMertensThirdLowerGap_holds` — closure of
   `PairedBrunMertensThirdLowerGap` via exponentiation.

This closes the residual Kernel B input of T2-real. -/
theorem pathC_p19_t6_summary : True := trivial

end PathCMertensSecondUpper
end Gdbh
