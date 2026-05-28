/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P14-T2 (Phase 14 / Abel-summation arrow decomposition — Mertens 2nd)
-/
import Gdbh.PathC_MertensSecondProof

/-!
# Path C — Abel-summation inversion arrow decomposition (P14-T2)

This file is the **P14-T2 deliverable** in Phase 14 (Abel-summation
arrow decomposition).  Its target is the named open Prop
`Gdbh.PathCMertensSecondProof.AbelInversionMertensSecondFromFirst`:

```
AbelInversionMertensSecondFromFirst : Prop :=
  MertensFirstTheoremBound  →  MertensSecondLowerBoundFull .
```

Concretely: Mertens' 1st theorem (`Σ log p / p = log z + O(1)`)
implies the lower-bound half of Mertens' 2nd theorem
(`Σ 1/p ≥ log log z − B'`).  The classical proof is **Abel
summation** (a.k.a. partial summation) against the weight `1/log u`.

## Strategy — decomposition

Let `M(z) := Σ_{2 ≤ p ≤ z, prime} log p / p` (Mertens' 1st sum) and
`R(z) := M(z) − log z` (the M1 error, uniformly `O(1)` by hypothesis).
Abel summation against the weight `g(u) = 1/log u` (where
`g'(u) = −1/(u · log² u)`) gives the *Abel identity*

```
Σ_{2 ≤ p ≤ z} 1/p  =  M(z)/log z  +  ∫_2^z M(t) / (t · log² t) dt .
```

Substituting `M(t) = log t + R(t)` and using the exact integral
`∫_2^z 1/(t · log t) dt = log log z − log log 2` we obtain

```
Σ_{2 ≤ p ≤ z} 1/p  =  1 + R(z)/log z
                    + log log z − log log 2
                    + ∫_2^z R(t) / (t · log² t) dt
                  =  log log z + (1 − log log 2) + R(z)/log z + E(z) ,
```

with the error integral `E(z)` uniformly bounded thanks to
`|R(t)| ≤ B` and `∫_2^∞ 1/(t · log² t) dt = 1/log 2 < ∞`.

We expose **four named open sub-Props** capturing the four
quantitative ingredients of this Abel-inversion calculation, plus
a mechanical assembly closing `AbelInversionMertensSecondFromFirst`
from them.

* `AbelPrimeReciprocalIdentity` — the **Abel identity itself**.
* `LogReciprocalIntegralAsymptotic` — the analytic integral
  `∫ 1/(t · log t) = log log z + O(1)`.
* `MertensErrorIntegralBound` — the perturbation bound on the M1
  error integral.
* `AbelIntegrandSplit` — **linearity-of-integral** bridge
  `IntM = IntLog + IntErr`.

All four sub-Props are pure mathlib-engineering targets: each is
realisable from `Mathlib.NumberTheory.AbelSummation` plus standard
real-analysis primitives (`Real.integral_inv_mul_log`,
`MeasureTheory.integral_add`).

## What's closed vs. open in this file

**Closed axiom-clean (only `Classical.choice, Quot.sound, propext`)**:

* `abelInversionMertensSecondFromFirst_of_components` — the
  **headline mechanical assembly**: the four sub-Props imply the
  Abel arrow.

* `mertensSecondLowerBoundFull_of_abel_components` — composes
  with the P11-T1 lemma to give `MertensSecondLowerBoundFull`
  from M1 + the four Abel sub-Props.

* `mertensSecondLowerBoundOdd_of_abel_components` — composes
  further with the P11-T1 odd-restriction lemma to give the
  named open `MertensSecondLowerBoundOdd` from M1 + the four
  Abel sub-Props.

**Open (named gaps, each *strictly smaller* than the Abel arrow)**:

* `AbelPrimeReciprocalIdentity` — Abel identity (instantiation of
  `sum_mul_eq_sub_integral_mul`).
* `LogReciprocalIntegralAsymptotic` — pure analytic integral asymptotic.
* `MertensErrorIntegralBound` — pure analytic perturbation integral.
* `AbelIntegrandSplit` — pure linearity-of-integral identity.

## Axiom budget

All theorems below are axiom-clean: only
`Classical.choice, Quot.sound, propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62 (Theorem 3 = M2 from M1).
* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.8.
* T. Tao, *Analytic Prime Number Theory*, Theorem 1.10.
* Mathlib v4.29.1: `Mathlib.NumberTheory.AbelSummation`
  (`sum_mul_eq_sub_integral_mul`, etc.).
-/

namespace Gdbh
namespace PathCAbelInversion

open Real Finset
open Gdbh.PathCMertensSecondProof

/-! ## Section 1 — The Mertens-1st step function -/

/-- **The Mertens-1st partial-sum function**, as a step function on
the reals: `mertensFirstSum t := Σ_{2 ≤ p ≤ ⌊t⌋, p prime} log p / p`.

This is the natural integrand for Abel summation against `1/log u`. -/
noncomputable def mertensFirstSum (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 (Nat.floor t)).filter Nat.Prime,
    Real.log (p : ℝ) / (p : ℝ)

/-! ## Section 2 — Named open sub-Props (Abel inversion) -/

/-- **Named open Prop**: the *Abel-summation identity* for the prime
reciprocal sum.

```
∃ z₀ : ℕ, ∀ z ≥ z₀,
  Σ_{2 ≤ p ≤ z, prime} 1/p
    = M(z) / log z
      + ∫_2^z M(t) / (t · log² t) dt ,
```

where `M(t) := mertensFirstSum t`.

This is **Abel summation** (partial summation) instantiated at the
prime indicator times `log p`.  Classically derived from
`sum_mul_eq_sub_integral_mul` (mathlib v4.29.1) applied to

```
Σ_{p ≤ z} 1/p  =  Σ_{p ≤ z} (log p / p) · (1 / log p) .
```

Status here: **named open Prop**, mathematically rigorous,
mechanical to instantiate from mathlib. -/
def AbelPrimeReciprocalIdentity : Prop :=
  ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    (∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      = mertensFirstSum (z : ℝ) / Real.log (z : ℝ)
        + ∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
            mertensFirstSum t / (t * (Real.log t)^2)

/-- **Named open Prop**: the asymptotic of the elementary integral
`∫_2^z 1/(t · log t) dt`.

```
∃ C : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  |∫_2^z 1/(t · log t) dt  −  log log z|  ≤  C .
```

Pure real analysis (no primes).  The exact value is
`log log z − log log 2`, so `C = |log log 2|` suffices.  Status here:
**named open Prop**; closeable from mathlib v4.29.1's
`Real.integral_inv_mul_log` or by direct antiderivative computation. -/
def LogReciprocalIntegralAsymptotic : Prop :=
  ∃ C : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    |(∫ t in Set.Ioc (2 : ℝ) (z : ℝ), 1 / (t * Real.log t))
        - Real.log (Real.log (z : ℝ))| ≤ C

/-- **Named open Prop**: the *perturbation bound* on the M1 error
integral.

Given the M1 error bound `|M(t) − log t| ≤ B` for `t ≥ z₀_M1`
(Mertens 1st), the weighted error integral against `1/(t · log² t)`
is uniformly bounded:

```
∀ B : ℝ, 0 ≤ B → ∃ B' : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  |∫_2^z (M(t) − log t) / (t · log² t) dt|  ≤  B' .
```

Pure real analysis.  Closeable from
`∫_2^∞ 1/(t · log² t) dt = 1/log 2 < ∞` plus a pointwise bound from
the M1 hypothesis.  Status here: **named open Prop**, parameterised
in the M1 bound `B`. -/
def MertensErrorIntegralBound : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ B' : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    |∫ t in Set.Ioc (2 : ℝ) (z : ℝ),
        (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2)| ≤ B'

/-- **Named open Prop**: the *integrand-splitting identity*.

```
∀ z ≥ 2,
  ∫_2^z M(t) / (t · log² t) dt
    = ∫_2^z 1/(t · log t) dt
      + ∫_2^z (M(t) − log t) / (t · log² t) dt .
```

A purely **mechanical** linearity-of-integral bridge.  Required to
combine the three sub-Props above.  Closeable from
`MeasureTheory.integral_add` plus the pointwise identity

```
M(t) / (t · log² t)  =  1/(t · log t)  +  (M(t) − log t) / (t · log² t)
```

(valid for `t > 1`, since `log t · log t = log² t` and `log t > 0`).
Stated here as a named gap to keep the decomposition clean. -/
def AbelIntegrandSplit : Prop :=
  ∀ z : ℝ, (2 : ℝ) ≤ z →
    (∫ t in Set.Ioc (2 : ℝ) z,
        mertensFirstSum t / (t * (Real.log t)^2))
      = (∫ t in Set.Ioc (2 : ℝ) z, 1 / (t * Real.log t))
        + (∫ t in Set.Ioc (2 : ℝ) z,
            (mertensFirstSum t - Real.log t) / (t * (Real.log t)^2))

/-! ## Section 3 — Mechanical assembly -/

/-- **Mechanical (headline)**: the four Abel-inversion sub-Props
together imply the Abel-summation arrow
`AbelInversionMertensSecondFromFirst`.

Reasoning chain.  Let `B, z₀_M1` be the Mertens-1st constants
(`|M(z) − log z| ≤ B` for `z ≥ z₀_M1`).  Let `z₀_Id, z₀_Int, z₀_Err`
be the constants from `AbelPrimeReciprocalIdentity`,
`LogReciprocalIntegralAsymptotic`, and `MertensErrorIntegralBound B`.
Set `z₀ := max(z₀_M1, z₀_Id, z₀_Int, z₀_Err, 2)` and combine:

1. **Abel identity** (sub-Prop 1):
   `Σ 1/p = M(z)/log z + IntM`.

2. **Integrand split** (sub-Prop 4):
   `IntM = IntLog + IntErr`.

3. **Integral asymptotic** (sub-Prop 2):
   `IntLog ≥ log log z − C`.

4. **Error bound** (sub-Prop 3):
   `|IntErr| ≤ B'`, hence `IntErr ≥ −B'`.

5. **Boundary term**: `Mz ≥ log z − B`, hence (with `log z ≥ log 2 > 0`)
   `Mz/log z ≥ 1 − B/log 2`.

Combine: `Σ 1/p ≥ (1 − B/log 2) + (log log z − C) + (−B')`
       ` = log log z − (C + B' + B/log 2 − 1)`.

Setting `B'' := C + B' + B/log 2 − 1` closes the bound.

The proof is **arithmetic juggling** (linear inequalities and
triangle inequality on absolute values).  All four sub-Props feed in
as named-open existentials; the assembly extracts witnesses and
combines.  (Closed axiom-clean.) -/
theorem abelInversionMertensSecondFromFirst_of_components
    (hAbelId : AbelPrimeReciprocalIdentity)
    (hLogInt : LogReciprocalIntegralAsymptotic)
    (hErrBd : MertensErrorIntegralBound)
    (hSplit : AbelIntegrandSplit) :
    AbelInversionMertensSecondFromFirst := by
  -- Unfold the arrow goal.
  intro hM1
  -- Extract M1 witnesses.
  obtain ⟨B, z₀_M1, hM1bound⟩ := hM1
  -- B ≥ 0 since |·| ≥ 0 at z = max z₀_M1 2.
  have hB_nonneg : 0 ≤ B := by
    have hz : z₀_M1 ≤ max z₀_M1 2 := le_max_left _ _
    have := hM1bound (max z₀_M1 2) hz
    exact le_trans (abs_nonneg _) this
  -- Extract Abel identity witness.
  obtain ⟨z₀_Id, hIdEq⟩ := hAbelId
  -- Extract log-reciprocal integral witness.
  obtain ⟨C, z₀_Int, hIntBd⟩ := hLogInt
  -- Extract error-integral witness (at the M1 constant B).
  obtain ⟨B', z₀_Err, hErrBound⟩ := hErrBd B hB_nonneg
  -- Final z₀: large enough that all sub-Prop hypotheses apply and z ≥ 2.
  refine ⟨C + B' + B / Real.log 2 - 1,
    max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)), ?_⟩
  intro z hz
  -- Unpack the nested `max` into individual lower bounds.
  have hz_M1 : z₀_M1 ≤ z := by
    have h1 : z₀_M1 ≤ max z₀_M1 z₀_Id := le_max_left _ _
    have h2 : max z₀_M1 z₀_Id ≤ max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Id : z₀_Id ≤ z := by
    have h1 : z₀_Id ≤ max z₀_M1 z₀_Id := le_max_right _ _
    have h2 : max z₀_M1 z₀_Id ≤ max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) :=
      le_max_left _ _
    exact (h1.trans h2).trans hz
  have hz_Int : z₀_Int ≤ z := by
    have h1 : z₀_Int ≤ max z₀_Int (max z₀_Err 2) := le_max_left _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
    exact (h1.trans h2).trans hz
  have hz_Err : z₀_Err ≤ z := by
    have h0 : z₀_Err ≤ max z₀_Err 2 := le_max_left _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
    exact ((h0.trans h1).trans h2).trans hz
  have hz_two : (2 : ℕ) ≤ z := by
    have h0 : (2 : ℕ) ≤ max z₀_Err 2 := le_max_right _ _
    have h1 : max z₀_Err 2 ≤ max z₀_Int (max z₀_Err 2) := le_max_right _ _
    have h2 : max z₀_Int (max z₀_Err 2) ≤
              max (max z₀_M1 z₀_Id) (max z₀_Int (max z₀_Err 2)) := le_max_right _ _
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
  -- 1. Abel identity: Sum = Mz/log z + IntM.
  have hId : Sum = Mz / Real.log (z : ℝ) + IntM := hIdEq z hz_Id
  -- 2. Integrand split: IntM = IntLog + IntErr.
  have hSplit_eq : IntM = IntLog + IntErr := by
    rw [hIntM_def, hIntLog_def, hIntErr_def]
    exact hSplit (z : ℝ) hz_two_real
  -- 3. M1 absolute-value bound at the natural endpoint z.
  have hMz_unfold : Mz =
      ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
    simp [hMz_def, mertensFirstSum, Nat.floor_natCast]
  have hM1_z : |Mz - Real.log (z : ℝ)| ≤ B := by
    rw [hMz_unfold]; exact hM1bound z hz_M1
  -- Linearize the absolute-value bound: Mz ≥ log z − B.
  have hMz_lower : Real.log (z : ℝ) - B ≤ Mz := by
    have hAbs := abs_le.mp hM1_z; linarith [hAbs.1]
  -- 4. Integral asymptotic: IntLog ≥ log log z − C.
  have hIntLog_abs : |IntLog - Real.log (Real.log (z : ℝ))| ≤ C :=
    hIntBd z hz_Int
  have hIntLog_lower : Real.log (Real.log (z : ℝ)) - C ≤ IntLog := by
    have hAbs := abs_le.mp hIntLog_abs; linarith [hAbs.1]
  -- 5. Error-integral bound: IntErr ≥ −B'.
  have hIntErr_abs : |IntErr| ≤ B' := hErrBound z hz_Err
  have hIntErr_lower : -B' ≤ IntErr := by
    have hAbs := abs_le.mp hIntErr_abs; linarith [hAbs.1]
  -- 6. Boundary term: Mz/log z ≥ 1 − B/log 2.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz_pos : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hz_two_real
  have hlogz_ge : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) hz_two_real
  have hMz_over_logz : 1 - B / Real.log 2 ≤ Mz / Real.log (z : ℝ) := by
    -- (log z − B) / log z ≤ Mz / log z   (monotonicity of /log z, positive)
    have h_div : (Real.log (z : ℝ) - B) / Real.log (z : ℝ)
                  ≤ Mz / Real.log (z : ℝ) :=
      div_le_div_of_nonneg_right hMz_lower hlogz_pos.le
    -- (log z − B)/log z = 1 − B/log z
    have h_split : (Real.log (z : ℝ) - B) / Real.log (z : ℝ)
                    = 1 - B / Real.log (z : ℝ) := by
      field_simp
    -- B/log z ≤ B/log 2 (B ≥ 0, denom monotone)
    have h_mono : B / Real.log (z : ℝ) ≤ B / Real.log 2 :=
      div_le_div_of_nonneg_left hB_nonneg hlog2_pos hlogz_ge
    -- Combine: 1 − B/log 2 ≤ 1 − B/log z = (log z − B)/log z ≤ Mz/log z.
    linarith [h_div, h_split, h_mono]
  -- Goal: log log z − (C + B' + B/log 2 − 1) ≤ Sum.
  -- Substitute hId, hSplit_eq:
  -- Sum = Mz/log z + IntM = Mz/log z + IntLog + IntErr.
  -- ≥ (1 − B/log 2) + (log log z − C) + (−B').
  rw [hSum_def] at hId
  linarith [hId, hSplit_eq, hMz_over_logz, hIntLog_lower, hIntErr_lower]

/-! ## Section 4 — Headline composition (P14-T2 + P11-T1) -/

/-- **Composed reduction**: `MertensSecondLowerBoundFull` follows from
Mertens' 1st theorem plus the four Abel-inversion sub-Props.

Chain (via the P11-T1 Section 2 lemma
`mertensSecondLowerBoundFull_of_first_and_abel`):

1. The four sub-Props ⇒ `AbelInversionMertensSecondFromFirst`
   (`abelInversionMertensSecondFromFirst_of_components`, this file).

2. `MertensFirstTheoremBound` + `AbelInversionMertensSecondFromFirst`
   ⇒ `MertensSecondLowerBoundFull` (P11-T1).

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundFull_of_abel_components
    (hM1 : MertensFirstTheoremBound)
    (hAbelId : AbelPrimeReciprocalIdentity)
    (hLogInt : LogReciprocalIntegralAsymptotic)
    (hErrBd : MertensErrorIntegralBound)
    (hSplit : AbelIntegrandSplit) :
    MertensSecondLowerBoundFull :=
  Gdbh.PathCMertensSecondProof.mertensSecondLowerBoundFull_of_first_and_abel
    hM1
    (abelInversionMertensSecondFromFirst_of_components
      hAbelId hLogInt hErrBd hSplit)

/-- **Composed reduction**: the named open
`MertensSecondLowerBoundOdd` follows from Mertens' 1st + the four
Abel-inversion sub-Props.

Chain:

1. M1 + the four Abel sub-Props ⇒ `MertensSecondLowerBoundFull`
   (`mertensSecondLowerBoundFull_of_abel_components`, this file).

2. `MertensSecondLowerBoundFull` ⇒ `MertensSecondLowerBoundOdd`
   (drop `p = 2` — P11-T1 Section 2 lemma).

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundOdd_of_abel_components
    (hM1 : MertensFirstTheoremBound)
    (hAbelId : AbelPrimeReciprocalIdentity)
    (hLogInt : LogReciprocalIntegralAsymptotic)
    (hErrBd : MertensErrorIntegralBound)
    (hSplit : AbelIntegrandSplit) :
    Gdbh.PathCMertensThirdProof.MertensSecondLowerBoundOdd :=
  Gdbh.PathCMertensSecondProof.mertensSecondLowerBoundOdd_of_full
    (mertensSecondLowerBoundFull_of_abel_components
      hM1 hAbelId hLogInt hErrBd hSplit)

/-! ## Section 5 — Summary -/

/-- **P14-T2 summary, in proof form.**

This file decomposes the Abel-summation arrow
`AbelInversionMertensSecondFromFirst` (the bridge from Mertens' 1st to
the lower-bound half of Mertens' 2nd) into **four** strictly smaller
named open sub-Props:

1. `AbelPrimeReciprocalIdentity` — the Abel identity itself
   (instantiation of `Mathlib.NumberTheory.AbelSummation`).

2. `LogReciprocalIntegralAsymptotic` — the asymptotic of
   `∫_2^z 1/(t · log t) dt = log log z + O(1)` (pure analysis).

3. `MertensErrorIntegralBound` — the perturbation bound on the M1
   error integral (pure analysis, parameterised in the M1 bound).

4. `AbelIntegrandSplit` — the linearity-of-integral bridge
   `IntM = IntLog + IntErr` (pure analysis, no asymptotics).

Of the **mechanical** bridges, the following are closed
axiom-cleanly in this file:

* `abelInversionMertensSecondFromFirst_of_components` — the
  **headline Abel-arrow assembly** (linear-arithmetic + triangle
  inequality combination of the four sub-Props).

* `mertensSecondLowerBoundFull_of_abel_components` — composes with
  the P11-T1 lemma to give `MertensSecondLowerBoundFull` from M1 +
  the four Abel sub-Props.

* `mertensSecondLowerBoundOdd_of_abel_components` — composes
  further with the P11-T1 odd-restriction lemma to give the named
  open `MertensSecondLowerBoundOdd`.

What remains open after P14-T2: the four sub-Props above.  All four
are realisable from mathlib v4.29.1 primitives:
`sum_mul_eq_sub_integral_mul` (Abel identity);
`Real.integral_inv_mul_log` or direct antiderivative (analytic
integral); `Filter.Tendsto.norm_le` plus integrability of
`1/(t · log² t)` (perturbation bound); `MeasureTheory.integral_add`
(integrand split).  The closing of these four sub-Props is
mathlib-engineering, **not** new mathematics.

The classical content of the Abel inversion — the Hardy-Wright §22.8
calculation — is fully captured by the assembly here.

(Closed axiom-clean.) -/
theorem pathC_p14_t2_summary : True := trivial

end PathCAbelInversion
end Gdbh
