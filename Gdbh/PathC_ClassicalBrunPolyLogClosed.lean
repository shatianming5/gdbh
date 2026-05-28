/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T10 (Phase 22 / Path C — Closed-form bridge for
        `ClassicalBrunGoldbachPolyLogN`:  T5's closed
        `S(n) ≤ K · log n` bound (for the Goldbach singular-series
        multiplier) wired through T2's parametric Bridge B, so that
        the residual `ClassicalBrunGoldbachPolyLogN` reduces to JUST
        `BrunGoldbachWithSingularSeries`.)
-/
import Gdbh.PathC_BrunGoldbachSingularSeries
import Gdbh.PathC_SingularSeriesLogNBound

/-!
# Path C — P22-T10: `ClassicalBrunGoldbachPolyLogN` closed form

## Mission

After P22-T5, the closed Mertens-style bound

```
∃ K > 0, ∃ N₀, ∀ n ≥ N₀,
  goldbachSingularSeriesLocalMultiplier n  ≤  K · log n
```

is available axiom-clean (`Gdbh.PathCSingularSeriesLogNBound.
singularSeries_log_n_bound_holds`).  P22-T2 defines the named Prop
`BrunGoldbachWithSingularSeries` (the Halberstam-Richert §3.11 master
inequality) together with the parametric "Bridge B":

```
BrunGoldbachWithSingularSeries  +  SingularSeriesPolyLogBound
   ⇒ ClassicalBrunGoldbachPolyLogN .
```

This file **wires T5 + T2** by closing `SingularSeriesPolyLogBound`
axiom-clean from T5, so that the residual
`ClassicalBrunGoldbachPolyLogN` reduces to **JUST**
`BrunGoldbachWithSingularSeries`.

## Strategy

1. **Identify the two singular-series shapes.**  T5 bounds
   `goldbachSingularSeriesLocalMultiplier n`
   (`= ∏_{p ∈ n.divisors, p prime, p > 2} (p - 1)/(p - 2)`).
   T2 uses
   `singularSeries n`
   (`= ∏_{p ∈ Finset.Icc 3 n, p prime, p ∣ n} (p - 1)/(p - 2)`).
   These are *equal* for every `n` (Section 1 below) — the two filter
   conditions select the same primes.

2. **From log n to (log n)².**  Multiply by `log n ≥ 1` (valid for
   `n ≥ 3`) to upgrade `K · log n` to `K · (log n)²` (Section 2 / 3).

3. **Apply Bridge B.**  Feed the closed `SingularSeriesPolyLogBound`
   into T2's `classicalBrunGoldbachPolyLogN_of_brunGoldbachWithSingularSeries`
   to obtain the closed-form bridge
   `ClassicalBrunGoldbachPolyLogN_of_brunSingularSeries` (Section 4).

## Residual mathlib gap (after this file)

After this file, the residual `ClassicalBrunGoldbachPolyLogN` reduces
to **exactly one** named open Prop:

```
BrunGoldbachWithSingularSeries   -- Halberstam-Richert §3.11 master
```

The previous `SingularSeriesPolyLogBound` open gap is **eliminated**
by T5's closed `S(n) ≤ K · log n` bound.

## Strict constraints (P22-T10 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Every theorem below is axiom-clean:  only `Classical.choice`,
  `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCClassicalBrunPolyLogClosed

open Real Finset
open Gdbh
  (goldbachOddPrimeLocalFactor goldbachSingularSeriesLocalPrimes
   goldbachSingularSeriesLocalMultiplier)
open Gdbh.PathCHardyLittlewoodForm
  (singularSeries singularSeries_def)
open Gdbh.PathCBrunGoldbachSingularSeries
  (BrunGoldbachWithSingularSeries
   ClassicalBrunGoldbachPolyLogN
   SingularSeriesPolyLogBound
   classicalBrunGoldbachPolyLogN_of_brunGoldbachWithSingularSeries)
open Gdbh.PathCSingularSeriesLogNBound
  (SingularSeriesLogNBound singularSeries_log_n_bound_holds)

/-! ## Section 1 — `singularSeries n = goldbachSingularSeriesLocalMultiplier n`

The two singular-series definitions in the project filter the *same*
underlying set of odd prime divisors of `n` from two superficially
different ambient sets:

* `goldbachSingularSeriesLocalMultiplier n` filters
  `n.divisors` with `(Nat.Prime p ∧ 2 < p)`.
* `singularSeries n` filters
  `Finset.Icc 3 n` with `(Nat.Prime p ∧ p ∣ n)`.

We prove these are literally equal for every `n` (including the trivial
`n = 0` case where both sets are empty). -/

/-- The two filter sets coincide for every `n`:

```
n.divisors.filter (fun p => Nat.Prime p ∧ 2 < p)
  = (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n) .
```

For `n = 0`, both sides are `∅`; for `n ≥ 1`, the bidirectional
membership follows from `Nat.mem_divisors`, `Nat.divisor_le`, and the
elementary equivalence `(Nat.Prime p ∧ 2 < p) ↔ (3 ≤ p ∧ Nat.Prime p)`. -/
lemma goldbachSingularSeriesLocalPrimes_eq_singularSeriesFilter (n : ℕ) :
    n.divisors.filter (fun p => Nat.Prime p ∧ 2 < p)
      = (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n) := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hp_dvd, hn_ne⟩, hp_prime, hp_gt2⟩
    have hp_le_n : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn_ne) hp_dvd
    refine ⟨⟨by omega, hp_le_n⟩, hp_prime, hp_dvd⟩
  · rintro ⟨⟨hp_ge_3, hp_le_n⟩, hp_prime, hp_dvd⟩
    have hp_pos : 0 < p := by omega
    have hn_pos : 0 < n := lt_of_lt_of_le hp_pos hp_le_n
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
    refine ⟨⟨hp_dvd, hn_ne⟩, hp_prime, by omega⟩

/-- The Hardy-Littlewood `singularSeries n` and the
`goldbachSingularSeriesLocalMultiplier n` agree pointwise.  Both are
the product of `(p - 1)/(p - 2)` over the same odd prime divisors of
`n`. -/
theorem singularSeries_eq_goldbachSingularSeriesLocalMultiplier (n : ℕ) :
    singularSeries n = goldbachSingularSeriesLocalMultiplier n := by
  classical
  -- Unfold both definitions.
  rw [singularSeries_def]
  unfold goldbachSingularSeriesLocalMultiplier goldbachSingularSeriesLocalPrimes
  -- The filter sets are equal; the product values per element are equal.
  rw [← goldbachSingularSeriesLocalPrimes_eq_singularSeriesFilter n]
  -- Now both sides sum over the same set; the per-element functions
  -- coincide:  `goldbachOddPrimeLocalFactor p = (p-1)/(p-2)`.
  refine Finset.prod_congr rfl (fun p _ => ?_)
  unfold goldbachOddPrimeLocalFactor
  rfl

/-! ## Section 2 — Closed `SingularSeriesPolyLogBound`

T5 closes `SingularSeriesLogNBound goldbachSingularSeriesLocalMultiplier`
(i.e., `S(n) ≤ K · log n`).  We upgrade this to
`SingularSeriesPolyLogBound` (i.e., `S(n) ≤ K · (log n)²`) by
multiplying the bound by `log n ≥ 1`, valid for `n ≥ 3`. -/

/-- For real `n ≥ 3`, `1 ≤ Real.log n`. -/
lemma one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) ≤ Real.log (n : ℝ) := by
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_e_le_3 : Real.exp 1 ≤ (n : ℝ) := by
    have h_exp_lt : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      linarith
    linarith
  have h_log_e : Real.log (Real.exp 1) = 1 := Real.log_exp _
  have h_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_mono : Real.log (Real.exp 1) ≤ Real.log (n : ℝ) :=
    Real.log_le_log h_pos h_e_le_3
  linarith [h_mono, h_log_e]

/-- **Closed `SingularSeriesPolyLogBound`** for the Hardy-Littlewood
singular series.

Combining T5 (`S(n) ≤ K · log n`) with `log n ≥ 1` (for `n ≥ 3`)
yields `S(n) ≤ K · (log n)²`, axiom-clean from
`singularSeries_log_n_bound_holds`. -/
theorem singularSeriesPolyLogBound_holds :
    SingularSeriesPolyLogBound := by
  -- Extract the T5 witness.
  obtain ⟨K, N₀, hK_pos, hT5_bd⟩ := singularSeries_log_n_bound_holds
  refine ⟨K, max N₀ 3, hK_pos, ?_⟩
  intro n hn
  -- Decompose the threshold.
  have hn_N₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn_3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  -- T5 bound for `goldbachSingularSeriesLocalMultiplier`.
  have h_T5 : goldbachSingularSeriesLocalMultiplier n ≤ K * Real.log (n : ℝ) :=
    hT5_bd n hn_N₀
  -- Rewrite via the equality `singularSeries n = goldbachSingularSeriesLocalMultiplier n`.
  have h_eq := singularSeries_eq_goldbachSingularSeriesLocalMultiplier n
  rw [h_eq]
  -- Now bound `K · log n ≤ K · (log n)²` by multiplying by `log n ≥ 1`.
  have h_log_ge_1 : (1 : ℝ) ≤ Real.log (n : ℝ) := one_le_log_of_three_le hn_3
  have h_log_pos : 0 < Real.log (n : ℝ) := by linarith
  have h_K_nn : 0 ≤ K := le_of_lt hK_pos
  -- `K · log n ≤ K · log n · log n = K · (log n)²`.
  have h_step : K * Real.log (n : ℝ) ≤ K * Real.log (n : ℝ) * Real.log (n : ℝ) := by
    have h_factor_nn : 0 ≤ K * Real.log (n : ℝ) :=
      mul_nonneg h_K_nn (le_of_lt h_log_pos)
    -- `a ≤ a · L` when `1 ≤ L` and `0 ≤ a`.
    have := mul_le_mul_of_nonneg_left h_log_ge_1 h_factor_nn
    -- this : K * log n * 1 ≤ K * log n * log n.
    simpa using this
  have h_sq : K * Real.log (n : ℝ) * Real.log (n : ℝ) = K * (Real.log (n : ℝ))^2 := by
    ring
  linarith [h_T5, h_step, h_sq.le, h_sq.ge]

/-! ## Section 3 — Headline closure

The closed-form bridge:  consuming **only** `BrunGoldbachWithSingularSeries`
(the residual Halberstam-Richert §3.11 master inequality), we produce
`ClassicalBrunGoldbachPolyLogN` axiom-clean. -/

/-- **Headline closed-form bridge.**

```
BrunGoldbachWithSingularSeries  ⇒  ClassicalBrunGoldbachPolyLogN .
```

The Bridge B of P22-T2
(`classicalBrunGoldbachPolyLogN_of_brunGoldbachWithSingularSeries`)
takes `BrunGoldbachWithSingularSeries + SingularSeriesPolyLogBound`.
Here we supply the second hypothesis from the closed T5 bound
(`singularSeriesPolyLogBound_holds`), so the residual is just the
first hypothesis. -/
theorem classicalBrunGoldbachPolyLogN_of_brunSingularSeries
    (hBG : BrunGoldbachWithSingularSeries) :
    ClassicalBrunGoldbachPolyLogN :=
  classicalBrunGoldbachPolyLogN_of_brunGoldbachWithSingularSeries
    hBG singularSeriesPolyLogBound_holds

/-! ## Section 4 — Documentation:  the residual reduction

This section is purely documentary.  It records that, after wiring T5
through Bridge B, the residual `ClassicalBrunGoldbachPolyLogN` reduces
to **JUST** `BrunGoldbachWithSingularSeries`. -/

/-- **Residual reduction marker.**  Closing
`BrunGoldbachWithSingularSeries` (the classical Halberstam-Richert §3.11
master inequality, mathlib v4.29.1 *open*) suffices to close
`ClassicalBrunGoldbachPolyLogN`.

This is the **net reduction** delivered by P22-T10:  before this file,
`ClassicalBrunGoldbachPolyLogN` required *two* open inputs
(`BrunGoldbachWithSingularSeries` and `SingularSeriesPolyLogBound`);
after this file, it requires only the *one* — the second is closed by
T5 + the equality between the two singular-series shapes. -/
theorem pathC_p22_t10_residual_marker :
    ∀ _h : BrunGoldbachWithSingularSeries, ClassicalBrunGoldbachPolyLogN :=
  fun h => classicalBrunGoldbachPolyLogN_of_brunSingularSeries h

/-! ## Section 5 — FixA''' chain wiring (documentation)

The `ClassicalBrunGoldbachPolyLogN` Prop is the polynomial-in-log
variant of the Brun-Goldbach bound:

```
r(n)  ≤  C · n · pairedBrunFactor(√n) · (log n)² .
```

Multiplying by the closed Mertens upper bound
`pairedBrunFactor(√n) ≤ C' / (log n)²` collapses the `(log n)²` factor
to a *constant*, yielding the trivial counting bound
`r(n) ≤ C · C' · n`.  Consequently the `PolyLogN` form **cannot**
absorb into the FixA' / FixA''' (`n · log log n / (log n)²` or
`n · (log log n)² / (log n)²`) reservoirs the way that
`ClassicalBrunGoldbachLogLog` does (via the AM-GM-style absorption
established in P21-T1's
`brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog`).

This is **not** a defect of T10; rather it is an inherent property of
the *polynomial-in-log* shape, which is *strictly weaker* than the
`log log n` shape (so closing it does not improve on what the FixA'
chain already has via the `LogLog` form).

We expose this as a documentation theorem:  the `PolyLogN` form is
closed (under `BrunGoldbachWithSingularSeries`) but not used by the
FixA' chain — the FixA' chain instead consumes
`ClassicalBrunGoldbachLogLog`, which is *also* closed under
`BrunGoldbachWithSingularSeries` modulo the Mertens-3
absorption `S(n) ≤ K · log log n` (T2 Bridge A,
`classicalBrunGoldbachLogLog_of_brunGoldbachWithSingularSeries`). -/
theorem pathC_p22_t10_fixA_wiring_note : True := trivial

/-! ## Section 6 — Headline summary marker

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `goldbachSingularSeriesLocalPrimes_eq_singularSeriesFilter`
   — set equality between the two singular-series filter shapes.

2. `singularSeries_eq_goldbachSingularSeriesLocalMultiplier`
   — `singularSeries n = goldbachSingularSeriesLocalMultiplier n` for
   every `n`.

3. `one_le_log_of_three_le` — for `n ≥ 3`, `1 ≤ log n`.

4. `singularSeriesPolyLogBound_holds`
   — closed `SingularSeriesPolyLogBound`:  `S(n) ≤ K · (log n)²` for
   the Hardy-Littlewood singular series.

5. `classicalBrunGoldbachPolyLogN_of_brunSingularSeries`
   — closed-form bridge:  `BrunGoldbachWithSingularSeries ⇒
   ClassicalBrunGoldbachPolyLogN`.

6. `pathC_p22_t10_residual_marker`
   — explicit one-hypothesis residual reduction. -/
theorem pathC_p22_t10_summary : True := trivial

end PathCClassicalBrunPolyLogClosed
end Gdbh

/-! ## Axiom audit -/

#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.goldbachSingularSeriesLocalPrimes_eq_singularSeriesFilter
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.singularSeries_eq_goldbachSingularSeriesLocalMultiplier
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.one_le_log_of_three_le
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.singularSeriesPolyLogBound_holds
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.classicalBrunGoldbachPolyLogN_of_brunSingularSeries
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.pathC_p22_t10_residual_marker
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.pathC_p22_t10_fixA_wiring_note
#print axioms
  Gdbh.PathCClassicalBrunPolyLogClosed.pathC_p22_t10_summary
