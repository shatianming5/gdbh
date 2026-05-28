/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCoprimeSplitDensityBridge

/-!
# Path C -- full local-density reduction

`PathC_ResidueCoprimeSplitDensityBridge` reduces the active Round 9
coprime/non-coprime local-density Euler residual to the unsplit compatible
local-density sum.  This file removes the canonical cardinality cutoff from
that sum at `z = sqrt n`, `k = 2n`.

The remaining worker target is purely algebraic: the full double
local-density expansion over all subsets of the odd prime set must match the
existing single Goldbach-density Euler expansion.
-/

namespace Gdbh
namespace PathCResidueFullLocalDensityReduction

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueCoprimeSplitDensityBridge
  (ResidueCoprimeSplitLocalDensityEulerAtSqrt
   residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (ResidueDoubleDivisorLocalDensityEulerAtSqrt
   ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt
   residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch
   residueDoubleDivisorLocalDensitySum residueDoubleDivisorLocalDensitySumAtSqrt
   residueGoldbachDensityMainSum residueGoldbachDensityMainSum_eq_residueMainFactor
   residuePairCompatibilityWeight)

/-! ## Full-depth local-density sum -/

/-- The double local-density sum with no cardinality cutoff on the two
divisor subsets. -/
noncomputable def residueDoubleDivisorFullLocalDensitySum
    (n z : ℕ) : ℝ :=
  ∑ d₁ ∈ (residuePrimeSet z).powerset,
    ∑ d₂ ∈ (residuePrimeSet z).powerset,
      (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
        residuePairCompatibilityWeight n d₁ d₂

/-- Full-depth local-density algebra residual at the final threshold.

This is strictly smaller than the split Round 9 residual: it has no
coprime/non-coprime partition, no counting term, no tail reservoir, and no
Bonferroni cardinality cutoff. -/
def ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorFullLocalDensitySum n (Nat.sqrt n)
      = residueGoldbachDensityMainSum n (Nat.sqrt n)

/-- Reusable all-level version of the full-depth local-density algebra
identity. -/
def ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity : Prop :=
  ∀ n z : ℕ,
    residueDoubleDivisorFullLocalDensitySum n z =
      residueGoldbachDensityMainSum n z

/-! ## Removing the canonical cutoff -/

private lemma powerset_filter_card_eq_powerset_of_card_le
    {P : Finset ℕ} {k : ℕ} (hPk : P.card ≤ k) :
    P.powerset.filter (fun d => d.card ≤ k) = P.powerset := by
  classical
  ext d
  by_cases hd : d ⊆ P
  · have hcard : d.card ≤ k := (Finset.card_le_card hd).trans hPk
    simp [Finset.mem_powerset, hd, hcard]
  · simp [Finset.mem_powerset, hd]

lemma residuePrimeSet_card_le_succ (z : ℕ) :
    (residuePrimeSet z).card ≤ z + 1 := by
  classical
  have hsub : residuePrimeSet z ⊆ Finset.range (z + 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpPrime⟩
    exact Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hpIcc).2)
  simpa using Finset.card_le_card hsub

lemma residuePrimeSet_sqrt_card_le_canonicalK {n : ℕ} (hn : 16 ≤ n) :
    (residuePrimeSet (Nat.sqrt n)).card ≤ canonicalK n := by
  have hcard := residuePrimeSet_card_le_succ (Nat.sqrt n)
  have hsqrt_lt : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega : 1 < n)
  have hsqrt_succ_le : Nat.sqrt n + 1 ≤ n := Nat.succ_le_of_lt hsqrt_lt
  have hn_le_two : n ≤ 2 * n := by omega
  calc
    (residuePrimeSet (Nat.sqrt n)).card ≤ Nat.sqrt n + 1 := hcard
    _ ≤ n := hsqrt_succ_le
    _ ≤ canonicalK n := by
      unfold canonicalK
      exact hn_le_two

theorem residueDoubleDivisorLocalDensitySum_eq_full_of_card_le
    (n z k : ℕ) (hcard : (residuePrimeSet z).card ≤ k) :
    residueDoubleDivisorLocalDensitySum n z k =
      residueDoubleDivisorFullLocalDensitySum n z := by
  classical
  unfold residueDoubleDivisorLocalDensitySum
    residueDoubleDivisorFullLocalDensitySum
  rw [powerset_filter_card_eq_powerset_of_card_le hcard]

theorem residueDoubleDivisorLocalDensitySumAtSqrt_eq_full
    {n : ℕ} (hn : 16 ≤ n) :
    residueDoubleDivisorLocalDensitySumAtSqrt n =
      residueDoubleDivisorFullLocalDensitySum n (Nat.sqrt n) := by
  simpa [residueDoubleDivisorLocalDensitySumAtSqrt] using
    residueDoubleDivisorLocalDensitySum_eq_full_of_card_le
      n (Nat.sqrt n) (canonicalK n)
      (residuePrimeSet_sqrt_card_le_canonicalK hn)

/-! ## Bridges back to Round 9 residuals -/

theorem residueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt_of_full
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt := by
  intro n hn
  rw [residueDoubleDivisorLocalDensitySumAtSqrt_eq_full hn]
  exact hFull n hn

theorem residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_all
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity) :
    ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt := by
  intro n _hn
  exact hFull n (Nat.sqrt n)

theorem residueDoubleDivisorLocalDensityEulerAtSqrt_of_full
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueDoubleDivisorLocalDensityEulerAtSqrt :=
  residueDoubleDivisorLocalDensityEulerAtSqrt_of_goldbachDensityMatch
    (residueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt_of_full hFull)

theorem residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt) :
    ResidueCoprimeSplitLocalDensityEulerAtSqrt :=
  residueCoprimeSplitLocalDensityEulerAtSqrt_of_unsplit
    (residueDoubleDivisorLocalDensityEulerAtSqrt_of_full hFull)

theorem residueCoprimeSplitLocalDensityEulerAtSqrt_of_full_all
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensity) :
    ResidueCoprimeSplitLocalDensityEulerAtSqrt :=
  residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
    (residueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt_of_all hFull)

/-- Direct Euler-shape version of the at-sqrt full-depth residual. -/
theorem residueDoubleDivisorFullLocalDensityEulerAtSqrt
    (hFull : ResidueDoubleDivisorFullLocalDensityMatchesGoldbachDensityAtSqrt)
    {n : ℕ} (hn : 16 ≤ n) :
    residueDoubleDivisorFullLocalDensitySum n (Nat.sqrt n)
      = goldbachResidueMainFactor n (Nat.sqrt n) := by
  rw [hFull n hn, residueGoldbachDensityMainSum_eq_residueMainFactor]

end PathCResidueFullLocalDensityReduction
end Gdbh

#print axioms
  Gdbh.PathCResidueFullLocalDensityReduction.residueDoubleDivisorLocalDensitySum_eq_full_of_card_le
#print axioms
  Gdbh.PathCResidueFullLocalDensityReduction.residueDoubleDivisorLocalDensitySumAtSqrt_eq_full
#print axioms
  Gdbh.PathCResidueFullLocalDensityReduction.residueDoubleDivisorLocalDensityMatchesGoldbachDensityAtSqrt_of_full
#print axioms
  Gdbh.PathCResidueFullLocalDensityReduction.residueCoprimeSplitLocalDensityEulerAtSqrt_of_full
