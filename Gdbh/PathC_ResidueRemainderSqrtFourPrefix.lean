/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderThresholdSplit
import Gdbh.PathC_ResidueCanonicalSqrtSplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Path C -- relative remainder finite prefix at sqrt four

Round 54 split the relative remainder target into a finite square-root prefix
and a large-range analytic tail.  This file closes the first nonempty prefix:
`Nat.sqrt n ≤ 4`.  Since `16 ≤ n`, this is exactly the `Nat.sqrt n = 4`
range, so the residue prime set is `{3}` and the double-divisor remainder is
an explicit four-term calculation.

The result leaves the next active residue-side worker as the large-range
relative remainder estimate beginning at `5 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtFourPrefix

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSum residueDoubleDivisorRemainderSumAtSqrt
   residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold
   ResidueDoubleDivisorRemainderRelativeFinitePrefixAtSqrt
   ResidueDoubleDivisorRemainderRelativeThresholdSplit
   ResidueDoubleDivisorRemainderRelativeThresholdSplitAtSqrt
   pathC_kGoldbach_of_remainderThresholdSplit_and_countingInput)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (one_third_le_goldbachResidueMainFactor_at_four)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private lemma residuePrimeSet_four :
    residuePrimeSet 4 = ({3} : Finset ℕ) := by
  ext p
  simp only [residuePrimeSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp3, hp4⟩, hpprime⟩
    interval_cases p
    · rfl
    · norm_num at hpprime
  · intro hp
    subst p
    exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

private lemma singleton_powerset_filter_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    ({3} : Finset ℕ).powerset.filter (fun d => d.card ≤ k) =
      ({∅, {3}} : Finset (Finset ℕ)) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hd
    have hsub := hd.1
    by_cases h3 : 3 ∈ d
    · right
      ext x
      constructor
      · intro hx
        have hx3 := hsub hx
        simpa using hx3
      · intro hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact h3
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx3 := hsub hx
      simp only [Finset.mem_singleton] at hx3
      subst x
      exact h3 hx
  · intro hd
    rcases hd with rfl | rfl
    · constructor <;> simp
    · constructor
      · simp
      · simpa using hk

private lemma residuePrimeSet_four_filter_of_one_le {k : ℕ}
    (hk : 1 ≤ k) :
    (residuePrimeSet 4).powerset.filter (fun d => d.card ≤ k) =
      ({∅, {3}} : Finset (Finset ℕ)) := by
  rw [residuePrimeSet_four]
  exact singleton_powerset_filter_of_one_le hk

private lemma card_left_multiples_three_of_sqrt_four
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 4) :
    ((Finset.Icc 1 (n - 1)).filter (fun m => 3 ∣ m)).card =
      (n - 1) / 3 := by
  have hlt25 : n < 25 := by
    simpa [hsqrt] using Nat.lt_succ_sqrt n
  have hn24 : n ≤ 24 := by omega
  interval_cases n <;> decide

private lemma card_right_multiples_three_of_sqrt_four
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 4) :
    ((Finset.Icc 1 (n - 1)).filter
      (fun m => 3 ∣ (n - m))).card = (n - 1) / 3 := by
  have hlt25 : n < 25 := by
    simpa [hsqrt] using Nat.lt_succ_sqrt n
  have hn24 : n ≤ 24 := by omega
  interval_cases n <;> decide

private lemma card_common_multiples_three_of_sqrt_four
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 4) :
    ((Finset.Icc 1 (n - 1)).filter
      (fun m => 3 ∣ m ∧ 3 ∣ (n - m))).card =
        if 3 ∣ n then n / 3 - 1 else 0 := by
  have hlt25 : n < 25 := by
    simpa [hsqrt] using Nat.lt_succ_sqrt n
  have hn24 : n ≤ 24 := by omega
  interval_cases n <;> decide

/-- On the `Nat.sqrt n = 4` prefix, the signed double-divisor remainder is
always one of `-1/3`, `0`, or `1/3`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_third_of_sqrt_four
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 4) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤ (1 / 3 : ℝ) := by
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n 4 (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt, hsqrt]]
  unfold residueDoubleDivisorRemainderSum residuePairCountingRemainder
    residuePairQuotientMainTerm
  rw [residuePrimeSet_four_filter_of_one_le
    (by unfold canonicalK; omega : 1 ≤ canonicalK n)]
  have hmu3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  simp [hmu3]
  rw [card_left_multiples_three_of_sqrt_four hn hsqrt,
    card_right_multiples_three_of_sqrt_four hn hsqrt,
    card_common_multiples_three_of_sqrt_four hn hsqrt]
  have hlt25 : n < 25 := by
    simpa [hsqrt] using Nat.lt_succ_sqrt n
  have hn24 : n ≤ 24 := by omega
  interval_cases n <;> norm_num

/-- The first finite prefix of the Round 54 relative remainder split is
closed with coefficient `1`. -/
theorem residueRemainderRelativeFinitePrefixSqrtFour_one :
    ResidueDoubleDivisorRemainderRelativeFinitePrefixAtSqrt 4 1 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn hsqrt_le_four
  have hsqrt_ge_four : 4 ≤ Nat.sqrt n :=
    Nat.le_sqrt.mpr (by omega : 4 * 4 ≤ n)
  have hsqrt : Nat.sqrt n = 4 := le_antisymm hsqrt_le_four hsqrt_ge_four
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_third_of_sqrt_four
      hn hsqrt
  have hlocal_third :
      (1 / 3 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    simpa [hsqrt] using one_third_le_goldbachResidueMainFactor_at_four n
  have hlocal_nonneg :
      0 ≤ residueDoubleDivisorLocalDensitySumAtSqrt n :=
    residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn
  have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hlocal_le_main :
      residueDoubleDivisorLocalDensitySumAtSqrt n
        ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    have hmul :=
      mul_le_mul_of_nonneg_right hn_ge_one_real hlocal_nonneg
    simpa [one_mul] using hmul
  calc
    |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ (1 / 3 : ℝ) := hrem
    _ ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := hlocal_third
    _ ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n :=
      hlocal_le_main
    _ = (1 : ℝ) *
        ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by ring

/-- The remaining large-range worker after the closed `sqrt = 4` prefix. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 4 A

/-- A large-range relative estimate from `5 ≤ Nat.sqrt n`, together with the
closed `sqrt = 4` prefix, supplies the full Round 54 threshold split. -/
theorem residueRemainderThresholdSplit_of_afterSqrtFive
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant) :
    ResidueDoubleDivisorRemainderRelativeThresholdSplit := by
  rcases hAfter with ⟨A, hA⟩
  exact ⟨4, 1, A, residueRemainderRelativeFinitePrefixSqrtFour_one, hA⟩

/-- Fixed-threshold version of the previous bridge. -/
theorem residueRemainderThresholdSplitAtSqrtFour_of_afterSqrtFive
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant) :
    ResidueDoubleDivisorRemainderRelativeThresholdSplitAtSqrt 4 := by
  rcases hAfter with ⟨A, hA⟩
  exact ⟨1, A, residueRemainderRelativeFinitePrefixSqrtFour_one, hA⟩

/-- Final Path C adapter after the closed first finite prefix. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtFive_and_countingInput
    (hAfter :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtFiveWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderThresholdSplit_and_countingInput
    (residueRemainderThresholdSplit_of_afterSqrtFive hAfter)
    hCounting

end PathCResidueRemainderSqrtFourPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtFourPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_third_of_sqrt_four
#print axioms
  Gdbh.PathCResidueRemainderSqrtFourPrefix.residueRemainderRelativeFinitePrefixSqrtFour_one
#print axioms
  Gdbh.PathCResidueRemainderSqrtFourPrefix.residueRemainderThresholdSplit_of_afterSqrtFive
#print axioms
  Gdbh.PathCResidueRemainderSqrtFourPrefix.pathC_kGoldbach_of_remainderAfterSqrtFive_and_countingInput
