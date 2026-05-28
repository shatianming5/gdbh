/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtFivePrefix
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite prefix at sqrt six

Round 57 closed the `Nat.sqrt n = 5` finite prefix and left the tail beginning
at `6 ≤ Nat.sqrt n`.  This file closes the next finite prefix, `Nat.sqrt n = 6`.
The proof intentionally reuses the same coarse structure: at `z = 6`, the
residue prime set is still `{3, 5}`, so the sixteen pairwise CRT remainders are
bounded by `32n` in total and absorbed by the `z = 6` local-density lower
bound with coefficient `160`.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSixPrefix

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachBadResidueSet_card_le_two
   goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSum residueDoubleDivisorRemainderSumAtSqrt
   residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderAbsoluteRepair
  (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg)
open Gdbh.PathCResidueRemainderThresholdSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderSqrtFiveSplit
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant)
open Gdbh.PathCResidueRemainderSqrtFivePrefix
  (pathC_kGoldbach_of_remainderAfterSqrtSix_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private def sqrtSixDivisorPowerset : Finset (Finset ℕ) :=
  ({∅, {3}, {5}, {3, 5}} : Finset (Finset ℕ))

private lemma sqrtSixDivisorPowerset_card :
    sqrtSixDivisorPowerset.card = 4 := by
  decide

private lemma sqrtSixDivisorPowerset_prod_pos {d : Finset ℕ}
    (hd : d ∈ sqrtSixDivisorPowerset) :
    0 < d.prod id := by
  unfold sqrtSixDivisorPowerset at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private lemma residuePrimeSet_six :
    residuePrimeSet 6 = ({3, 5} : Finset ℕ) := by
  ext p
  simp only [residuePrimeSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp3, hp6⟩, hpprime⟩
    interval_cases p
    · exact Or.inl rfl
    · norm_num at hpprime
    · exact Or.inr rfl
    · norm_num at hpprime
  · intro hp
    rcases hp with rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

private lemma pair_powerset_filter_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ({3, 5} : Finset ℕ).powerset.filter (fun d => d.card ≤ k) =
      sqrtSixDivisorPowerset := by
  unfold sqrtSixDivisorPowerset
  rw [Finset.filter_true_of_mem]
  · decide
  · intro d hd
    have hsub : d ⊆ ({3, 5} : Finset ℕ) := by
      simpa using hd
    have hcard : d.card ≤ 2 := by
      have hcard' := Finset.card_le_card hsub
      simpa using hcard'
    exact le_trans hcard hk

private lemma residuePrimeSet_six_filter_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    (residuePrimeSet 6).powerset.filter (fun d => d.card ≤ k) =
      sqrtSixDivisorPowerset := by
  rw [residuePrimeSet_six]
  exact pair_powerset_filter_of_two_le hk

private lemma filtered_interval_card_le_n
    (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (((Finset.Icc 1 (n - 1)).filter P).card : ℝ) ≤ (n : ℝ) := by
  have hcard_nat : ((Finset.Icc 1 (n - 1)).filter P).card ≤ n := by
    have hsubset :
        (Finset.Icc 1 (n - 1)).filter P ⊆ Finset.Icc 1 (n - 1) :=
      Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 1 (n - 1)).card ≤ n := by
      rw [Nat.card_Icc]
      omega
    exact le_trans hcard hIcc
  exact_mod_cast hcard_nat

private lemma residuePairQuotientMainTerm_nonneg_le_n
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2) :
    0 ≤ residuePairQuotientMainTerm n D1 D2 ∧
      residuePairQuotientMainTerm n D1 D2 ≤ (n : ℝ) := by
  unfold residuePairQuotientMainTerm
  by_cases hdiv : Nat.gcd D1 D2 ∣ n
  · simp [hdiv]
    have hlcm_pos_nat : 0 < Nat.lcm D1 D2 := Nat.lcm_pos hD1 hD2
    have hlcm_one : (1 : ℝ) ≤ (Nat.lcm D1 D2 : ℝ) := by
      exact_mod_cast hlcm_pos_nat
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      exact_mod_cast Nat.zero_le n
    constructor
    · positivity
    · have hmul := div_le_self hn_nonneg hlcm_one
      simpa using hmul
  · simp [hdiv]

private lemma residuePairCountingRemainder_abs_le_two_n_of_pos
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hd1pos : 0 < d1.prod id) (hd2pos : 0 < d2.prod id) :
    |residuePairCountingRemainder n d1 d2| ≤ (2 * n : ℝ) := by
  unfold residuePairCountingRemainder
  let c : ℝ := (((Finset.Icc 1 (n - 1)).filter
    (fun m => (d1.prod id) ∣ m ∧ (d2.prod id) ∣ (n - m))).card : ℝ)
  let q : ℝ := residuePairQuotientMainTerm n (d1.prod id) (d2.prod id)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_le : c ≤ (n : ℝ) := by
    dsimp [c]
    exact filtered_interval_card_le_n n _
  have hq_bounds :=
    residuePairQuotientMainTerm_nonneg_le_n n (d1.prod id) (d2.prod id)
      hd1pos hd2pos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact hq_bounds.1
  have hq_le : q ≤ (n : ℝ) := by
    dsimp [q]
    exact hq_bounds.2
  calc
    |c - q| ≤ |c| + |q| := abs_sub c q
    _ = c + q := by rw [abs_of_nonneg hc_nonneg, abs_of_nonneg hq_nonneg]
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add hc_le hq_le
    _ = (2 * n : ℝ) := by ring

private lemma residueRemainderSqrtSixTerm_abs_le_two_n
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ sqrtSixDivisorPowerset)
    (hd2 : d2 ∈ sqrtSixDivisorPowerset) :
    |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residuePairCountingRemainder n d1 d2| ≤ (2 * n : ℝ) := by
  rw [abs_mul, abs_mul]
  have hmu1 :
      |((ArithmeticFunction.moebius (d1.prod id) : ℤ) : ℝ)| ≤
        (1 : ℝ) := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d1.prod id))
  have hmu2 :
      |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| ≤
        (1 : ℝ) := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d2.prod id))
  have hmu_nonneg2 :
      0 ≤ |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| :=
    abs_nonneg _
  have hmu_prod :
      |((ArithmeticFunction.moebius (d1.prod id) : ℤ) : ℝ)| *
          |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| ≤
        (1 : ℝ) := by
    have hmul :=
      mul_le_mul hmu1 hmu2 hmu_nonneg2 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hmul
  have hrem := residuePairCountingRemainder_abs_le_two_n_of_pos n
    (sqrtSixDivisorPowerset_prod_pos hd1)
    (sqrtSixDivisorPowerset_prod_pos hd2)
  have hrem_nonneg : 0 ≤ |residuePairCountingRemainder n d1 d2| :=
    abs_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hmu_prod hrem_nonneg
  calc
    |((ArithmeticFunction.moebius (d1.prod id) : ℤ) : ℝ)| *
        |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| *
        |residuePairCountingRemainder n d1 d2|
        ≤ (1 : ℝ) * |residuePairCountingRemainder n d1 d2| := by
          simpa [mul_assoc] using hmul
    _ ≤ (2 * n : ℝ) := by simpa using hrem

theorem one_fifth_le_goldbachResidueMainFactor_at_six (n : ℕ) :
    (1 / 5 : ℝ) ≤ goldbachResidueMainFactor n 6 := by
  classical
  have hfilter :
      (Finset.Icc 3 6).filter Nat.Prime = ({3, 5} : Finset ℕ) := by
    decide
  rw [goldbachResidueMainFactor, hfilter]
  rw [show ({3, 5} : Finset ℕ) = insert 3 ({5} : Finset ℕ) from rfl]
  rw [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have hcard_three_nat : (goldbachBadResidueSet n 3).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 3
  have hcard_five_nat : (goldbachBadResidueSet n 5).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 5
  have hcard_three : ((goldbachBadResidueSet n 3).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_three_nat
  have hcard_five : ((goldbachBadResidueSet n 5).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_five_nat
  have hthree :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hthree_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hmul := mul_le_mul hthree hfive (by norm_num : (0 : ℝ) ≤ 3 / 5)
    hthree_nonneg
  norm_num at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- On the `Nat.sqrt n = 6` prefix, the full signed CRT remainder is bounded
by `32n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_six
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 6) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤ (32 * n : ℝ) := by
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n 6 (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt, hsqrt]]
  unfold residueDoubleDivisorRemainderSum
  rw [residuePrimeSet_six_filter_of_two_le
    (by unfold canonicalK; omega : 2 ≤ canonicalK n)]
  calc
    |∑ d1 ∈ sqrtSixDivisorPowerset, ∑ d2 ∈ sqrtSixDivisorPowerset,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2|
        ≤ ∑ d1 ∈ sqrtSixDivisorPowerset,
            |∑ d2 ∈ sqrtSixDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2| :=
          Finset.abs_sum_le_sum_abs
            (fun d1 => ∑ d2 ∈ sqrtSixDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2)
            sqrtSixDivisorPowerset
    _ ≤ ∑ d1 ∈ sqrtSixDivisorPowerset, ∑ d2 ∈ sqrtSixDivisorPowerset,
          |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
            (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
            residuePairCountingRemainder n d1 d2| := by
          apply Finset.sum_le_sum
          intro d1 _hd1
          exact Finset.abs_sum_le_sum_abs
            (fun d2 =>
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2)
            sqrtSixDivisorPowerset
    _ ≤ ∑ _d1 ∈ sqrtSixDivisorPowerset, ∑ _d2 ∈ sqrtSixDivisorPowerset,
          (2 * n : ℝ) := by
          apply Finset.sum_le_sum
          intro d1 hd1
          apply Finset.sum_le_sum
          intro d2 hd2
          exact residueRemainderSqrtSixTerm_abs_le_two_n n hd1 hd2
    _ = (32 * n : ℝ) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [sqrtSixDivisorPowerset_card]
          ring

/-- Fixed-coefficient finite-prefix worker for the `Nat.sqrt n = 6` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 6 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `sqrt = 6` finite-prefix worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSixWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSixAtSqrt A

/-- Remaining large-range worker after removing the `sqrt = 6` prefix. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 6 A

/-- The `Nat.sqrt n = 6` relative remainder worker is closed with coefficient
`160`. -/
theorem residueRemainderRelativeSqrtSix_one_sixty :
    ResidueDoubleDivisorRemainderRelativeSqrtSixAtSqrt 160 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn hsqrt
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_six
      hn hsqrt
  have hlocal_fifth :
      (1 / 5 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    simpa [hsqrt] using one_fifth_le_goldbachResidueMainFactor_at_six n
  have hscale : (32 : ℝ) ≤ 160 * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      (32 * n : ℝ) ≤
        160 * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      (32 * n : ℝ)
          ≤ (160 * residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) :=
            hmul
      _ = 160 * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `sqrt = 6` prefix. -/
theorem residueRemainderRelativeSqrtSixWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSixWithConstant :=
  ⟨160, residueRemainderRelativeSqrtSix_one_sixty⟩

/-- A `sqrt = 6` prefix bound and a `sqrt ≥ 7` tail bound combine into the
Round 57 active `sqrt ≥ 6` target. -/
theorem residueRemainderAfterSqrtSixFixed_of_sqrtSix_and_afterSqrtSeven
    {A₆ A₇ : ℝ}
    (hSix : ResidueDoubleDivisorRemainderRelativeSqrtSixAtSqrt A₆)
    (hSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 6 A₇) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 5
      (max A₆ A₇) := by
  rcases hSix with ⟨hA₆, hSixBd⟩
  rcases hSeven with ⟨hA₇, hSevenBd⟩
  refine ⟨hA₆.trans (le_max_left A₆ A₇), ?_⟩
  intro n hn hsqrt_ge_six
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt : Nat.sqrt n = 6
  · have hbd := hSixBd n hn hsqrt
    have hscale :
        A₆ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₆ A₇ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left A₆ A₇) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_seven : 6 + 1 ≤ Nat.sqrt n := by
      have hne : 6 ≠ Nat.sqrt n := by
        intro h
        exact hsqrt h.symm
      exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hsqrt_ge_six hne)
    have hbd := hSevenBd n hn hsqrt_ge_seven
    have hscale :
        A₇ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₆ A₇ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right A₆ A₇) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 57 active
`sqrt ≥ 6` target. -/
theorem residueRemainderAfterSqrtSix_of_sqrtSix_and_afterSqrtSeven
    (hSix : ResidueDoubleDivisorRemainderRelativeSqrtSixWithConstant)
    (hSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant := by
  rcases hSix with ⟨A₆, hA₆⟩
  rcases hSeven with ⟨A₇, hA₇⟩
  exact ⟨max A₆ A₇,
    residueRemainderAfterSqrtSixFixed_of_sqrtSix_and_afterSqrtSeven
      hA₆ hA₇⟩

/-- Closing the `sqrt = 6` prefix means only the `sqrt ≥ 7` tail remains. -/
theorem residueRemainderAfterSqrtSix_of_afterSqrtSeven
    (hSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant :=
  residueRemainderAfterSqrtSix_of_sqrtSix_and_afterSqrtSeven
    residueRemainderRelativeSqrtSixWithConstant_closed hSeven

/-- Final Path C adapter after closing the `sqrt = 6` prefix. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSeven_and_countingInput
    (hSeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSix_and_countingInput
    (residueRemainderAfterSqrtSix_of_afterSqrtSeven hSeven)
    hCounting

end PathCResidueRemainderSqrtSixPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSixPrefix.one_fifth_le_goldbachResidueMainFactor_at_six
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_six
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixPrefix.residueRemainderRelativeSqrtSix_one_sixty
#print axioms
  Gdbh.PathCResidueRemainderSqrtSixPrefix.pathC_kGoldbach_of_remainderAfterSqrtSeven_and_countingInput
