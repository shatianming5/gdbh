/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSixPrefix
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite prefix at sqrt seven

Round 58 closed the `Nat.sqrt n = 6` finite prefix and left the tail beginning
at `7 ≤ Nat.sqrt n`.  This file closes the next finite prefix, `Nat.sqrt n = 7`.
The proof keeps the same deliberately coarse structure: at `z = 7`, the
residue prime set is `{3, 5, 7}`, so the sixty-four pairwise CRT remainders are
bounded by `128n` in total and absorbed by the `z = 7` local-density lower
bound with coefficient `896`.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSevenPrefix

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
open Gdbh.PathCResidueRemainderSqrtSixPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSeven_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private def sqrtSevenDivisorPowerset : Finset (Finset ℕ) :=
  ({∅, {3}, {5}, {7}, {3, 5}, {3, 7}, {5, 7}, {3, 5, 7}} :
    Finset (Finset ℕ))

private lemma sqrtSevenDivisorPowerset_card :
    sqrtSevenDivisorPowerset.card = 8 := by
  decide

private lemma sqrtSevenDivisorPowerset_prod_pos {d : Finset ℕ}
    (hd : d ∈ sqrtSevenDivisorPowerset) :
    0 < d.prod id := by
  unfold sqrtSevenDivisorPowerset at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma residuePrimeSet_seven :
    residuePrimeSet 7 = ({3, 5, 7} : Finset ℕ) := by
  ext p
  simp only [residuePrimeSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp3, hp7⟩, hpprime⟩
    interval_cases p
    · exact Or.inl rfl
    · norm_num at hpprime
    · exact Or.inr (Or.inl rfl)
    · norm_num at hpprime
    · exact Or.inr (Or.inr rfl)
  · intro hp
    rcases hp with rfl | hrest
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    rcases hrest with rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

private lemma pair_powerset_filter_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    ({3, 5, 7} : Finset ℕ).powerset.filter (fun d => d.card ≤ k) =
      sqrtSevenDivisorPowerset := by
  unfold sqrtSevenDivisorPowerset
  rw [Finset.filter_true_of_mem]
  · decide
  · intro d hd
    have hsub : d ⊆ ({3, 5, 7} : Finset ℕ) := by
      simpa using hd
    have hcard : d.card ≤ 3 := by
      have hcard' := Finset.card_le_card hsub
      simpa using hcard'
    exact le_trans hcard hk

private lemma residuePrimeSet_seven_filter_of_three_le {k : ℕ}
    (hk : 3 ≤ k) :
    (residuePrimeSet 7).powerset.filter (fun d => d.card ≤ k) =
      sqrtSevenDivisorPowerset := by
  rw [residuePrimeSet_seven]
  exact pair_powerset_filter_of_three_le hk

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

private lemma residueRemainderSqrtSevenTerm_abs_le_two_n
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ sqrtSevenDivisorPowerset)
    (hd2 : d2 ∈ sqrtSevenDivisorPowerset) :
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
    (sqrtSevenDivisorPowerset_prod_pos hd1)
    (sqrtSevenDivisorPowerset_prod_pos hd2)
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

theorem one_seventh_le_goldbachResidueMainFactor_at_seven (n : ℕ) :
    (1 / 7 : ℝ) ≤ goldbachResidueMainFactor n 7 := by
  classical
  have hfilter :
      (Finset.Icc 3 7).filter Nat.Prime = ({3, 5, 7} : Finset ℕ) := by
    decide
  rw [goldbachResidueMainFactor, hfilter]
  rw [show ({3, 5, 7} : Finset ℕ) =
      insert 3 (insert 5 ({7} : Finset ℕ)) from rfl]
  rw [Finset.prod_insert (by decide : (3 : ℕ) ∉ insert 5 ({7} : Finset ℕ))]
  rw [Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7} : Finset ℕ))]
  rw [Finset.prod_singleton]
  have hcard_three_nat : (goldbachBadResidueSet n 3).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 3
  have hcard_five_nat : (goldbachBadResidueSet n 5).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 5
  have hcard_seven_nat : (goldbachBadResidueSet n 7).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n 7
  have hcard_three : ((goldbachBadResidueSet n 3).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_three_nat
  have hcard_five : ((goldbachBadResidueSet n 5).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_five_nat
  have hcard_seven : ((goldbachBadResidueSet n 7).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard_seven_nat
  have hthree :
      (1 / 3 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive :
      (3 / 5 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hseven :
      (5 / 7 : ℝ) ≤
        1 - ((goldbachBadResidueSet n 7).card : ℝ) / 7 := by
    nlinarith
  have hthree_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 3).card : ℝ) / 3 := by
    nlinarith
  have hfive_nonneg :
      0 ≤ 1 - ((goldbachBadResidueSet n 5).card : ℝ) / 5 := by
    nlinarith
  have hmul_five_seven :=
    mul_le_mul hfive hseven (by norm_num : (0 : ℝ) ≤ 5 / 7) hfive_nonneg
  have hmul_all :=
    mul_le_mul hthree hmul_five_seven
      (by norm_num : (0 : ℝ) ≤ (3 / 5) * (5 / 7)) hthree_nonneg
  norm_num at hmul_all
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_all

/-- On the `Nat.sqrt n = 7` prefix, the full signed CRT remainder is bounded
by `128n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_one_twenty_eight_mul_n_of_sqrt_seven
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 7) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤ (128 * n : ℝ) := by
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n 7 (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt, hsqrt]]
  unfold residueDoubleDivisorRemainderSum
  rw [residuePrimeSet_seven_filter_of_three_le
    (by unfold canonicalK; omega : 3 ≤ canonicalK n)]
  calc
    |∑ d1 ∈ sqrtSevenDivisorPowerset, ∑ d2 ∈ sqrtSevenDivisorPowerset,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2|
        ≤ ∑ d1 ∈ sqrtSevenDivisorPowerset,
            |∑ d2 ∈ sqrtSevenDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2| :=
          Finset.abs_sum_le_sum_abs
            (fun d1 => ∑ d2 ∈ sqrtSevenDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2)
            sqrtSevenDivisorPowerset
    _ ≤ ∑ d1 ∈ sqrtSevenDivisorPowerset, ∑ d2 ∈ sqrtSevenDivisorPowerset,
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
            sqrtSevenDivisorPowerset
    _ ≤ ∑ _d1 ∈ sqrtSevenDivisorPowerset, ∑ _d2 ∈ sqrtSevenDivisorPowerset,
          (2 * n : ℝ) := by
          apply Finset.sum_le_sum
          intro d1 hd1
          apply Finset.sum_le_sum
          intro d2 hd2
          exact residueRemainderSqrtSevenTerm_abs_le_two_n n hd1 hd2
    _ = (128 * n : ℝ) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [sqrtSevenDivisorPowerset_card]
          ring

/-- Fixed-coefficient finite-prefix worker for the `Nat.sqrt n = 7` slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → Nat.sqrt n = 7 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `sqrt = 7` finite-prefix worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSevenWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSevenAtSqrt A

/-- Remaining large-range worker after removing the `sqrt = 7` prefix. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtEightWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 7 A

/-- The `Nat.sqrt n = 7` relative remainder worker is closed with coefficient
`896`. -/
theorem residueRemainderRelativeSqrtSeven_eight_ninety_six :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenAtSqrt 896 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn hsqrt
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_one_twenty_eight_mul_n_of_sqrt_seven
      hn hsqrt
  have hlocal_seventh :
      (1 / 7 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    simpa [hsqrt] using one_seventh_le_goldbachResidueMainFactor_at_seven n
  have hscale :
      (128 : ℝ) ≤ 896 * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      (128 * n : ℝ) ≤
        896 * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      (128 * n : ℝ)
          ≤ (896 * residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) :=
            hmul
      _ = 896 * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `sqrt = 7` prefix. -/
theorem residueRemainderRelativeSqrtSevenWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSevenWithConstant :=
  ⟨896, residueRemainderRelativeSqrtSeven_eight_ninety_six⟩

/-- A `sqrt = 7` prefix bound and a `sqrt ≥ 8` tail bound combine into the
Round 58 active `sqrt ≥ 7` target. -/
theorem residueRemainderAfterSqrtSevenFixed_of_sqrtSeven_and_afterSqrtEight
    {A₇ A₈ : ℝ}
    (hSeven : ResidueDoubleDivisorRemainderRelativeSqrtSevenAtSqrt A₇)
    (hEight :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 7 A₈) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 6
      (max A₇ A₈) := by
  rcases hSeven with ⟨hA₇, hSevenBd⟩
  rcases hEight with ⟨_hA₈, hEightBd⟩
  refine ⟨hA₇.trans (le_max_left A₇ A₈), ?_⟩
  intro n hn hsqrt_ge_seven
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt : Nat.sqrt n = 7
  · have hbd := hSevenBd n hn hsqrt
    have hscale :
        A₇ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₇ A₈ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left A₇ A₈) hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_eight : 7 + 1 ≤ Nat.sqrt n := by
      have hne : 7 ≠ Nat.sqrt n := by
        intro h
        exact hsqrt h.symm
      exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hsqrt_ge_seven hne)
    have hbd := hEightBd n hn hsqrt_ge_eight
    have hscale :
        A₈ * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max A₇ A₈ *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right A₇ A₈) hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 58 active
`sqrt ≥ 7` target. -/
theorem residueRemainderAfterSqrtSeven_of_sqrtSeven_and_afterSqrtEight
    (hSeven :
      ResidueDoubleDivisorRemainderRelativeSqrtSevenWithConstant)
    (hEight :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtEightWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant := by
  rcases hSeven with ⟨A₇, hA₇⟩
  rcases hEight with ⟨A₈, hA₈⟩
  exact ⟨max A₇ A₈,
    residueRemainderAfterSqrtSevenFixed_of_sqrtSeven_and_afterSqrtEight
      hA₇ hA₈⟩

/-- Closing the `sqrt = 7` prefix means only the `sqrt ≥ 8` tail remains. -/
theorem residueRemainderAfterSqrtSeven_of_afterSqrtEight
    (hEight :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtEightWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSevenWithConstant :=
  residueRemainderAfterSqrtSeven_of_sqrtSeven_and_afterSqrtEight
    residueRemainderRelativeSqrtSevenWithConstant_closed hEight

/-- Final Path C adapter after closing the `sqrt = 7` prefix. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtEight_and_countingInput
    (hEight :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtEightWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSeven_and_countingInput
    (residueRemainderAfterSqrtSeven_of_afterSqrtEight hEight)
    hCounting

end PathCResidueRemainderSqrtSevenPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenPrefix.one_seventh_le_goldbachResidueMainFactor_at_seven
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_one_twenty_eight_mul_n_of_sqrt_seven
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenPrefix.residueRemainderRelativeSqrtSeven_eight_ninety_six
#print axioms
  Gdbh.PathCResidueRemainderSqrtSevenPrefix.pathC_kGoldbach_of_remainderAfterSqrtEight_and_countingInput
