/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtElevenToSixteenPrefix
import Gdbh.PathC_ResidueCanonicalSqrtSeventeenToThirtySixSplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt seventeen to thirty-six

Round 61 closed the `11 ≤ Nat.sqrt n ≤ 16` finite block and left the tail
beginning at `17 ≤ Nat.sqrt n`.  This file closes the larger finite block
`17 ≤ Nat.sqrt n ≤ 36`.  The proof remains finite and deliberately coarse:
throughout the block the residue prime set has at most ten primes, so the
double divisor family has at most `1024 * 1024` pairs.  Each pairwise CRT
remainder is bounded by `2n`, giving `2097152n`, which is absorbed by the
existing `1 / 17` local-density lower bound.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtSeventeenToThirtySixPrefix

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
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold)
open Gdbh.PathCResidueRemainderSqrtElevenToSixteenPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtSeventeenWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtSeventeen_and_countingInput)
open Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
  (one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_thirty_six)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private lemma residuePrimeSet_card_le_ten_of_seventeen_to_thirty_six {z : ℕ}
    (hz17 : 17 ≤ z) (hz36 : z ≤ 36) :
    (residuePrimeSet z).card ≤ 10 := by
  interval_cases z <;> decide

private lemma residueDivisorProd_pos_of_mem_filter {z k : ℕ}
    {d : Finset ℕ}
    (hd : d ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)) :
    0 < d.prod id := by
  have hdsub : d ⊆ residuePrimeSet z := by
    have hpowerset : d ∈ (residuePrimeSet z).powerset :=
      (Finset.mem_filter.mp hd).1
    simpa using hpowerset
  exact Finset.prod_pos (fun p hp => by
    have hpz : p ∈ residuePrimeSet z := hdsub hp
    unfold residuePrimeSet at hpz
    simp only [Finset.mem_filter, Finset.mem_Icc] at hpz
    exact lt_of_lt_of_le (by norm_num : 0 < 3) hpz.1.1)

private lemma filteredResiduePowerset_card_le_ten_twenty_four {z k : ℕ}
    (hz17 : 17 ≤ z) (hz36 : z ≤ 36) :
    ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
      1024 := by
  have hfilter_card :
      ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
        (residuePrimeSet z).powerset.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hbase : (residuePrimeSet z).card ≤ 10 :=
    residuePrimeSet_card_le_ten_of_seventeen_to_thirty_six hz17 hz36
  have hpow : 2 ^ (residuePrimeSet z).card ≤ 1024 := by
    have hpow' := Nat.pow_le_pow_right (by norm_num : 0 < 2) hbase
    norm_num at hpow'
    exact hpow'
  have hpowerset : (residuePrimeSet z).powerset.card ≤ 1024 := by
    rw [Finset.card_powerset]
    exact hpow
  exact le_trans hfilter_card hpowerset

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

private lemma residueRemainderTerm_abs_le_two_n_of_mem_filter
    (n z k : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k))
    (hd2 : d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)) :
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
    (residueDivisorProd_pos_of_mem_filter hd1)
    (residueDivisorProd_pos_of_mem_filter hd2)
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

/-- On the block `17 ≤ Nat.sqrt n ≤ 36`, the full signed CRT remainder is
bounded by `2097152n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_two_million_ninety_seven_thousand_one_fifty_two_mul_n_of_sqrt_seventeen_to_thirty_six
    {n : ℕ} (hn : 16 ≤ n) (hsqrt_ge_seventeen : 17 ≤ Nat.sqrt n)
    (hsqrt_le_thirty_six : Nat.sqrt n ≤ 36) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤ (2097152 * n : ℝ) := by
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet (Nat.sqrt n)).powerset.filter
      (fun d => d.card ≤ canonicalK n)
  have hFcard_nat : F.card ≤ 1024 := by
    dsimp [F]
    exact filteredResiduePowerset_card_le_ten_twenty_four
      hsqrt_ge_seventeen hsqrt_le_thirty_six
  have hFcard_real : (F.card : ℝ) ≤ 1024 := by
    exact_mod_cast hFcard_nat
  have hFcard_nonneg : 0 ≤ (F.card : ℝ) := by
    positivity
  have hFcard_sq :
      (F.card : ℝ) * (F.card : ℝ) ≤ 1024 * 1024 := by
    exact mul_le_mul hFcard_real hFcard_real hFcard_nonneg
      (by norm_num : (0 : ℝ) ≤ 1024)
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n (Nat.sqrt n) (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt]]
  unfold residueDoubleDivisorRemainderSum
  change
    |∑ d1 ∈ F, ∑ d2 ∈ F,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2| ≤ (2097152 * n : ℝ)
  calc
    |∑ d1 ∈ F, ∑ d2 ∈ F,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2|
        ≤ ∑ d1 ∈ F,
            |∑ d2 ∈ F,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2| :=
          Finset.abs_sum_le_sum_abs
            (fun d1 => ∑ d2 ∈ F,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2)
            F
    _ ≤ ∑ d1 ∈ F, ∑ d2 ∈ F,
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
            F
    _ ≤ ∑ d1 ∈ F, ∑ d2 ∈ F, (2 * n : ℝ) := by
          apply Finset.sum_le_sum
          intro d1 hd1
          apply Finset.sum_le_sum
          intro d2 hd2
          exact residueRemainderTerm_abs_le_two_n_of_mem_filter
            n (Nat.sqrt n) (canonicalK n) hd1 hd2
    _ = (F.card : ℝ) * ((F.card : ℝ) * (2 * n : ℝ)) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [nsmul_eq_mul]
    _ ≤ (2097152 * n : ℝ) := by
          have hn_nonneg : 0 ≤ (2 * n : ℝ) := by
            positivity
          have hmul :=
            mul_le_mul_of_nonneg_right hFcard_sq hn_nonneg
          calc
            (F.card : ℝ) * ((F.card : ℝ) * (2 * n : ℝ))
                = ((F.card : ℝ) * (F.card : ℝ)) * (2 * n : ℝ) := by
                  ring
            _ ≤ (1024 * 1024 : ℝ) * (2 * n : ℝ) := hmul
            _ = (2097152 * n : ℝ) := by ring

/-- Fixed-coefficient finite-block worker for the `17 ≤ Nat.sqrt n ≤ 36`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 17 ≤ Nat.sqrt n → Nat.sqrt n ≤ 36 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `17 ≤ sqrt ≤ 36` finite-block worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixAtSqrt A

/-- Remaining large-range worker after removing the `17 ≤ sqrt ≤ 36` block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 36 A

/-- The `17 ≤ Nat.sqrt n ≤ 36` relative remainder worker is closed with
coefficient `35651584`. -/
theorem residueRemainderRelativeSqrtSeventeenToThirtySix_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixAtSqrt
      35651584 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn hsqrt_ge_seventeen hsqrt_le_thirty_six
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_two_million_ninety_seven_thousand_one_fifty_two_mul_n_of_sqrt_seventeen_to_thirty_six
      hn hsqrt_ge_seventeen hsqrt_le_thirty_six
  have hlocal_seventeenth :
      (1 / 17 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_seventeenth_le_goldbachResidueMainFactor_of_seventeen_le_of_le_thirty_six
        n (Nat.sqrt n) hsqrt_ge_seventeen hsqrt_le_thirty_six
  have hscale :
      (2097152 : ℝ) ≤
        35651584 * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      (2097152 * n : ℝ) ≤
        35651584 *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      (2097152 * n : ℝ)
          ≤
            (35651584 * residueDoubleDivisorLocalDensitySumAtSqrt n) *
              (n : ℝ) := hmul
      _ =
          35651584 *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `17 ≤ sqrt ≤ 36` block. -/
theorem residueRemainderRelativeSqrtSeventeenToThirtySixWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixWithConstant :=
  ⟨35651584, residueRemainderRelativeSqrtSeventeenToThirtySix_explicit⟩

/-- A closed `17 ≤ sqrt ≤ 36` block and a `sqrt ≥ 37` tail bound combine into
the Round 61 active `sqrt ≥ 17` target. -/
theorem residueRemainderAfterSqrtSeventeenFixed_of_sqrtSeventeenToThirtySix_and_afterSqrtThirtySeven
    {Ablock AthirtySeven : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixAtSqrt
        Ablock)
    (hThirtySeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 36
        AthirtySeven) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 16
      (max Ablock AthirtySeven) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hThirtySeven with ⟨_hAthirtySeven, hThirtySevenBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AthirtySeven), ?_⟩
  intro n hn hsqrt_ge_seventeen
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_thirty_six : Nat.sqrt n ≤ 36
  · have hbd := hBlockBd n hn hsqrt_ge_seventeen hsqrt_le_thirty_six
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AthirtySeven *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left Ablock AthirtySeven)
        hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_thirty_seven : 36 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr (lt_of_not_ge hsqrt_le_thirty_six)
    have hbd := hThirtySevenBd n hn hsqrt_ge_thirty_seven
    have hscale :
        AthirtySeven *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AthirtySeven *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right Ablock AthirtySeven)
        hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 61 active
`sqrt ≥ 17` target. -/
theorem residueRemainderAfterSqrtSeventeen_of_sqrtSeventeenToThirtySix_and_afterSqrtThirtySeven
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtSeventeenToThirtySixWithConstant)
    (hThirtySeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSeventeenWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hThirtySeven with ⟨AthirtySeven, hAthirtySeven⟩
  exact ⟨max Ablock AthirtySeven,
    residueRemainderAfterSqrtSeventeenFixed_of_sqrtSeventeenToThirtySix_and_afterSqrtThirtySeven
      hAblock hAthirtySeven⟩

/-- Closing the `17 ≤ sqrt ≤ 36` block means only the `sqrt ≥ 37` tail
remains. -/
theorem residueRemainderAfterSqrtSeventeen_of_afterSqrtThirtySeven
    (hThirtySeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtSeventeenWithConstant :=
  residueRemainderAfterSqrtSeventeen_of_sqrtSeventeenToThirtySix_and_afterSqrtThirtySeven
    residueRemainderRelativeSqrtSeventeenToThirtySixWithConstant_closed
    hThirtySeven

/-- Final Path C adapter after closing the `17 ≤ sqrt ≤ 36` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtThirtySeven_and_countingInput
    (hThirtySeven :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtSeventeen_and_countingInput
    (residueRemainderAfterSqrtSeventeen_of_afterSqrtThirtySeven
      hThirtySeven)
    hCounting

end PathCResidueRemainderSqrtSeventeenToThirtySixPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtSeventeenToThirtySixPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_two_million_ninety_seven_thousand_one_fifty_two_mul_n_of_sqrt_seventeen_to_thirty_six
#print axioms
  Gdbh.PathCResidueRemainderSqrtSeventeenToThirtySixPrefix.residueRemainderRelativeSqrtSeventeenToThirtySix_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtSeventeenToThirtySixPrefix.pathC_kGoldbach_of_remainderAfterSqrtThirtySeven_and_countingInput
