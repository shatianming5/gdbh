/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtSeventeenToThirtySixPrefix
import Gdbh.PathC_ResidueCanonicalSqrtThirtySevenToHundredSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite block from sqrt thirty-seven to hundred

Round 62 closed the `17 ≤ Nat.sqrt n ≤ 36` finite block and left the tail
beginning at `37 ≤ Nat.sqrt n`.  This file closes the next finite block
`37 ≤ Nat.sqrt n ≤ 100`.  The proof uses a finite cardinal envelope: the
residue prime set is a subset of the odd primes up to `100`, hence has at most
`24` elements.  The double divisor family therefore has at most
`2^24 * 2^24` pairs, and each pairwise CRT remainder is bounded by `2n`.
The resulting finite remainder is absorbed by the existing `1 / 37`
local-density lower bound.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtThirtySevenToHundredPrefix

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
open Gdbh.PathCResidueRemainderSqrtSeventeenToThirtySixPrefix
  (ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant
   pathC_kGoldbach_of_remainderAfterSqrtThirtySeven_and_countingInput)
open Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit
  (one_thirty_seventh_le_goldbachResidueMainFactor_of_le_hundred
   prime_filter_three_to_hundred)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-- Coarse finite remainder multiplier for the `37 ≤ sqrt ≤ 100` block:
`(2^24)^2 * 2`. -/
noncomputable def sqrtThirtySevenToHundredRemainderBound : ℝ :=
  ((2 : ℝ) ^ 24 * (2 : ℝ) ^ 24) * 2

/-- Relative coefficient after absorbing the finite remainder by the
`1 / 37` local-density lower bound. -/
noncomputable def sqrtThirtySevenToHundredRelativeCoefficient : ℝ :=
  37 * sqrtThirtySevenToHundredRemainderBound

private lemma residuePrimeSet_subset_primes_to_hundred {z : ℕ}
    (hz100 : z ≤ 100) :
    residuePrimeSet z ⊆ (Finset.Icc 3 100).filter Nat.Prime := by
  intro p hp
  unfold residuePrimeSet at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, le_trans hp.1.2 hz100⟩, hp.2⟩

private lemma residuePrimeSet_card_le_twenty_four_of_le_hundred {z : ℕ}
    (hz100 : z ≤ 100) :
    (residuePrimeSet z).card ≤ 24 := by
  have hsubset := residuePrimeSet_subset_primes_to_hundred hz100
  have hcard := Finset.card_le_card hsubset
  have hhundred :
      ((Finset.Icc 3 100).filter Nat.Prime).card = 24 := by
    rw [prime_filter_three_to_hundred]
    decide
  simpa [hhundred] using hcard

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

private lemma filteredResiduePowerset_card_le_two_pow_twenty_four {z k : ℕ}
    (hz100 : z ≤ 100) :
    ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
      2 ^ 24 := by
  have hfilter_card :
      ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
        (residuePrimeSet z).powerset.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hbase : (residuePrimeSet z).card ≤ 24 :=
    residuePrimeSet_card_le_twenty_four_of_le_hundred hz100
  have hpow : 2 ^ (residuePrimeSet z).card ≤ 2 ^ 24 :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hbase
  have hpowerset : (residuePrimeSet z).powerset.card ≤ 2 ^ 24 := by
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

/-- On the block `37 ≤ Nat.sqrt n ≤ 100`, the full signed CRT remainder is
bounded by the finite cardinal envelope `(2^24)^2 * 2n`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_thirty_seven_to_hundred
    {n : ℕ} (hn : 16 ≤ n) (_hsqrt_ge_thirty_seven : 37 ≤ Nat.sqrt n)
    (hsqrt_le_hundred : Nat.sqrt n ≤ 100) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      sqrtThirtySevenToHundredRemainderBound * (n : ℝ) := by
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet (Nat.sqrt n)).powerset.filter
      (fun d => d.card ≤ canonicalK n)
  have hFcard_nat : F.card ≤ 2 ^ 24 := by
    dsimp [F]
    exact filteredResiduePowerset_card_le_two_pow_twenty_four
      hsqrt_le_hundred
  have hFcard_real : (F.card : ℝ) ≤ (2 : ℝ) ^ 24 := by
    exact_mod_cast hFcard_nat
  have hFcard_nonneg : 0 ≤ (F.card : ℝ) := by
    positivity
  have hFcard_sq :
      (F.card : ℝ) * (F.card : ℝ) ≤
        (2 : ℝ) ^ 24 * (2 : ℝ) ^ 24 := by
    exact mul_le_mul hFcard_real hFcard_real hFcard_nonneg
      (by positivity)
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n (Nat.sqrt n) (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt]]
  unfold residueDoubleDivisorRemainderSum
  change
    |∑ d1 ∈ F, ∑ d2 ∈ F,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2| ≤
      sqrtThirtySevenToHundredRemainderBound * (n : ℝ)
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
    _ ≤ sqrtThirtySevenToHundredRemainderBound * (n : ℝ) := by
          have hn_nonneg : 0 ≤ (2 * n : ℝ) := by
            positivity
          have hmul :=
            mul_le_mul_of_nonneg_right hFcard_sq hn_nonneg
          calc
            (F.card : ℝ) * ((F.card : ℝ) * (2 * n : ℝ))
                = ((F.card : ℝ) * (F.card : ℝ)) * (2 * n : ℝ) := by
                  ring
            _ ≤ ((2 : ℝ) ^ 24 * (2 : ℝ) ^ 24) * (2 * n : ℝ) := hmul
            _ = sqrtThirtySevenToHundredRemainderBound * (n : ℝ) := by
              unfold sqrtThirtySevenToHundredRemainderBound
              ring

/-- Fixed-coefficient finite-block worker for the `37 ≤ Nat.sqrt n ≤ 100`
slice. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredAtSqrt
    (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ n : ℕ, 16 ≤ n → 37 ≤ Nat.sqrt n → Nat.sqrt n ≤ 100 →
      |residueDoubleDivisorRemainderSumAtSqrt n|
        ≤ A * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)

/-- Existential coefficient form of the `37 ≤ sqrt ≤ 100` finite-block
worker. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredAtSqrt A

/-- Remaining large-range worker after removing the `37 ≤ sqrt ≤ 100` block. -/
noncomputable def
    ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant :
    Prop :=
  ∃ A : ℝ,
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 100 A

/-- The `37 ≤ Nat.sqrt n ≤ 100` relative remainder worker is closed with the
explicit symbolic coefficient `37 * ((2^24)^2 * 2)`. -/
theorem residueRemainderRelativeSqrtThirtySevenToHundred_explicit :
    ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredAtSqrt
      sqrtThirtySevenToHundredRelativeCoefficient := by
  refine ⟨by unfold sqrtThirtySevenToHundredRelativeCoefficient
              sqrtThirtySevenToHundredRemainderBound; positivity, ?_⟩
  intro n hn hsqrt_ge_thirty_seven hsqrt_le_hundred
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_thirty_seven_to_hundred
      hn hsqrt_ge_thirty_seven hsqrt_le_hundred
  have hlocal_thirty_seventh :
      (1 / 37 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    exact
      one_thirty_seventh_le_goldbachResidueMainFactor_of_le_hundred
        n (Nat.sqrt n) hsqrt_le_hundred
  have hbound_nonneg : 0 ≤ sqrtThirtySevenToHundredRemainderBound := by
    unfold sqrtThirtySevenToHundredRemainderBound
    positivity
  have hscale :
      sqrtThirtySevenToHundredRemainderBound ≤
        sqrtThirtySevenToHundredRelativeCoefficient *
          residueDoubleDivisorLocalDensitySumAtSqrt n := by
    unfold sqrtThirtySevenToHundredRelativeCoefficient
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hmain :
      sqrtThirtySevenToHundredRemainderBound * (n : ℝ) ≤
        sqrtThirtySevenToHundredRelativeCoefficient *
          ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
    have hmul := mul_le_mul_of_nonneg_right hscale hn_nonneg
    calc
      sqrtThirtySevenToHundredRemainderBound * (n : ℝ)
          ≤
            (sqrtThirtySevenToHundredRelativeCoefficient *
              residueDoubleDivisorLocalDensitySumAtSqrt n) * (n : ℝ) := hmul
      _ =
          sqrtThirtySevenToHundredRelativeCoefficient *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) := by
        ring
  exact hrem.trans hmain

/-- Existential form of the closed `37 ≤ sqrt ≤ 100` block. -/
theorem residueRemainderRelativeSqrtThirtySevenToHundredWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredWithConstant :=
  ⟨sqrtThirtySevenToHundredRelativeCoefficient,
    residueRemainderRelativeSqrtThirtySevenToHundred_explicit⟩

/-- A closed `37 ≤ sqrt ≤ 100` block and a `sqrt ≥ 101` tail bound combine
into the Round 62 active `sqrt ≥ 37` target. -/
theorem residueRemainderAfterSqrtThirtySevenFixed_of_sqrtThirtySevenToHundred_and_afterSqrtHundredOne
    {Ablock AhundredOne : ℝ}
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredAtSqrt
        Ablock)
    (hHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 100
        AhundredOne) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThreshold 36
      (max Ablock AhundredOne) := by
  rcases hBlock with ⟨hAblock, hBlockBd⟩
  rcases hHundredOne with ⟨_hAhundredOne, hHundredOneBd⟩
  refine ⟨hAblock.trans (le_max_left Ablock AhundredOne), ?_⟩
  intro n hn hsqrt_ge_thirty_seven
  have hmain_nonneg :
      0 ≤ (n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (residueDoubleDivisorLocalDensitySumAtSqrt_nonneg n hn)
  by_cases hsqrt_le_hundred : Nat.sqrt n ≤ 100
  · have hbd := hBlockBd n hn hsqrt_ge_thirty_seven hsqrt_le_hundred
    have hscale :
        Ablock * ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AhundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_left Ablock AhundredOne)
        hmain_nonneg
    exact hbd.trans hscale
  · have hsqrt_ge_hundred_one : 100 + 1 ≤ Nat.sqrt n := by
      exact Nat.succ_le_iff.mpr (lt_of_not_ge hsqrt_le_hundred)
    have hbd := hHundredOneBd n hn hsqrt_ge_hundred_one
    have hscale :
        AhundredOne *
            ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n)
          ≤ max Ablock AhundredOne *
              ((n : ℝ) * residueDoubleDivisorLocalDensitySumAtSqrt n) :=
      mul_le_mul_of_nonneg_right (le_max_right Ablock AhundredOne)
        hmain_nonneg
    exact hbd.trans hscale

/-- Existential bridge from the two smaller workers to the Round 62 active
`sqrt ≥ 37` target. -/
theorem residueRemainderAfterSqrtThirtySeven_of_sqrtThirtySevenToHundred_and_afterSqrtHundredOne
    (hBlock :
      ResidueDoubleDivisorRemainderRelativeSqrtThirtySevenToHundredWithConstant)
    (hHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant := by
  rcases hBlock with ⟨Ablock, hAblock⟩
  rcases hHundredOne with ⟨AhundredOne, hAhundredOne⟩
  exact ⟨max Ablock AhundredOne,
    residueRemainderAfterSqrtThirtySevenFixed_of_sqrtThirtySevenToHundred_and_afterSqrtHundredOne
      hAblock hAhundredOne⟩

/-- Closing the `37 ≤ sqrt ≤ 100` block means only the `sqrt ≥ 101` tail
remains. -/
theorem residueRemainderAfterSqrtThirtySeven_of_afterSqrtHundredOne
    (hHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant) :
    ResidueDoubleDivisorRemainderRelativeAfterSqrtThirtySevenWithConstant :=
  residueRemainderAfterSqrtThirtySeven_of_sqrtThirtySevenToHundred_and_afterSqrtHundredOne
    residueRemainderRelativeSqrtThirtySevenToHundredWithConstant_closed
    hHundredOne

/-- Final Path C adapter after closing the `37 ≤ sqrt ≤ 100` block. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtHundredOne_and_countingInput
    (hHundredOne :
      ResidueDoubleDivisorRemainderRelativeAfterSqrtHundredOneWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderAfterSqrtThirtySeven_and_countingInput
    (residueRemainderAfterSqrtThirtySeven_of_afterSqrtHundredOne
      hHundredOne)
    hCounting

end PathCResidueRemainderSqrtThirtySevenToHundredPrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtThirtySevenToHundredPrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_bound_mul_n_of_sqrt_thirty_seven_to_hundred
#print axioms
  Gdbh.PathCResidueRemainderSqrtThirtySevenToHundredPrefix.residueRemainderRelativeSqrtThirtySevenToHundred_explicit
#print axioms
  Gdbh.PathCResidueRemainderSqrtThirtySevenToHundredPrefix.pathC_kGoldbach_of_remainderAfterSqrtHundredOne_and_countingInput
