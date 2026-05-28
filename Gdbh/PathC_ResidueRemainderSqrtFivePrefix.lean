/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderSqrtFiveSplit
import Gdbh.PathC_ResidueCanonicalSqrtFiveSplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- relative remainder finite prefix at sqrt five

Round 56 isolated the finite `Nat.sqrt n = 5` prefix.  This file closes that
prefix with a deliberately crude but uniform bound: the four subset divisors
`1, 3, 5, 15` give sixteen CRT-pair remainder terms, each bounded by `2n` in
absolute value.  The already closed local-density Euler chain and the `z = 5`
factor lower bound absorb the resulting `32n` error with coefficient `160`.

The remaining residue-side worker begins at `6 ≤ Nat.sqrt n`.
-/

namespace Gdbh
namespace PathCResidueRemainderSqrtFivePrefix

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorDensityDecomposition
  (residueDoubleDivisorLocalDensitySumAtSqrt)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSum residueDoubleDivisorRemainderSumAtSqrt
   residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderSqrtFiveSplit
  (ResidueDoubleDivisorRemainderRelativeSqrtFiveAtSqrt
   ResidueDoubleDivisorRemainderRelativeSqrtFiveWithConstant
   ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant
   pathC_kGoldbach_of_remainderSqrtFive_and_afterSqrtSix)
open Gdbh.PathCResidueCanonicalSqrtFiveSplit
  (one_fifth_le_goldbachResidueMainFactor_at_five)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

private def sqrtFiveDivisorPowerset : Finset (Finset ℕ) :=
  ({∅, {3}, {5}, {3, 5}} : Finset (Finset ℕ))

private lemma sqrtFiveDivisorPowerset_card :
    sqrtFiveDivisorPowerset.card = 4 := by
  decide

private lemma sqrtFiveDivisorPowerset_prod_pos {d : Finset ℕ}
    (hd : d ∈ sqrtFiveDivisorPowerset) :
    0 < d.prod id := by
  unfold sqrtFiveDivisorPowerset at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> norm_num

private lemma residuePrimeSet_five :
    residuePrimeSet 5 = ({3, 5} : Finset ℕ) := by
  ext p
  simp only [residuePrimeSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp3, hp5⟩, hpprime⟩
    interval_cases p <;> simp at hpprime ⊢
    norm_num at hpprime
  · intro hp
    rcases hp with rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

private lemma pair_powerset_filter_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ({3, 5} : Finset ℕ).powerset.filter (fun d => d.card ≤ k) =
      sqrtFiveDivisorPowerset := by
  unfold sqrtFiveDivisorPowerset
  rw [Finset.filter_true_of_mem]
  · decide
  · intro d hd
    have hsub : d ⊆ ({3, 5} : Finset ℕ) := by
      simpa using hd
    have hcard : d.card ≤ 2 := by
      have hcard' := Finset.card_le_card hsub
      simpa using hcard'
    exact le_trans hcard hk

private lemma residuePrimeSet_five_filter_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    (residuePrimeSet 5).powerset.filter (fun d => d.card ≤ k) =
      sqrtFiveDivisorPowerset := by
  rw [residuePrimeSet_five]
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

private lemma residueRemainderSqrtFiveTerm_abs_le_two_n
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ sqrtFiveDivisorPowerset)
    (hd2 : d2 ∈ sqrtFiveDivisorPowerset) :
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
    (sqrtFiveDivisorPowerset_prod_pos hd1)
    (sqrtFiveDivisorPowerset_prod_pos hd2)
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

/-- On the `Nat.sqrt n = 5` prefix, the full signed CRT remainder is bounded
by `32n`; this is deliberately coarse but avoids a brittle sixteen-entry
table. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_five
    {n : ℕ} (hn : 16 ≤ n) (hsqrt : Nat.sqrt n = 5) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤ (32 * n : ℝ) := by
  rw [show residueDoubleDivisorRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSum n 5 (canonicalK n) by
    simp [residueDoubleDivisorRemainderSumAtSqrt, hsqrt]]
  unfold residueDoubleDivisorRemainderSum
  rw [residuePrimeSet_five_filter_of_two_le
    (by unfold canonicalK; omega : 2 ≤ canonicalK n)]
  calc
    |∑ d1 ∈ sqrtFiveDivisorPowerset, ∑ d2 ∈ sqrtFiveDivisorPowerset,
        (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
          (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
          residuePairCountingRemainder n d1 d2|
        ≤ ∑ d1 ∈ sqrtFiveDivisorPowerset,
            |∑ d2 ∈ sqrtFiveDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2| :=
          Finset.abs_sum_le_sum_abs
            (fun d1 => ∑ d2 ∈ sqrtFiveDivisorPowerset,
              (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
                (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
                residuePairCountingRemainder n d1 d2)
            sqrtFiveDivisorPowerset
    _ ≤ ∑ d1 ∈ sqrtFiveDivisorPowerset, ∑ d2 ∈ sqrtFiveDivisorPowerset,
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
            sqrtFiveDivisorPowerset
    _ ≤ ∑ _d1 ∈ sqrtFiveDivisorPowerset, ∑ _d2 ∈ sqrtFiveDivisorPowerset,
          (2 * n : ℝ) := by
          apply Finset.sum_le_sum
          intro d1 hd1
          apply Finset.sum_le_sum
          intro d2 hd2
          exact residueRemainderSqrtFiveTerm_abs_le_two_n n hd1 hd2
    _ = (32 * n : ℝ) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [sqrtFiveDivisorPowerset_card]
          ring

/-- The `Nat.sqrt n = 5` relative remainder worker is closed with coefficient
`160`. -/
theorem residueRemainderRelativeSqrtFive_one_sixty :
    ResidueDoubleDivisorRemainderRelativeSqrtFiveAtSqrt 160 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn hsqrt
  have hrem :=
    residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_five
      hn hsqrt
  have hlocal_fifth :
      (1 / 5 : ℝ) ≤ residueDoubleDivisorLocalDensitySumAtSqrt n := by
    rw [
      Gdbh.PathCResidueFullLocalDensityClosure.residueDoubleDivisorLocalDensityEulerAtSqrt
        n hn]
    simpa [hsqrt] using one_fifth_le_goldbachResidueMainFactor_at_five n
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

/-- Existential form of the closed `sqrt = 5` prefix. -/
theorem residueRemainderRelativeSqrtFiveWithConstant_closed :
    ResidueDoubleDivisorRemainderRelativeSqrtFiveWithConstant :=
  ⟨160, residueRemainderRelativeSqrtFive_one_sixty⟩

/-- Final Path C adapter after closing the `sqrt = 5` prefix: only the
`sqrt ≥ 6` relative remainder tail remains on this branch. -/
theorem pathC_kGoldbach_of_remainderAfterSqrtSix_and_countingInput
    (hSix : ResidueDoubleDivisorRemainderRelativeAfterSqrtSixWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderSqrtFive_and_afterSqrtSix
    residueRemainderRelativeSqrtFiveWithConstant_closed hSix hCounting

end PathCResidueRemainderSqrtFivePrefix
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderSqrtFivePrefix.residueDoubleDivisorRemainderSumAtSqrt_abs_le_thirty_two_mul_n_of_sqrt_five
#print axioms
  Gdbh.PathCResidueRemainderSqrtFivePrefix.residueRemainderRelativeSqrtFive_one_sixty
#print axioms
  Gdbh.PathCResidueRemainderSqrtFivePrefix.pathC_kGoldbach_of_remainderAfterSqrtSix_and_countingInput
