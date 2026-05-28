/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderThresholdSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- cardinal envelope for residue remainder blocks

This file isolates the finite cardinal argument used by the residue remainder
prefix closures.  If the residue prime set at `Nat.sqrt n` has at most `M`
members, then the double divisor family has at most `2^M * 2^M` pairs and each
pairwise CRT remainder is bounded by `2n`.

The result is intentionally crude but honest; finite block files can supply
their own verified prime-set cardinal bound and then absorb this envelope into
the local-density lower bound available for that block.
-/

namespace Gdbh
namespace PathCResidueRemainderCardinalityEnvelope

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSum residueDoubleDivisorRemainderSumAtSqrt
   residuePairCountingRemainder residuePairQuotientMainTerm)

/-- Cardinal envelope multiplier for a residue prime family of size at most
`M`: `(2^M)^2 * 2`. -/
noncomputable def residueRemainderCardinalityEnvelope (M : ℕ) : ℝ :=
  ((2 : ℝ) ^ M * (2 : ℝ) ^ M) * 2

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

private lemma filteredResiduePowerset_card_le_two_pow_of_card_le
    {z k M : ℕ}
    (hcard : (residuePrimeSet z).card ≤ M) :
    ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
      2 ^ M := by
  have hfilter_card :
      ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
        (residuePrimeSet z).powerset.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hpow : 2 ^ (residuePrimeSet z).card ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard
  have hpowerset : (residuePrimeSet z).powerset.card ≤ 2 ^ M := by
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

/-- Cardinal-envelope bound for the full signed CRT remainder. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
    {n M : ℕ}
    (hcard : (residuePrimeSet (Nat.sqrt n)).card ≤ M) :
    |residueDoubleDivisorRemainderSumAtSqrt n| ≤
      residueRemainderCardinalityEnvelope M * (n : ℝ) := by
  let F : Finset (Finset ℕ) :=
    (residuePrimeSet (Nat.sqrt n)).powerset.filter
      (fun d => d.card ≤ canonicalK n)
  have hFcard_nat : F.card ≤ 2 ^ M := by
    dsimp [F]
    exact filteredResiduePowerset_card_le_two_pow_of_card_le hcard
  have hFcard_real : (F.card : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hFcard_nat
  have hFcard_nonneg : 0 ≤ (F.card : ℝ) := by
    positivity
  have hFcard_sq :
      (F.card : ℝ) * (F.card : ℝ) ≤
        (2 : ℝ) ^ M * (2 : ℝ) ^ M := by
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
      residueRemainderCardinalityEnvelope M * (n : ℝ)
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
    _ ≤ residueRemainderCardinalityEnvelope M * (n : ℝ) := by
          have hn_nonneg : 0 ≤ (2 * n : ℝ) := by
            positivity
          have hmul :=
            mul_le_mul_of_nonneg_right hFcard_sq hn_nonneg
          calc
            (F.card : ℝ) * ((F.card : ℝ) * (2 * n : ℝ))
                = ((F.card : ℝ) * (F.card : ℝ)) * (2 * n : ℝ) := by
                  ring
            _ ≤ ((2 : ℝ) ^ M * (2 : ℝ) ^ M) * (2 * n : ℝ) := hmul
            _ = residueRemainderCardinalityEnvelope M * (n : ℝ) := by
              unfold residueRemainderCardinalityEnvelope
              ring

end PathCResidueRemainderCardinalityEnvelope
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderCardinalityEnvelope.residueDoubleDivisorRemainderSumAtSqrt_abs_le_cardinalityEnvelope
