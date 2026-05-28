/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFiltered
import Gdbh.PathC_ResidueRemainderCardinalityEnvelope
import Mathlib.Tactic.Ring

/-!
# Path C -- cardinal envelope for the filtered witness cover

Round 83 isolates a crude but honest finite envelope for the Round82 filtered
cover.  If the residue-prime set has at most `M` elements, then the outer
witness-prime set has at most `M` elements and each filtered divisor family
has at most `2^M` elements.  Each pair remainder is bounded by `2n`.

This file is a finite cardinality bound only.  It does not assert the analytic
log-squared estimate.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredEnvelope

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderIntersectionSplit
  (residueSharedPrimeIntersectionPairCountingRemainder)
open Gdbh.PathCResidueRemainderWitnessDivisorPartition
  (residuePrimeDivisorWitnessSet residuePrimeDivisorWitnessSet_subset)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
   residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt
   residueWitnessContainingDivisorFamily)

/-! ## Cardinal support facts -/

/-- Cardinal envelope multiplier for a filtered witness-prime cover with
residue-prime set cardinal at most `M`: `M * (2^M)^2 * 2`. -/
noncomputable def residueFilteredCoverCardinalityEnvelope (M : ℕ) : ℝ :=
  ((M : ℝ) * ((2 : ℝ)^M * (2 : ℝ)^M)) * 2

/-- The filtered divisor family is bounded by the full cardinal-cutoff
powerset family. -/
theorem residueWitnessContainingDivisorFamily_card_le_base
    (z k p : ℕ) :
    (residueWitnessContainingDivisorFamily z k p).card ≤
      ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card := by
  unfold residueWitnessContainingDivisorFamily
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- If the residue-prime set has at most `M` elements, then each filtered
divisor family has at most `2^M` elements. -/
theorem residueWitnessContainingDivisorFamily_card_le_two_pow_of_card_le
    {z k p M : ℕ}
    (hcard : (residuePrimeSet z).card ≤ M) :
    (residueWitnessContainingDivisorFamily z k p).card ≤ 2 ^ M := by
  have hbase :
      ((residuePrimeSet z).powerset.filter (fun d => d.card ≤ k)).card ≤
        (residuePrimeSet z).powerset.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hpowerset :
      (residuePrimeSet z).powerset.card ≤ 2 ^ M := by
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard
  exact le_trans
    (residueWitnessContainingDivisorFamily_card_le_base z k p)
    (le_trans hbase hpowerset)

/-- The divisor-witness prime set has cardinal bounded by the residue-prime
set cardinal bound. -/
theorem residuePrimeDivisorWitnessSet_card_le_of_residuePrimeSet_card_le
    {n z M : ℕ}
    (hcard : (residuePrimeSet z).card ≤ M) :
    (residuePrimeDivisorWitnessSet n z).card ≤ M :=
  le_trans
    (Finset.card_le_card (residuePrimeDivisorWitnessSet_subset n z))
    hcard

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

private lemma residueDivisorProd_pos_of_mem_family {z k p : ℕ}
    {d : Finset ℕ}
    (hd : d ∈ residueWitnessContainingDivisorFamily z k p) :
    0 < d.prod id := by
  have hbase :
      d ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k) := by
    unfold residueWitnessContainingDivisorFamily at hd
    exact (Finset.mem_filter.mp hd).1
  exact residueDivisorProd_pos_of_mem_filter hbase

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
    · exact div_le_self hn_nonneg hlcm_one
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

private lemma
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_two_n_of_pos
    (n : ℕ) {d1 d2 : Finset ℕ}
    (hd1pos : 0 < d1.prod id) (hd2pos : 0 < d2.prod id) :
    |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| ≤
      (2 * n : ℝ) := by
  unfold residueSharedPrimeIntersectionPairCountingRemainder
  by_cases hinter : d1 ∩ d2 = ∅
  · rw [if_pos hinter, abs_zero]
    positivity
  · by_cases hdiv : (d1 ∩ d2).prod id ∣ n
    · rw [if_neg hinter, if_pos hdiv]
      exact residuePairCountingRemainder_abs_le_two_n_of_pos n hd1pos hd2pos
    · rw [if_neg hinter, if_neg hdiv, abs_zero]
      positivity

private lemma residueFilteredCoverTerm_le_two_n_of_mem_family
    (n z k p : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ residueWitnessContainingDivisorFamily z k p)
    (hd2 : d2 ∈ residueWitnessContainingDivisorFamily z k p) :
    |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| ≤
      (2 * n : ℝ) := by
  rw [abs_mul]
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
  have hrem :=
    residueSharedPrimeIntersectionPairCountingRemainder_abs_le_two_n_of_pos n
      (residueDivisorProd_pos_of_mem_family hd1)
      (residueDivisorProd_pos_of_mem_family hd2)
  have hrem_nonneg :
      0 ≤ |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| :=
    abs_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hmu_prod hrem_nonneg
  calc
    |((ArithmeticFunction.moebius (d1.prod id) : ℤ) : ℝ)| *
        |((ArithmeticFunction.moebius (d2.prod id) : ℤ) : ℝ)| *
        |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        ≤ (1 : ℝ) *
            |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2| := by
          simpa [mul_assoc] using hmul
    _ ≤ (2 * n : ℝ) := by simpa using hrem

/-! ## Filtered cover envelope -/

/-- Crude cardinal-envelope bound for the filtered witness-prime cover. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum_le_cardinalityEnvelope
    {n z k M : ℕ}
    (hcard : (residuePrimeSet z).card ≤ M) :
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum n z k ≤
      residueFilteredCoverCardinalityEnvelope M * (n : ℝ) := by
  classical
  let W : Finset ℕ := residuePrimeDivisorWitnessSet n z
  let Fp : ℕ → Finset (Finset ℕ) :=
    fun p => residueWitnessContainingDivisorFamily z k p
  have hWcard_nat : W.card ≤ M := by
    dsimp [W]
    exact residuePrimeDivisorWitnessSet_card_le_of_residuePrimeSet_card_le hcard
  have hWcard_real : (W.card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hWcard_nat
  have hFp_card_nat : ∀ p : ℕ, (Fp p).card ≤ 2 ^ M := by
    intro p
    dsimp [Fp]
    exact residueWitnessContainingDivisorFamily_card_le_two_pow_of_card_le
      (z := z) (k := k) (p := p) hcard
  have htwo_n_nonneg : 0 ≤ (2 * n : ℝ) := by
    positivity
  have htwo_pow_nonneg : 0 ≤ (2 : ℝ)^M := by
    positivity
  unfold residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum
    residueFilteredCoverCardinalityEnvelope
  change
    ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
      ≤ (((M : ℝ) * ((2 : ℝ)^M * (2 : ℝ)^M)) * 2) * (n : ℝ)
  calc
    ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p,
      |(ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ)| *
        |residueSharedPrimeIntersectionPairCountingRemainder n d1 d2|
        ≤ ∑ p ∈ W, ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p, (2 * n : ℝ) := by
          apply Finset.sum_le_sum
          intro p _hp
          apply Finset.sum_le_sum
          intro d1 hd1
          apply Finset.sum_le_sum
          intro d2 hd2
          exact residueFilteredCoverTerm_le_two_n_of_mem_family n z k p
            hd1 hd2
    _ ≤ ∑ p ∈ W,
          (2 : ℝ)^M * ((2 : ℝ)^M * (2 * n : ℝ)) := by
          apply Finset.sum_le_sum
          intro p _hp
          have hFp_real : ((Fp p).card : ℝ) ≤ (2 : ℝ)^M := by
            exact_mod_cast hFp_card_nat p
          have hFp_nonneg : 0 ≤ ((Fp p).card : ℝ) := by
            positivity
          have hcard_sq :
              ((Fp p).card : ℝ) * ((Fp p).card : ℝ) ≤
                (2 : ℝ)^M * (2 : ℝ)^M :=
            mul_le_mul hFp_real hFp_real hFp_nonneg htwo_pow_nonneg
          have hmul := mul_le_mul_of_nonneg_right hcard_sq htwo_n_nonneg
          calc
            ∑ d1 ∈ Fp p, ∑ d2 ∈ Fp p, (2 * n : ℝ)
                = ((Fp p).card : ℝ) *
                    (((Fp p).card : ℝ) * (2 * n : ℝ)) := by
                  rw [Finset.sum_const, Finset.sum_const]
                  simp [nsmul_eq_mul]
            _ = (((Fp p).card : ℝ) * ((Fp p).card : ℝ)) *
                    (2 * n : ℝ) := by ring
            _ ≤ ((2 : ℝ)^M * (2 : ℝ)^M) * (2 * n : ℝ) := hmul
            _ = (2 : ℝ)^M * ((2 : ℝ)^M * (2 * n : ℝ)) := by ring
    _ = (W.card : ℝ) *
          ((2 : ℝ)^M * ((2 : ℝ)^M * (2 * n : ℝ))) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    _ ≤ (M : ℝ) * ((2 : ℝ)^M * ((2 : ℝ)^M * (2 * n : ℝ))) := by
          have hconst_nonneg :
              0 ≤ (2 : ℝ)^M * ((2 : ℝ)^M * (2 * n : ℝ)) := by
            positivity
          exact mul_le_mul_of_nonneg_right hWcard_real hconst_nonneg
    _ = (((M : ℝ) * ((2 : ℝ)^M * (2 : ℝ)^M)) * 2) * (n : ℝ) := by
          ring

/-- At-sqrt version of the filtered cover cardinal-envelope bound. -/
theorem
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_cardinalityEnvelope
    {n M : ℕ}
    (hcard : (residuePrimeSet (Nat.sqrt n)).card ≤ M) :
    residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt n ≤
      residueFilteredCoverCardinalityEnvelope M * (n : ℝ) := by
  simpa [residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt]
    using
      residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum_le_cardinalityEnvelope
        (n := n) (z := Nat.sqrt n) (k := canonicalK n) (M := M) hcard

end PathCResidueRemainderWitnessCoverFilteredEnvelope
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelope.residueWitnessContainingDivisorFamily_card_le_two_pow_of_card_le
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelope.residuePrimeDivisorWitnessSet_card_le_of_residuePrimeSet_card_le
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelope.residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSum_le_cardinalityEnvelope
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredEnvelope.residueDoubleDivisorSharedPrimeDivisorWitnessFilteredCoverSumAtSqrt_le_cardinalityEnvelope
