/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderWitnessCoverFilteredTermwise
import Mathlib.Tactic

/-!
# Path C -- pair-counting interval envelope

Round 89 isolates the raw interval-counting remainder underneath the
filtered-cover termwise input.  The new D-level envelope has no finite-set
residue support in its statement; the filtered-cover bridge supplies
positivity of the divisor products from the residue-prime family.

This file also exposes the existing honest crude bound `|remainder| <= 2n`
as a public baseline.  It does not claim the filtered-cover log-squared tail
and it leaves the sharper CRT `O(1)` interval discrepancy as a named residual.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResiduePairCountingIntervalEnvelope

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (residueWitnessContainingDivisorFamily)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise
  (ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter)

/-! ## D-level pair remainder -/

/-- D-level form of the pair-counting remainder. -/
noncomputable def residuePairDivisorCountingRemainder
    (n D1 D2 : ℕ) : ℝ :=
  (((Finset.Icc 1 (n - 1)).filter
      (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
    - residuePairQuotientMainTerm n D1 D2

@[simp]
theorem residuePairCountingRemainder_eq_divisorCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) :
    residuePairCountingRemainder n d1 d2 =
      residuePairDivisorCountingRemainder n (d1.prod id) (d2.prod id) := rfl

/-- Large-range D-level interval envelope. -/
noncomputable def ResiduePairDivisorIntervalEnvelopeAfter
    (N : ℕ) (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
    0 ≤ R n ∧
      ∀ D1 D2 : ℕ, 0 < D1 → 0 < D2 →
        |residuePairDivisorCountingRemainder n D1 D2| ≤ R n

/-- Sharper uniform interval discrepancy residual.  A future CRT closure with
`B = 2` would provide the desired O(1) pair-level envelope. -/
noncomputable def ResiduePairDivisorSharpIntervalEnvelope (B : ℝ) : Prop :=
  0 ≤ B ∧
    ∀ n D1 D2 : ℕ, 0 < D1 → 0 < D2 →
      |residuePairDivisorCountingRemainder n D1 D2| ≤ B

/-! ## Product positivity from residue support -/

/-- Products of residue-prime divisor supports are positive. -/
theorem residueDivisorProd_pos_of_mem_residuePowerset
    {z k : ℕ} {d : Finset ℕ}
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

/-- Products of filtered witness-family divisor supports are positive. -/
theorem residueDivisorProd_pos_of_mem_witnessFamily
    {z k p : ℕ} {d : Finset ℕ}
    (hd : d ∈ residueWitnessContainingDivisorFamily z k p) :
    0 < d.prod id := by
  have hbase :
      d ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k) := by
    unfold residueWitnessContainingDivisorFamily at hd
    exact (Finset.mem_filter.mp hd).1
  exact residueDivisorProd_pos_of_mem_residuePowerset hbase

/-! ## Crude interval envelope -/

/-- Any filtered subinterval of `Icc 1 (n - 1)` has at most `n` elements. -/
theorem filtered_interval_card_le_n
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

/-- The quotient main term is nonnegative and at most `n` for positive
divisors. -/
theorem residuePairQuotientMainTerm_nonneg_le_n
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

/-- Crude but unconditional D-level interval envelope. -/
theorem residuePairDivisorCountingRemainder_abs_le_two_n_of_pos
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2) :
    |residuePairDivisorCountingRemainder n D1 D2| ≤ (2 * n : ℝ) := by
  unfold residuePairDivisorCountingRemainder
  let c : ℝ := (((Finset.Icc 1 (n - 1)).filter
    (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
  let q : ℝ := residuePairQuotientMainTerm n D1 D2
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_le : c ≤ (n : ℝ) := by
    dsimp [c]
    exact filtered_interval_card_le_n n _
  have hq_bounds := residuePairQuotientMainTerm_nonneg_le_n n D1 D2 hD1 hD2
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

/-- Crude pair-counting envelope for filtered witness-family terms. -/
theorem residuePairCountingRemainder_abs_le_two_n_of_mem_family
    (n z k p : ℕ) {d1 d2 : Finset ℕ}
    (hd1 : d1 ∈ residueWitnessContainingDivisorFamily z k p)
    (hd2 : d2 ∈ residueWitnessContainingDivisorFamily z k p) :
    |residuePairCountingRemainder n d1 d2| ≤ (2 * n : ℝ) := by
  simpa using
    residuePairDivisorCountingRemainder_abs_le_two_n_of_pos n
      (d1.prod id) (d2.prod id)
      (residueDivisorProd_pos_of_mem_witnessFamily hd1)
      (residueDivisorProd_pos_of_mem_witnessFamily hd2)

/-- The crude D-level bound supplies a large-range interval envelope with
`R n = 2n`. -/
theorem residuePairDivisorIntervalEnvelopeAfter_two_n
    (N : ℕ) :
    ResiduePairDivisorIntervalEnvelopeAfter N (fun n => (2 * n : ℝ)) := by
  intro n _hn _hsqrt
  refine ⟨by positivity, ?_⟩
  intro D1 D2 hD1 hD2
  exact residuePairDivisorCountingRemainder_abs_le_two_n_of_pos n D1 D2 hD1 hD2

/-- A sharp D-level interval discrepancy supplies the large-range envelope. -/
theorem residuePairDivisorIntervalEnvelopeAfter_of_sharp
    (N : ℕ) {B : ℝ}
    (hSharp : ResiduePairDivisorSharpIntervalEnvelope B) :
    ResiduePairDivisorIntervalEnvelopeAfter N (fun _ => B) := by
  rcases hSharp with ⟨hB, hbd⟩
  intro n _hn _hsqrt
  exact ⟨hB, hbd n⟩

/-! ## Bridge to the Round88 termwise envelope -/

/-- A D-level interval envelope implies the Round88 raw pair envelope on the
filtered witness cover. -/
theorem
    residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_of_divisorIntervalEnvelope
    {N : ℕ} {R : ℕ → ℝ}
    (hDiv : ResiduePairDivisorIntervalEnvelopeAfter N R) :
    ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter N R := by
  intro n hn hsqrt
  rcases hDiv n hn hsqrt with ⟨hR, hbd⟩
  refine ⟨hR, ?_⟩
  intro p _hp d1 hd1 d2 hd2
  simpa using
    hbd (d1.prod id) (d2.prod id)
      (residueDivisorProd_pos_of_mem_witnessFamily hd1)
      (residueDivisorProd_pos_of_mem_witnessFamily hd2)

/-- Public baseline: the filtered-cover raw pair envelope holds with
`R n = 2n`. -/
theorem residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two_n
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter
      N (fun n => (2 * n : ℝ)) :=
  residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_of_divisorIntervalEnvelope
    (residuePairDivisorIntervalEnvelopeAfter_two_n N)

end PathCResiduePairCountingIntervalEnvelope
end Gdbh

#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairCountingRemainder_eq_divisorCountingRemainder
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairDivisorCountingRemainder_abs_le_two_n_of_pos
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairCountingRemainder_abs_le_two_n_of_mem_family
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairDivisorIntervalEnvelopeAfter_two_n
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairDivisorIntervalEnvelopeAfter_of_sharp
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_of_divisorIntervalEnvelope
#print axioms
  Gdbh.PathCResiduePairCountingIntervalEnvelope.residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two_n
