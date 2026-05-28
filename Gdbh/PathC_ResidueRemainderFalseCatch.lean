/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueQuotientMainClosure
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Path C -- residue remainder false catch

Round 22 reduced the strict residue count route to the signed remainder target
`ResidueDoubleDivisorRemainderAtSqrtBound`.  This file records the smallest
explicit obstruction found during the next scout: at `n = 20`, the signed
double-divisor remainder is exactly `1 / 3`, while the canonical Bonferroni
tail is strictly smaller than `1 / 3`.

Therefore the proposed remainder target is not a valid worker Prop.  The next
route must either keep a positive small-`n` slack, change the error reservoir,
or avoid this signed-remainder split.
-/

namespace Gdbh
namespace PathCResidueRemainderFalseCatch

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (ResidueDoubleDivisorRemainderAtSqrtBound residueDoubleDivisorRemainderSum
   residueDoubleDivisorRemainderSumAtSqrt residuePairCountingRemainder
   residuePairQuotientMainTerm)
open Gdbh.PathCGoldbachResidues
  (goldbachResidueMainFactor goldbachResidueSiftedCount)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel)
open Gdbh.PathCResidueBonferroniKernelDecomposition
  (residueDivisibilityIndicatorSum goldbachResidueSiftedCount_eq_divisibilityIndicatorSum
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleSum)
open Gdbh.PathCResidueDoubleSumDecomposition
  (ResidueDoubleDivisorCanonicalAtSqrtBound
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor)

private lemma residuePrimeSet_four :
    residuePrimeSet 4 = ({3} : Finset ℕ) := by
  ext p
  simp only [residuePrimeSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h3, h4⟩, hp⟩
    interval_cases p
    · rfl
    · norm_num at hp
  · intro hp
    subst p
    constructor
    · constructor <;> norm_num
    · norm_num

private lemma residuePrimeSet_four_filter_forty :
    (residuePrimeSet 4).powerset.filter (fun d => d.card ≤ 40) =
      ({∅, {3}} : Finset (Finset ℕ)) := by
  rw [residuePrimeSet_four]
  decide

private lemma card_multiples_three_1_19 :
    ((Finset.Icc 1 19).filter (fun m => 3 ∣ m)).card = 6 := by
  have hset : (Finset.Icc 1 19).filter (fun m => 3 ∣ m) =
      ({3, 6, 9, 12, 15, 18} : Finset ℕ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h19⟩, hdiv⟩
      interval_cases m <;> simp_all
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
  rw [hset]
  norm_num

private lemma card_twenty_minus_m_multiples_three_1_19 :
    ((Finset.Icc 1 19).filter (fun m => 3 ∣ (20 - m))).card = 6 := by
  have hset : (Finset.Icc 1 19).filter (fun m => 3 ∣ (20 - m)) =
      ({2, 5, 8, 11, 14, 17} : Finset ℕ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h19⟩, hdiv⟩
      interval_cases m <;> simp_all
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
  rw [hset]
  norm_num

private lemma card_common_multiples_three_twenty_1_19 :
    ((Finset.Icc 1 19).filter
      (fun m => 3 ∣ m ∧ 3 ∣ (20 - m))).card = 0 := by
  have hset :
      (Finset.Icc 1 19).filter (fun m => 3 ∣ m ∧ 3 ∣ (20 - m)) =
        (∅ : Finset ℕ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h19⟩, hdiv⟩
      interval_cases m <;> simp_all
    · intro h
      simp at h
  rw [hset]
  norm_num

private lemma residuePairCountingRemainder_twenty_empty_empty :
    residuePairCountingRemainder 20 (∅ : Finset ℕ) (∅ : Finset ℕ) =
      (-1 : ℝ) := by
  unfold residuePairCountingRemainder residuePairQuotientMainTerm
  rw [show ((Finset.Icc 1 (20 - 1)).filter
      (fun m => ((∅ : Finset ℕ).prod id) ∣ m ∧
        ((∅ : Finset ℕ).prod id) ∣ (20 - m))).card = 19 by
        norm_num]
  norm_num

private lemma residuePairCountingRemainder_twenty_three_empty :
    residuePairCountingRemainder 20 ({3} : Finset ℕ) (∅ : Finset ℕ) =
      (-2 / 3 : ℝ) := by
  unfold residuePairCountingRemainder residuePairQuotientMainTerm
  rw [show ((Finset.Icc 1 (20 - 1)).filter
      (fun m => (({3} : Finset ℕ).prod id) ∣ m ∧
        ((∅ : Finset ℕ).prod id) ∣ (20 - m))).card = 6 by
        simpa using card_multiples_three_1_19]
  norm_num

private lemma residuePairCountingRemainder_twenty_empty_three :
    residuePairCountingRemainder 20 (∅ : Finset ℕ) ({3} : Finset ℕ) =
      (-2 / 3 : ℝ) := by
  unfold residuePairCountingRemainder residuePairQuotientMainTerm
  rw [show ((Finset.Icc 1 (20 - 1)).filter
      (fun m => ((∅ : Finset ℕ).prod id) ∣ m ∧
        (({3} : Finset ℕ).prod id) ∣ (20 - m))).card = 6 by
        simpa using card_twenty_minus_m_multiples_three_1_19]
  norm_num

private lemma residuePairCountingRemainder_twenty_three_three :
    residuePairCountingRemainder 20 ({3} : Finset ℕ) ({3} : Finset ℕ) =
      (0 : ℝ) := by
  unfold residuePairCountingRemainder residuePairQuotientMainTerm
  rw [show ((Finset.Icc 1 (20 - 1)).filter
      (fun m => (({3} : Finset ℕ).prod id) ∣ m ∧
        (({3} : Finset ℕ).prod id) ∣ (20 - m))).card = 0 by
        simpa using card_common_multiples_three_twenty_1_19]
  norm_num

/-- The signed remainder obstruction at `n = 20`. -/
theorem residueDoubleDivisorRemainderSumAtSqrt_twenty :
    residueDoubleDivisorRemainderSumAtSqrt 20 = (1 / 3 : ℝ) := by
  rw [show residueDoubleDivisorRemainderSumAtSqrt 20 =
      residueDoubleDivisorRemainderSum 20 4 40 by
    rw [residueDoubleDivisorRemainderSumAtSqrt]
    norm_num [canonicalK]]
  unfold residueDoubleDivisorRemainderSum
  rw [residuePrimeSet_four_filter_forty]
  have hmu3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  simp [residuePairCountingRemainder_twenty_empty_empty,
    residuePairCountingRemainder_twenty_three_empty,
    residuePairCountingRemainder_twenty_empty_three,
    residuePairCountingRemainder_twenty_three_three,
    hmu3]
  norm_num

/-- The canonical Bonferroni tail at `n = 20` is too small to absorb the
positive signed remainder. -/
theorem residueBonferroniTailAtSqrt_twenty_lt_third :
    residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) < (1 / 3 : ℝ) := by
  have hsqrt : Nat.sqrt 20 = 4 := by norm_num
  have hpi4 : Nat.primeCounting 4 = 2 := by decide
  have htail_eq :
      residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) =
        (20 : ℝ) * (2 : ℝ)^81 / ((81).factorial : ℝ) := by
    rw [hsqrt]
    simp [residueBonferroniTailAtSqrt, canonicalK, hpi4]
  have hnat : 60 * 2 ^ 81 < Nat.factorial 81 := by decide
  have hreal : (60 : ℝ) * (2 : ℝ)^81 < (Nat.factorial 81 : ℝ) := by
    exact_mod_cast hnat
  rw [htail_eq]
  have hfact_pos : (0 : ℝ) < (Nat.factorial 81 : ℝ) := by positivity
  rw [div_lt_iff₀ hfact_pos]
  nlinarith

/-- The Round 22 signed-remainder target is refuted by `n = 20`. -/
theorem not_residueDoubleDivisorRemainderAtSqrtBound :
    ¬ ResidueDoubleDivisorRemainderAtSqrtBound := by
  intro h
  have h20 := h 20 (by norm_num : 16 ≤ 20)
  rw [residueDoubleDivisorRemainderSumAtSqrt_twenty] at h20
  have htail := residueBonferroniTailAtSqrt_twenty_lt_third
  linarith

/-- At the same obstruction point, the residue main factor is exactly `1 / 3`. -/
theorem goldbachResidueMainFactor_twenty_four :
    goldbachResidueMainFactor 20 4 = (1 / 3 : ℝ) := by
  have hP : (Finset.Icc 3 4).filter Nat.Prime = ({3} : Finset ℕ) := by
    simpa [residuePrimeSet] using residuePrimeSet_four
  unfold goldbachResidueMainFactor
  rw [hP]
  simp [Gdbh.PathCGoldbachResidues.goldbachBadResidueSet_card,
    Gdbh.PathCGoldbachLocalFactor.goldbachBadResidueCard]
  norm_num

private lemma residueDivisibilityIndicatorSum_twenty_four :
    residueDivisibilityIndicatorSum 20 4 = (7 : ℝ) := by
  unfold residueDivisibilityIndicatorSum
  simp only [residuePrimeSet_four]
  have hset : (Finset.Icc 1 (20 - 1)).filter
      (fun m => (∀ p ∈ ({3} : Finset ℕ), ¬p ∣ m) ∧
        ∀ p ∈ ({3} : Finset ℕ), ¬p ∣ 20 - m) =
      ({1, 4, 7, 10, 13, 16, 19} : Finset ℕ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h19⟩, hdiv⟩
      interval_cases m <;> simp_all
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
  rw [show (∑ m ∈ Finset.Icc 1 (20 - 1),
      (if (∀ p ∈ ({3} : Finset ℕ), ¬p ∣ m) ∧
        (∀ p ∈ ({3} : Finset ℕ), ¬p ∣ 20 - m) then (1 : ℝ) else 0)) =
      ∑ m ∈ (Finset.Icc 1 (20 - 1)).filter
        (fun m => (∀ p ∈ ({3} : Finset ℕ), ¬p ∣ m) ∧
          ∀ p ∈ ({3} : Finset ℕ), ¬p ∣ 20 - m), (1 : ℝ) by
    rw [Finset.sum_filter]]
  rw [hset]
  norm_num

/-- The residue-sifted count at `n = 20`, `z = 4` is exactly seven. -/
theorem goldbachResidueSiftedCount_twenty_four :
    (goldbachResidueSiftedCount 20 4 : ℝ) = 7 := by
  rw [goldbachResidueSiftedCount_eq_divisibilityIndicatorSum]
  exact residueDivisibilityIndicatorSum_twenty_four

/-- The strict canonical residue kernel is also refuted at `n = 20`. -/
theorem not_brunGoldbachResidueSiftedAtSqrtCanonicalKernel :
    ¬ BrunGoldbachResidueSiftedAtSqrtCanonicalKernel := by
  intro h
  have h20 := h 20 (by norm_num : 16 ≤ 20)
  have hsqrt : Nat.sqrt 20 = 4 := by norm_num
  have h20' :
      (goldbachResidueSiftedCount 20 4 : ℝ)
        ≤ (20 : ℝ) * goldbachResidueMainFactor 20 4 +
          residueBonferroniTailAtSqrt 20 (Nat.sqrt 20) := by
    simpa [hsqrt] using h20
  rw [goldbachResidueSiftedCount_twenty_four,
    goldbachResidueMainFactor_twenty_four] at h20'
  have htail := residueBonferroniTailAtSqrt_twenty_lt_third
  linarith

/-- Consequently, the explicit double-divisor canonical target cannot be the
right repair target either, since it implies the strict canonical kernel. -/
theorem not_residueDoubleDivisorCanonicalAtSqrtBound :
    ¬ ResidueDoubleDivisorCanonicalAtSqrtBound := by
  intro h
  exact not_brunGoldbachResidueSiftedAtSqrtCanonicalKernel
    (brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor h)

end PathCResidueRemainderFalseCatch
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.residueDoubleDivisorRemainderSumAtSqrt_twenty
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.residueBonferroniTailAtSqrt_twenty_lt_third
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.not_residueDoubleDivisorRemainderAtSqrtBound
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.goldbachResidueMainFactor_twenty_four
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.goldbachResidueSiftedCount_twenty_four
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.not_brunGoldbachResidueSiftedAtSqrtCanonicalKernel
#print axioms
  Gdbh.PathCResidueRemainderFalseCatch.not_residueDoubleDivisorCanonicalAtSqrtBound
