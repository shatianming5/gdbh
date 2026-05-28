/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueRemainderMainFactorMertensLower

/-!
# Path C -- compatible support for the residue remainder

Round 73 left the signed double-divisor CRT remainder upper estimate as the
active large-tail worker.  This file removes an algebraic distraction from
that target: pairs with incompatible overlap, namely
`¬ Nat.gcd (d1.prod id) (d2.prod id) ∣ n`, contribute zero to the signed
counting remainder.

The remaining worker is therefore the same log-squared upper estimate, but
for the compatible-support sum only.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderCompatibleSupport

open scoped BigOperators

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residueDoubleDivisorRemainderSum residueDoubleDivisorRemainderSumAtSqrt
   residuePairCountingRemainder residuePairQuotientMainTerm)
open Gdbh.PathCResidueRemainderAnalyticTailReduction
  (ResidueRemainderLogSquaredUpperAfter)
open Gdbh.PathCResidueRemainderMainFactorMertensLower
  (ResidueRemainderLogSquaredUpperEventually
   pathC_kGoldbach_of_remainderLogSquaredUpperEventually_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Pairwise incompatible support vanishing -/

/-- If the two divisor products have an overlap obstruction not dividing `n`,
then the interval count in the pair remainder is empty, and the quotient main
term is also zero. -/
theorem residuePairCountingRemainder_eq_zero_of_not_gcd_dvd
    (n : ℕ) (d1 d2 : Finset ℕ)
    (hnot : ¬ Nat.gcd (d1.prod id) (d2.prod id) ∣ n) :
    residuePairCountingRemainder n d1 d2 = 0 := by
  unfold residuePairCountingRemainder residuePairQuotientMainTerm
  have hcard_zero :
      ((Finset.Icc 1 (n - 1)).filter
        (fun m => (d1.prod id) ∣ m ∧ (d2.prod id) ∣ (n - m))).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro m hm hcond
    obtain ⟨_hm_ge, _hm_le_pred⟩ := Finset.mem_Icc.mp hm
    have hm_le_n : m ≤ n := by omega
    obtain ⟨hD1m, hD2nm⟩ := hcond
    have hg_m : Nat.gcd (d1.prod id) (d2.prod id) ∣ m :=
      Nat.dvd_trans (Nat.gcd_dvd_left _ _) hD1m
    have hg_nm : Nat.gcd (d1.prod id) (d2.prod id) ∣ n - m :=
      Nat.dvd_trans (Nat.gcd_dvd_right _ _) hD2nm
    have hsum : (n - m) + m = n := Nat.sub_add_cancel hm_le_n
    have hg_n : Nat.gcd (d1.prod id) (d2.prod id) ∣ n := by
      have hdiv := Nat.dvd_add hg_nm hg_m
      simpa [hsum] using hdiv
    exact hnot hg_n
  rw [hcard_zero, if_neg hnot]
  norm_num

/-! ## Compatible-support remainder sum -/

/-- Pair remainder with the incompatible gcd branch made explicit. -/
noncomputable def residueCompatiblePairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  if Nat.gcd (d1.prod id) (d2.prod id) ∣ n then
    residuePairCountingRemainder n d1 d2
  else
    0

/-- The compatible-support pair remainder is equal to the original pair
remainder; incompatible branches vanish algebraically. -/
theorem residueCompatiblePairCountingRemainder_eq
    (n : ℕ) (d1 d2 : Finset ℕ) :
    residueCompatiblePairCountingRemainder n d1 d2 =
      residuePairCountingRemainder n d1 d2 := by
  unfold residueCompatiblePairCountingRemainder
  by_cases hdiv : Nat.gcd (d1.prod id) (d2.prod id) ∣ n
  · rw [if_pos hdiv]
  · rw [if_neg hdiv]
    exact (residuePairCountingRemainder_eq_zero_of_not_gcd_dvd
      n d1 d2 hdiv).symm

/-- The signed remainder sum with only gcd-compatible pair terms. -/
noncomputable def residueDoubleDivisorCompatibleRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residueCompatiblePairCountingRemainder n d1 d2

/-- At-sqrt compatible-support signed remainder at the canonical depth. -/
noncomputable def residueDoubleDivisorCompatibleRemainderSumAtSqrt
    (n : ℕ) : ℝ :=
  residueDoubleDivisorCompatibleRemainderSum n (Nat.sqrt n) (canonicalK n)

/-- Removing the incompatible support leaves the full signed remainder sum
unchanged. -/
theorem residueDoubleDivisorCompatibleRemainderSum_eq_remainderSum
    (n z k : ℕ) :
    residueDoubleDivisorCompatibleRemainderSum n z k =
      residueDoubleDivisorRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorCompatibleRemainderSum
    residueDoubleDivisorRemainderSum
  refine Finset.sum_congr rfl ?_
  intro d1 _hd1
  refine Finset.sum_congr rfl ?_
  intro d2 _hd2
  rw [residueCompatiblePairCountingRemainder_eq]

/-- At-sqrt version of the compatible-support equality. -/
theorem residueDoubleDivisorCompatibleRemainderSumAtSqrt_eq
    (n : ℕ) :
    residueDoubleDivisorCompatibleRemainderSumAtSqrt n =
      residueDoubleDivisorRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorCompatibleRemainderSumAtSqrt,
    residueDoubleDivisorRemainderSumAtSqrt] using
      residueDoubleDivisorCompatibleRemainderSum_eq_remainderSum
        n (Nat.sqrt n) (canonicalK n)

/-! ## Log-squared upper worker on the compatible support -/

/-- Large-range upper bound for the compatible-support signed remainder. -/
noncomputable def ResidueCompatibleRemainderLogSquaredUpperAfter
    (N : ℕ) (A : ℝ) : Prop :=
  0 < A ∧
    ∀ n : ℕ, 16 ≤ n → N + 1 ≤ Nat.sqrt n →
      |residueDoubleDivisorCompatibleRemainderSumAtSqrt n| ≤
        A * (n : ℝ) / (Real.log (n : ℝ))^2

/-- Eventual form of the compatible-support signed remainder upper bound. -/
noncomputable def ResidueCompatibleRemainderLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ, ResidueCompatibleRemainderLogSquaredUpperAfter N A

/-- A compatible-support upper bound implies the Round 73 full remainder upper
bound, because the incompatible support contributes zero. -/
theorem residueRemainderLogSquaredUpperAfter_of_compatible
    {N : ℕ} {A : ℝ}
    (hCompat : ResidueCompatibleRemainderLogSquaredUpperAfter N A) :
    ResidueRemainderLogSquaredUpperAfter N A := by
  rcases hCompat with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  rw [← residueDoubleDivisorCompatibleRemainderSumAtSqrt_eq n]
  exact hbd n hn hsqrt

/-- Eventual compatible-support upper bound supplies the Round 73 active
signed-remainder upper worker. -/
theorem residueRemainderLogSquaredUpperEventually_of_compatible
    (hCompat : ResidueCompatibleRemainderLogSquaredUpperEventually) :
    ResidueRemainderLogSquaredUpperEventually := by
  rcases hCompat with ⟨N, A, hN⟩
  exact ⟨N, A, residueRemainderLogSquaredUpperAfter_of_compatible hN⟩

/-- Final Path C adapter from the compatible-support signed-remainder upper
worker and any supported counting input. -/
theorem pathC_kGoldbach_of_compatibleRemainderLogSquaredUpperEventually_and_countingInput
    (hCompat : ResidueCompatibleRemainderLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_remainderLogSquaredUpperEventually_and_countingInput
    (residueRemainderLogSquaredUpperEventually_of_compatible hCompat)
    hCounting

end PathCResidueRemainderCompatibleSupport
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderCompatibleSupport.residuePairCountingRemainder_eq_zero_of_not_gcd_dvd
#print axioms
  Gdbh.PathCResidueRemainderCompatibleSupport.residueDoubleDivisorCompatibleRemainderSum_eq_remainderSum
#print axioms
  Gdbh.PathCResidueRemainderCompatibleSupport.residueRemainderLogSquaredUpperAfter_of_compatible
#print axioms
  Gdbh.PathCResidueRemainderCompatibleSupport.residueRemainderLogSquaredUpperEventually_of_compatible
#print axioms
  Gdbh.PathCResidueRemainderCompatibleSupport.pathC_kGoldbach_of_compatibleRemainderLogSquaredUpperEventually_and_countingInput
