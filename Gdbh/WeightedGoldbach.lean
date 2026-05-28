import Gdbh.AnalyticBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Gdbh

structure PrimeSupportedWeight where
  weight : Nat → Nat
  prime_of_pos : ∀ m : Nat, 0 < weight m → Nat.Prime m

def WeightedGoldbachSum (w : PrimeSupportedWeight) (n : Nat) : Nat :=
  (Finset.range n.succ).sum (fun p => w.weight p * w.weight (n - p))

def WeightedGoldbachPositiveAbove (w : PrimeSupportedWeight) (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n → 0 < WeightedGoldbachSum w n

theorem goldbachRepresentation_of_weighted_sum_pos
    {w : PrimeSupportedWeight} {n : Nat}
    (hsum : 0 < WeightedGoldbachSum w n) :
    GoldbachRepresentation n := by
  rw [WeightedGoldbachSum] at hsum
  rw [Finset.sum_pos_iff_of_nonneg] at hsum
  · rcases hsum with ⟨p, hp_mem, hp_pos⟩
    have hp_weight_pos : 0 < w.weight p :=
      Nat.pos_of_mul_pos_right hp_pos
    have hq_weight_pos : 0 < w.weight (n - p) :=
      Nat.pos_of_mul_pos_left hp_pos
    have hp_le : p ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hp_mem)
    exact goldbachRepresentation_of_prime_sub
      (w.prime_of_pos p hp_weight_pos)
      (w.prime_of_pos (n - p) hq_weight_pos)
      hp_le
  · intro p _hp_mem
    exact Nat.zero_le _

theorem goldbachCount_pos_of_weighted_sum_pos
    {w : PrimeSupportedWeight} {n : Nat}
    (hsum : 0 < WeightedGoldbachSum w n) :
    0 < GoldbachCount n :=
  goldbachCount_pos_of_representation
    (goldbachRepresentation_of_weighted_sum_pos hsum)

theorem count_positive_above_of_weighted_positive_above
    {w : PrimeSupportedWeight} {B : Nat}
    (weighted_positive : WeightedGoldbachPositiveAbove w B) :
    GoldbachCountPositiveAbove B := by
  intro n hBn hEven
  exact goldbachCount_pos_of_weighted_sum_pos
    (weighted_positive n hBn hEven)

theorem explicit_lower_bound_of_weighted_positive_above
    {w : PrimeSupportedWeight} {B : Nat}
    (weighted_positive : WeightedGoldbachPositiveAbove w B) :
    ExplicitGoldbachLowerBound B :=
  count_positive_above_of_weighted_positive_above weighted_positive

def primeIndicatorWeight : PrimeSupportedWeight where
  weight m := if Nat.Prime m then 1 else 0
  prime_of_pos := by
    intro m hm_pos
    by_cases hm : Nat.Prime m
    · exact hm
    · simp [hm] at hm_pos

theorem weightedGoldbachSum_primeIndicatorWeight (n : Nat) :
    WeightedGoldbachSum primeIndicatorWeight n = GoldbachCount n := by
  classical
  rw [WeightedGoldbachSum, GoldbachCount, GoldbachPrimeSubWitnesses]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _hp_mem
  by_cases hp : Nat.Prime p
  · by_cases hq : Nat.Prime (n - p)
    · simp [primeIndicatorWeight, hp, hq]
    · simp [primeIndicatorWeight, hp, hq]
  · simp [primeIndicatorWeight, hp]

theorem weightedGoldbachPositiveAbove_primeIndicatorWeight_iff {B : Nat} :
    WeightedGoldbachPositiveAbove primeIndicatorWeight B ↔
      GoldbachCountPositiveAbove B := by
  constructor
  · intro weighted_positive n hBn hEven
    simpa [weightedGoldbachSum_primeIndicatorWeight] using
      weighted_positive n hBn hEven
  · intro count_positive n hBn hEven
    simpa [weightedGoldbachSum_primeIndicatorWeight] using
      count_positive n hBn hEven

theorem explicit_lower_bound_iff_prime_indicator_weighted_positive_above
    {B : Nat} :
    ExplicitGoldbachLowerBound B ↔
      WeightedGoldbachPositiveAbove primeIndicatorWeight B := by
  rw [explicit_lower_bound_iff_count_positive_above]
  exact weightedGoldbachPositiveAbove_primeIndicatorWeight_iff.symm

structure WeightedGoldbachLowerBound where
  weight : PrimeSupportedWeight
  threshold : Nat
  mainTerm : Nat → Nat
  errorTerm : Nat → Nat
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - errorTerm n ≤ WeightedGoldbachSum weight n
  errorDominated :
    ∀ n : Nat, threshold < n → Even n → errorTerm n < mainTerm n

theorem weighted_positive_above_of_weighted_lower_bound
    (bound : WeightedGoldbachLowerBound) :
    WeightedGoldbachPositiveAbove bound.weight bound.threshold := by
  intro n htn hEven
  have hdiff_pos : 0 < bound.mainTerm n - bound.errorTerm n := by
    exact Nat.sub_pos_of_lt (bound.errorDominated n htn hEven)
  exact lt_of_lt_of_le hdiff_pos (bound.lowerBound n htn hEven)

theorem count_positive_above_of_weighted_lower_bound
    (bound : WeightedGoldbachLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_weighted_positive_above
    (weighted_positive_above_of_weighted_lower_bound bound)

theorem explicit_lower_bound_of_weighted_lower_bound
    (bound : WeightedGoldbachLowerBound) :
    ExplicitGoldbachLowerBound bound.threshold :=
  count_positive_above_of_weighted_lower_bound bound

theorem strongGoldbach_of_weighted_lower_bound_le100
    (bound : WeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach := by
  apply strongGoldbach_from_explicit_lower_bound100
  exact goldbachCountPositiveAbove_mono hthreshold
    (count_positive_above_of_weighted_lower_bound bound)

end Gdbh
