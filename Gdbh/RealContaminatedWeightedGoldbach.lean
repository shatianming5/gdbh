import Gdbh.GeneralHandoff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Gdbh

def RawRealWeightedGoldbachSum (w : Nat → ℝ) (n : Nat) : ℝ :=
  (Finset.range n.succ).sum (fun p => w p * w (n - p))

def PrimePairRealWeightedGoldbachSum (w : Nat → ℝ) (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).sum
      (fun p => w p * w (n - p))

def NonPrimePairRealWeightedGoldbachSum (w : Nat → ℝ) (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))).sum
      (fun p => w p * w (n - p))

theorem rawRealWeightedGoldbachSum_split (w : Nat → ℝ) (n : Nat) :
    RawRealWeightedGoldbachSum w n =
      PrimePairRealWeightedGoldbachSum w n +
        NonPrimePairRealWeightedGoldbachSum w n := by
  classical
  rw [RawRealWeightedGoldbachSum, PrimePairRealWeightedGoldbachSum,
    NonPrimePairRealWeightedGoldbachSum]
  exact (Finset.sum_filter_add_sum_filter_not
    (s := Finset.range n.succ)
    (p := fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    (f := fun p => w p * w (n - p))).symm

theorem goldbachRepresentation_of_prime_pair_real_weighted_sum_pos
    {w : Nat → ℝ} {n : Nat}
    (hweight_nonneg : ∀ m : Nat, 0 ≤ w m)
    (hsum : 0 < PrimePairRealWeightedGoldbachSum w n) :
    GoldbachRepresentation n := by
  rw [PrimePairRealWeightedGoldbachSum] at hsum
  rw [Finset.sum_pos_iff_of_nonneg] at hsum
  · rcases hsum with ⟨p, hp_mem, _hp_pos⟩
    rcases Finset.mem_filter.mp hp_mem with ⟨hp_range, hp_pair⟩
    exact goldbachRepresentation_of_prime_sub
      hp_pair.1
      hp_pair.2
      (Nat.le_of_lt_succ (Finset.mem_range.mp hp_range))
  · intro p _hp_mem
    exact mul_nonneg (hweight_nonneg p) (hweight_nonneg (n - p))

theorem prime_pair_real_weighted_sum_pos_of_raw_gt_nonprime
    {w : Nat → ℝ} {n : Nat}
    (hgt :
      NonPrimePairRealWeightedGoldbachSum w n <
        RawRealWeightedGoldbachSum w n) :
    0 < PrimePairRealWeightedGoldbachSum w n := by
  have hsplit := rawRealWeightedGoldbachSum_split w n
  linarith

theorem goldbachRepresentation_of_raw_real_weighted_sum_gt_nonprime
    {w : Nat → ℝ} {n : Nat}
    (hweight_nonneg : ∀ m : Nat, 0 ≤ w m)
    (hgt :
      NonPrimePairRealWeightedGoldbachSum w n <
        RawRealWeightedGoldbachSum w n) :
    GoldbachRepresentation n :=
  goldbachRepresentation_of_prime_pair_real_weighted_sum_pos
    hweight_nonneg
    (prime_pair_real_weighted_sum_pos_of_raw_gt_nonprime hgt)

theorem goldbachCount_pos_of_raw_real_weighted_sum_gt_nonprime
    {w : Nat → ℝ} {n : Nat}
    (hweight_nonneg : ∀ m : Nat, 0 ≤ w m)
    (hgt :
      NonPrimePairRealWeightedGoldbachSum w n <
        RawRealWeightedGoldbachSum w n) :
    0 < GoldbachCount n :=
  goldbachCount_pos_of_representation
    (goldbachRepresentation_of_raw_real_weighted_sum_gt_nonprime
      hweight_nonneg hgt)

def RealContaminatedWeightedGoldbachPositiveAbove
    (w : Nat → ℝ) (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n →
    NonPrimePairRealWeightedGoldbachSum w n <
      RawRealWeightedGoldbachSum w n

theorem count_positive_above_of_real_contaminated_weighted_positive_above
    {w : Nat → ℝ} {B : Nat}
    (hweight_nonneg : ∀ m : Nat, 0 ≤ w m)
    (positive : RealContaminatedWeightedGoldbachPositiveAbove w B) :
    GoldbachCountPositiveAbove B := by
  intro n hBn hEven
  exact goldbachCount_pos_of_raw_real_weighted_sum_gt_nonprime
    hweight_nonneg
    (positive n hBn hEven)

structure RealContaminatedWeightedGoldbachLowerBound where
  weight : Nat → ℝ
  weight_nonneg : ∀ m : Nat, 0 ≤ weight m
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  contamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawRealWeightedGoldbachSum weight n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairRealWeightedGoldbachSum weight n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + contamination n < mainTerm n

theorem real_contaminated_weighted_positive_above_of_lower_bound
    (bound : RealContaminatedWeightedGoldbachLowerBound) :
    RealContaminatedWeightedGoldbachPositiveAbove
      bound.weight bound.threshold := by
  intro n htn hEven
  have hlower := bound.lowerBound n htn hEven
  have hcontam := bound.contaminationBound n htn hEven
  have hdom := bound.totalErrorDominated n htn hEven
  linarith

theorem count_positive_above_of_real_contaminated_weighted_lower_bound
    (bound : RealContaminatedWeightedGoldbachLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_real_contaminated_weighted_positive_above
    bound.weight_nonneg
    (real_contaminated_weighted_positive_above_of_lower_bound bound)

theorem explicit_lower_bound_of_real_contaminated_weighted_lower_bound
    (bound : RealContaminatedWeightedGoldbachLowerBound) :
    ExplicitGoldbachLowerBound bound.threshold :=
  count_positive_above_of_real_contaminated_weighted_lower_bound bound

theorem strongGoldbach_of_real_contaminated_weighted_lower_bound_le100
    (bound : RealContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    goldbachUpTo100
    hthreshold
    (count_positive_above_of_real_contaminated_weighted_lower_bound bound)

theorem strongGoldbach_of_finite_and_real_contaminated_weighted_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : RealContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite
    hthreshold
    (count_positive_above_of_real_contaminated_weighted_lower_bound bound)

structure RealContaminatedWeightedMajorMinorArcEstimate where
  weight : Nat → ℝ
  weight_nonneg : ∀ m : Nat, 0 ≤ weight m
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  contamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawRealWeightedGoldbachSum weight n + minorArcError n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairRealWeightedGoldbachSum weight n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + contamination n < mainTerm n

def RealContaminatedWeightedMajorMinorArcEstimate.toLowerBound
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate) :
    RealContaminatedWeightedGoldbachLowerBound where
  weight := estimate.weight
  weight_nonneg := estimate.weight_nonneg
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  analyticError := fun n => estimate.majorArcError n + estimate.minorArcError n
  contamination := estimate.contamination
  lowerBound := by
    intro n htn hEven
    have hcombined := estimate.combinedLowerBound n htn hEven
    linarith
  contaminationBound := by
    intro n htn hEven
    exact estimate.contaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    have hdom := estimate.totalErrorDominated n htn hEven
    linarith

theorem count_positive_above_of_real_contaminated_weighted_major_minor_arc_estimate
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_real_contaminated_weighted_lower_bound
    estimate.toLowerBound

theorem explicit_lower_bound_of_real_contaminated_weighted_major_minor_arc_estimate
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_real_contaminated_weighted_major_minor_arc_estimate
    estimate

theorem strongGoldbach_of_real_contaminated_weighted_major_minor_arc_estimate_le100
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_real_contaminated_weighted_lower_bound_le100
    estimate.toLowerBound
    (by
      simpa [RealContaminatedWeightedMajorMinorArcEstimate.toLowerBound] using
        hthreshold)

theorem strongGoldbach_of_finite_and_real_contaminated_weighted_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_real_contaminated_weighted_lower_bound_le
    finite
    estimate.toLowerBound
    (by
      simpa [RealContaminatedWeightedMajorMinorArcEstimate.toLowerBound] using
        hthreshold)

end Gdbh
