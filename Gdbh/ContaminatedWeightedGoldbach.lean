import Gdbh.GeneralHandoff

namespace Gdbh

def RawWeightedGoldbachSum (w : Nat → Nat) (n : Nat) : Nat :=
  (Finset.range n.succ).sum (fun p => w p * w (n - p))

def PrimePairWeightedGoldbachSum (w : Nat → Nat) (n : Nat) : Nat :=
  ((Finset.range n.succ).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).sum
      (fun p => w p * w (n - p))

def NonPrimePairWeightedGoldbachSum (w : Nat → Nat) (n : Nat) : Nat :=
  ((Finset.range n.succ).filter
    (fun p => ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))).sum
      (fun p => w p * w (n - p))

theorem rawWeightedGoldbachSum_split (w : Nat → Nat) (n : Nat) :
    RawWeightedGoldbachSum w n =
      PrimePairWeightedGoldbachSum w n +
        NonPrimePairWeightedGoldbachSum w n := by
  classical
  rw [RawWeightedGoldbachSum, PrimePairWeightedGoldbachSum,
    NonPrimePairWeightedGoldbachSum]
  exact (Finset.sum_filter_add_sum_filter_not
    (s := Finset.range n.succ)
    (p := fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    (f := fun p => w p * w (n - p))).symm

theorem goldbachRepresentation_of_prime_pair_weighted_sum_pos
    {w : Nat → Nat} {n : Nat}
    (hsum : 0 < PrimePairWeightedGoldbachSum w n) :
    GoldbachRepresentation n := by
  rw [PrimePairWeightedGoldbachSum] at hsum
  rw [Finset.sum_pos_iff_of_nonneg] at hsum
  · rcases hsum with ⟨p, hp_mem, _hp_pos⟩
    rcases Finset.mem_filter.mp hp_mem with ⟨hp_range, hp_pair⟩
    exact goldbachRepresentation_of_prime_sub
      hp_pair.1
      hp_pair.2
      (Nat.le_of_lt_succ (Finset.mem_range.mp hp_range))
  · intro p _hp_mem
    exact Nat.zero_le _

theorem prime_pair_weighted_sum_pos_of_raw_gt_nonprime
    {w : Nat → Nat} {n : Nat}
    (hgt : NonPrimePairWeightedGoldbachSum w n < RawWeightedGoldbachSum w n) :
    0 < PrimePairWeightedGoldbachSum w n := by
  have hsplit := rawWeightedGoldbachSum_split w n
  omega

theorem goldbachRepresentation_of_raw_weighted_sum_gt_nonprime
    {w : Nat → Nat} {n : Nat}
    (hgt : NonPrimePairWeightedGoldbachSum w n < RawWeightedGoldbachSum w n) :
    GoldbachRepresentation n :=
  goldbachRepresentation_of_prime_pair_weighted_sum_pos
    (prime_pair_weighted_sum_pos_of_raw_gt_nonprime hgt)

theorem goldbachCount_pos_of_raw_weighted_sum_gt_nonprime
    {w : Nat → Nat} {n : Nat}
    (hgt : NonPrimePairWeightedGoldbachSum w n < RawWeightedGoldbachSum w n) :
    0 < GoldbachCount n :=
  goldbachCount_pos_of_representation
    (goldbachRepresentation_of_raw_weighted_sum_gt_nonprime hgt)

def ContaminatedWeightedGoldbachPositiveAbove (w : Nat → Nat) (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n →
    NonPrimePairWeightedGoldbachSum w n < RawWeightedGoldbachSum w n

theorem count_positive_above_of_contaminated_weighted_positive_above
    {w : Nat → Nat} {B : Nat}
    (positive : ContaminatedWeightedGoldbachPositiveAbove w B) :
    GoldbachCountPositiveAbove B := by
  intro n hBn hEven
  exact goldbachCount_pos_of_raw_weighted_sum_gt_nonprime
    (positive n hBn hEven)

structure ContaminatedWeightedGoldbachLowerBound where
  weight : Nat → Nat
  threshold : Nat
  mainTerm : Nat → Nat
  analyticError : Nat → Nat
  contamination : Nat → Nat
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawWeightedGoldbachSum weight n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairWeightedGoldbachSum weight n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + contamination n < mainTerm n

theorem contaminated_weighted_positive_above_of_lower_bound
    (bound : ContaminatedWeightedGoldbachLowerBound) :
    ContaminatedWeightedGoldbachPositiveAbove bound.weight bound.threshold := by
  intro n htn hEven
  have hlower := bound.lowerBound n htn hEven
  have hcontam := bound.contaminationBound n htn hEven
  have hdom := bound.totalErrorDominated n htn hEven
  omega

theorem count_positive_above_of_contaminated_weighted_lower_bound
    (bound : ContaminatedWeightedGoldbachLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_contaminated_weighted_positive_above
    (contaminated_weighted_positive_above_of_lower_bound bound)

theorem explicit_lower_bound_of_contaminated_weighted_lower_bound
    (bound : ContaminatedWeightedGoldbachLowerBound) :
    ExplicitGoldbachLowerBound bound.threshold :=
  count_positive_above_of_contaminated_weighted_lower_bound bound

theorem strongGoldbach_of_contaminated_weighted_lower_bound_le100
    (bound : ContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    goldbachUpTo100
    hthreshold
    (count_positive_above_of_contaminated_weighted_lower_bound bound)

theorem strongGoldbach_of_finite_and_contaminated_weighted_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : ContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite
    hthreshold
    (count_positive_above_of_contaminated_weighted_lower_bound bound)

structure ContaminatedWeightedMajorMinorArcEstimate where
  weight : Nat → Nat
  threshold : Nat
  mainTerm : Nat → Nat
  majorArcError : Nat → Nat
  minorArcError : Nat → Nat
  contamination : Nat → Nat
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawWeightedGoldbachSum weight n + minorArcError n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairWeightedGoldbachSum weight n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + contamination n < mainTerm n

def ContaminatedWeightedMajorMinorArcEstimate.toLowerBound
    (estimate : ContaminatedWeightedMajorMinorArcEstimate) :
    ContaminatedWeightedGoldbachLowerBound where
  weight := estimate.weight
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  analyticError := fun n => estimate.majorArcError n + estimate.minorArcError n
  contamination := estimate.contamination
  lowerBound := by
    intro n htn hEven
    have hcombined := estimate.combinedLowerBound n htn hEven
    omega
  contaminationBound := by
    intro n htn hEven
    exact estimate.contaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    have hdom := estimate.totalErrorDominated n htn hEven
    omega

theorem count_positive_above_of_contaminated_weighted_major_minor_arc_estimate
    (estimate : ContaminatedWeightedMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_contaminated_weighted_lower_bound
    estimate.toLowerBound

theorem explicit_lower_bound_of_contaminated_weighted_major_minor_arc_estimate
    (estimate : ContaminatedWeightedMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_contaminated_weighted_major_minor_arc_estimate estimate

theorem strongGoldbach_of_contaminated_weighted_major_minor_arc_estimate_le100
    (estimate : ContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_contaminated_weighted_lower_bound_le100
    estimate.toLowerBound
    (by
      simpa [ContaminatedWeightedMajorMinorArcEstimate.toLowerBound] using
        hthreshold)

theorem strongGoldbach_of_finite_and_contaminated_weighted_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : ContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_contaminated_weighted_lower_bound_le
    finite
    estimate.toLowerBound
    (by
      simpa [ContaminatedWeightedMajorMinorArcEstimate.toLowerBound] using
        hthreshold)

end Gdbh
