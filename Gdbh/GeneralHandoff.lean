import Gdbh.MajorMinorArcs
import Gdbh.WeightedMajorMinorArcs

namespace Gdbh

theorem count_positive_above_of_finite_and_count_positive_above_le
    {A B T : Nat}
    (hA : 2 ≤ A)
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (count_positive : GoldbachCountPositiveAbove T) :
    GoldbachCountPositiveAbove A := by
  intro n hAn hEven
  by_cases hle : n ≤ B
  · exact goldbachCount_pos_of_representation
      (finite n (lt_of_le_of_lt hA hAn) hle hEven)
  · exact count_positive n
      (lt_of_le_of_lt hthreshold (Nat.lt_of_not_ge hle)) hEven

theorem explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    {A B T : Nat}
    (hA : 2 ≤ A)
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    ExplicitGoldbachLowerBound A :=
  explicit_lower_bound_of_count_positive_above
    (count_positive_above_of_finite_and_count_positive_above_le
      hA finite hthreshold
      (count_positive_above_of_explicit_lower_bound lower_bound))

theorem explicit_lower_bound100_of_finite_and_explicit_lower_bound_le
    {B T : Nat}
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    ExplicitGoldbachLowerBound 100 :=
  explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    (A := 100) (by decide) finite hthreshold lower_bound

theorem strongGoldbach_of_finite_and_count_positive_above_le
    {B T : Nat}
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (count_positive : GoldbachCountPositiveAbove T) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_above finite
    (goldbachAbove_of_count_positive_above
      (goldbachCountPositiveAbove_mono hthreshold count_positive))

theorem strongGoldbach_of_finite_and_explicit_lower_bound_le
    {B T : Nat}
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite hthreshold
    (count_positive_above_of_explicit_lower_bound lower_bound)

theorem strongGoldbach_of_finite_and_circle_method_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite hthreshold
    (count_positive_of_circle_method_lower_bound bound)

theorem strongGoldbach_of_finite_and_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : MajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite hthreshold
    (count_positive_of_major_minor_arc_estimate estimate)

theorem strongGoldbach_of_finite_and_weighted_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : WeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite hthreshold
    (count_positive_above_of_weighted_lower_bound bound)

theorem strongGoldbach_of_finite_and_weighted_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : WeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    finite hthreshold
    (count_positive_above_of_weighted_major_minor_arc_estimate estimate)

end Gdbh
