import Gdbh.Certificate100
import Gdbh.CircleMethod

namespace Gdbh

def ExplicitGoldbachLowerBound (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n → 0 < GoldbachCount n

theorem count_positive_above_of_explicit_lower_bound {B : Nat}
    (lower_bound : ExplicitGoldbachLowerBound B) :
    GoldbachCountPositiveAbove B :=
  lower_bound

theorem explicit_lower_bound_of_count_positive_above {B : Nat}
    (count_positive : GoldbachCountPositiveAbove B) :
    ExplicitGoldbachLowerBound B :=
  count_positive

theorem explicit_lower_bound_iff_count_positive_above {B : Nat} :
    ExplicitGoldbachLowerBound B ↔ GoldbachCountPositiveAbove B := by
  constructor
  · exact count_positive_above_of_explicit_lower_bound
  · exact explicit_lower_bound_of_count_positive_above

theorem strongGoldbach_from_explicit_lower_bound100
    (lower_bound : ExplicitGoldbachLowerBound 100) :
    StrongGoldbach :=
  strongGoldbach_from_certificate100_and_count_positive_bridge
    (count_positive_above_of_explicit_lower_bound lower_bound)

theorem explicitLowerBound100_from_certificate100_and_explicit_lower_bound
    {T : Nat}
    (hthreshold : T ≤ 100)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    ExplicitGoldbachLowerBound 100 := by
  intro n h100 hEven
  by_cases hle : n ≤ 100
  · exact goldbachCount_pos_of_representation
      (goldbachUpTo100 n (by omega) hle hEven)
  · exact lower_bound n
      (lt_of_le_of_lt hthreshold (Nat.lt_of_not_ge hle)) hEven

theorem strongGoldbach_iff_explicit_lower_bound100 :
    StrongGoldbach ↔ ExplicitGoldbachLowerBound 100 := by
  simpa [ExplicitGoldbachLowerBound] using strongGoldbach_iff_count_positive_above100

theorem strongGoldbach_of_circle_method_lower_bound100
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold = 100) :
    StrongGoldbach := by
  apply strongGoldbach_from_explicit_lower_bound100
  intro n h100 hEven
  rw [← hthreshold] at h100
  exact count_positive_of_circle_method_lower_bound bound n h100 hEven

theorem strongGoldbach_of_circle_method_lower_bound_le100
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach := by
  apply strongGoldbach_from_explicit_lower_bound100
  exact goldbachCountPositiveAbove_mono hthreshold
    (count_positive_of_circle_method_lower_bound bound)

end Gdbh
