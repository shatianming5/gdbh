import Gdbh.Goldbach

namespace Gdbh

structure CircleMethodLowerBound where
  threshold : Nat
  mainTerm : Nat → Nat
  errorTerm : Nat → Nat
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - errorTerm n ≤ GoldbachCount n
  errorDominated :
    ∀ n : Nat, threshold < n → Even n → errorTerm n < mainTerm n

theorem count_positive_of_circle_method_lower_bound
    (bound : CircleMethodLowerBound) :
    GoldbachCountPositiveAbove bound.threshold := by
  intro n htn hEven
  have hdiff_pos : 0 < bound.mainTerm n - bound.errorTerm n := by
    exact Nat.sub_pos_of_lt (bound.errorDominated n htn hEven)
  exact lt_of_lt_of_le hdiff_pos (bound.lowerBound n htn hEven)

end Gdbh
