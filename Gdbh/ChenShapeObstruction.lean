import Mathlib.Tactic

/-!
# Chen-type shape obstruction

This file records a predicate-generic obstruction for routes that prove a
mixed representation theorem: one summand satisfies a core predicate while the
other satisfies a broader predicate.  This is the logical shape behind
prime-plus-almost-prime partial results.

The examples below are not statements about primes.  They show that even a
uniform representation theorem of the form `Core + Broad` on every
binary-Goldbach-domain input does not logically recover a `Core + Core`
binary-pair theorem.
-/

namespace Gdbh
namespace ChenShapeObstruction

/-- The input domain of the binary Goldbach statement. -/
def GoldbachEvenDomain (n : Nat) : Prop :=
  4 ≤ n ∧ Even n

/-- A mixed pair representation: the left summand satisfies `Core`, while the
right summand only satisfies the broader predicate `Broad`. -/
def CorePlusBroadCoverageOn (Domain : Nat → Prop)
    (Core Broad : Nat → Prop) : Prop :=
  ∀ n : Nat, Domain n → ∃ p q : Nat, Core p ∧ Broad q ∧ p + q = n

/-- The genuine binary endpoint: both summands satisfy the same core
predicate. -/
def CorePairCoverageOn (Domain : Nat → Prop) (Core : Nat → Prop) : Prop :=
  ∀ n : Nat, Domain n → ∃ p q : Nat, Core p ∧ Core q ∧ p + q = n

/-- `Broad` is strictly broader than `Core`. -/
def StrictlyBroadens (Core Broad : Nat → Prop) : Prop :=
  (∀ n : Nat, Core n → Broad n) ∧ ∃ n : Nat, Broad n ∧ ¬ Core n

/-- A deliberately tiny core predicate. -/
def ToyCore (n : Nat) : Prop :=
  n = 2

/-- A broader toy predicate. -/
def ToyBroad (n : Nat) : Prop :=
  2 ≤ n ∧ Even n

/-- `ToyBroad` properly contains `ToyCore`. -/
theorem toyBroad_strictlyBroadens_toyCore :
    StrictlyBroadens ToyCore ToyBroad := by
  constructor
  · intro n hn
    subst hn
    exact ⟨by norm_num, by norm_num⟩
  · refine ⟨4, ?_, ?_⟩
    · exact ⟨by norm_num, by norm_num⟩
    · intro h
      norm_num [ToyCore] at h

/-- Every Goldbach-domain input has a toy mixed representation `2 + (n - 2)`,
where the second summand only satisfies the broad predicate. -/
theorem toyCorePlusBroadCoverage :
    CorePlusBroadCoverageOn GoldbachEvenDomain ToyCore ToyBroad := by
  intro n hn
  unfold GoldbachEvenDomain at hn
  refine ⟨2, n - 2, rfl, ?_, ?_⟩
  · constructor
    · have h22 : 2 + 2 ≤ n := by omega
      exact Nat.le_sub_of_add_le h22
    · rcases hn.2 with ⟨k, hk⟩
      have hk2 : 2 ≤ k := by omega
      refine ⟨k - 1, ?_⟩
      omega
  · have hn2 : 2 ≤ n := by omega
    exact Nat.add_sub_of_le hn2

/-- The toy core cannot represent `6` as a binary pair of core summands. -/
theorem toyCore_not_corePairCoverage :
    ¬ CorePairCoverageOn GoldbachEvenDomain ToyCore := by
  intro hcover
  rcases hcover 6 ⟨by norm_num, by norm_num⟩ with
    ⟨p, q, hp, hq, hsum⟩
  simp [ToyCore] at hp hq
  omega

/-- A core-plus-broad theorem, even with `Broad` a proper extension of `Core`,
does not logically force a core-plus-core binary theorem. -/
theorem corePlusBroadCoverage_not_force_corePairCoverage :
    ∃ Core Broad : Nat → Prop,
      StrictlyBroadens Core Broad ∧
        CorePlusBroadCoverageOn GoldbachEvenDomain Core Broad ∧
          ¬ CorePairCoverageOn GoldbachEvenDomain Core := by
  exact
    ⟨ToyCore, ToyBroad, toyBroad_strictlyBroadens_toyCore,
      toyCorePlusBroadCoverage, toyCore_not_corePairCoverage⟩

end ChenShapeObstruction
end Gdbh
