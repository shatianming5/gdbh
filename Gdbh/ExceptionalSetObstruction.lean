import Mathlib.Tactic

/-!
# Exceptional-set obstruction

This file records a small obstruction for density-one, cofinite, or
"eventually true" Goldbach routes.  Even a result that proves the target for
all sufficiently large inputs does not by itself prove the universal binary
Goldbach statement.  The finite exceptional range still has to be verified.

The file is intentionally predicate-generic.  The final theorem gives a
one-hole model on the Goldbach domain: a property can hold for every even
`n >= 4` above a threshold and still fail at `n = 4`.
-/

namespace Gdbh
namespace ExceptionalSetObstruction

/-- `P` holds above the finite threshold `B`. -/
def EventuallyAbove (B : Nat) (P : Nat → Prop) : Prop :=
  ∀ n : Nat, B < n → P n

/-- `P` has been checked through the finite threshold `B`. -/
def CheckedUpTo (B : Nat) (P : Nat → Prop) : Prop :=
  ∀ n : Nat, n ≤ B → P n

/-- The binary-Goldbach-shaped domain: all even `n >= 4`. -/
def EvenDomainUniversal (P : Nat → Prop) : Prop :=
  ∀ n : Nat, 4 ≤ n → Even n → P n

/-- `P` holds above `B` on the binary-Goldbach-shaped domain. -/
def EvenDomainEventuallyAbove (B : Nat) (P : Nat → Prop) : Prop :=
  ∀ n : Nat, B < n → 4 ≤ n → Even n → P n

/-- `P` has been checked through `B` on the binary-Goldbach-shaped domain. -/
def EvenDomainCheckedUpTo (B : Nat) (P : Nat → Prop) : Prop :=
  ∀ n : Nat, 4 ≤ n → n ≤ B → Even n → P n

/-- For any predicate, universal coverage is exactly finite verification up to
`B` plus coverage above `B`. -/
theorem universal_iff_checkedUpTo_and_eventuallyAbove
    (B : Nat) (P : Nat → Prop) :
    (∀ n : Nat, P n) ↔ CheckedUpTo B P ∧ EventuallyAbove B P := by
  constructor
  · intro h
    exact ⟨fun n _ => h n, fun n _ => h n⟩
  · rintro ⟨hcheck, habove⟩ n
    by_cases hn : n ≤ B
    · exact hcheck n hn
    · exact habove n (by omega)

/-- Binary-Goldbach-shaped universal coverage is exactly finite verification
up to `B` plus above-threshold coverage. -/
theorem evenDomainUniversal_iff_checkedUpTo_and_eventuallyAbove
    (B : Nat) (P : Nat → Prop) :
    EvenDomainUniversal P ↔
      EvenDomainCheckedUpTo B P ∧ EvenDomainEventuallyAbove B P := by
  constructor
  · intro h
    exact
      ⟨fun n h4 _ heven => h n h4 heven,
        fun n _ h4 heven => h n h4 heven⟩
  · rintro ⟨hcheck, habove⟩ n h4 heven
    by_cases hn : n ≤ B
    · exact hcheck n h4 hn heven
    · exact habove n (by omega) h4 heven

/-- The predicate that misses exactly one input. -/
def OneHoleAt (m : Nat) : Nat → Prop :=
  fun n => n ≠ m

/-- A one-hole predicate is true above the missing point. -/
theorem oneHole_eventuallyAbove (m : Nat) :
    EventuallyAbove m (OneHoleAt m) := by
  intro n hn h
  omega

/-- A one-hole predicate is not universal. -/
theorem oneHole_not_universal (m : Nat) :
    ¬ (∀ n : Nat, OneHoleAt m n) := by
  intro h
  exact h m rfl

/-- Above-threshold coverage alone does not imply global coverage. -/
theorem eventuallyAbove_not_global :
    ∃ P : Nat → Prop, (∃ B : Nat, EventuallyAbove B P) ∧
      ¬ (∀ n : Nat, P n) := by
  refine ⟨OneHoleAt 0, ?_, oneHole_not_universal 0⟩
  exact ⟨0, oneHole_eventuallyAbove 0⟩

/-- A one-hole predicate at the first Goldbach-domain input. -/
def GoldbachDomainOneHole : Nat → Prop :=
  OneHoleAt 4

/-- The one-hole predicate holds above `4` on the Goldbach domain. -/
theorem goldbachDomainOneHole_eventuallyAbove :
    EvenDomainEventuallyAbove 4 GoldbachDomainOneHole := by
  intro n hn _ _ h
  omega

/-- The one-hole predicate still fails on the Goldbach domain at `n = 4`. -/
theorem goldbachDomainOneHole_not_universal :
    ¬ EvenDomainUniversal GoldbachDomainOneHole := by
  intro h
  exact h 4 (by norm_num) (by norm_num) rfl

/-- Even cofinite coverage on the Goldbach domain does not force the universal
statement unless the finite exceptional range is also checked. -/
theorem evenDomainEventuallyAbove_not_global :
    ∃ P : Nat → Prop,
      EvenDomainEventuallyAbove 4 P ∧ ¬ EvenDomainUniversal P := by
  exact
    ⟨GoldbachDomainOneHole, goldbachDomainOneHole_eventuallyAbove,
      goldbachDomainOneHole_not_universal⟩

end ExceptionalSetObstruction
end Gdbh
