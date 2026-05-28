import Mathlib.Tactic

/-!
# Finite prefix obstruction

This file records a predicate-generic obstruction for finite certificate
escalation.  Even perfect verification on an arbitrarily long finite prefix of
the binary-Goldbach-shaped domain does not by itself prove the universal
statement.  A successful proof still needs a tail theorem above the certificate
threshold.

The examples below are not statements about primes.  They are logical models
showing why finite evidence must be paired with an infinite tail argument.
-/

namespace Gdbh
namespace FinitePrefixObstruction

/-- The binary-Goldbach-shaped domain: all even `n >= 4`. -/
def GoldbachEvenDomain (n : Nat) : Prop :=
  4 ≤ n ∧ Even n

/-- `P` has been checked through the finite threshold `B` on the
binary-Goldbach-shaped domain. -/
def CheckedOnGoldbachPrefix (B : Nat) (P : Nat → Prop) : Prop :=
  ∀ n : Nat, GoldbachEvenDomain n → n ≤ B → P n

/-- `P` holds on the whole binary-Goldbach-shaped domain. -/
def UniversalOnGoldbachDomain (P : Nat → Prop) : Prop :=
  ∀ n : Nat, GoldbachEvenDomain n → P n

/-- The even input `2 * (B + 2)` is always beyond the checked prefix. -/
theorem witnessBeyondPrefix_gt (B : Nat) :
    B < 2 * (B + 2) := by
  omega

/-- The even input `2 * (B + 2)` lies in the Goldbach domain. -/
theorem witnessBeyondPrefix_mem_domain (B : Nat) :
    GoldbachEvenDomain (2 * (B + 2)) := by
  constructor
  · omega
  · exact ⟨B + 2, by ring⟩

/-- A one-hole predicate whose missing point is the first formal witness we
choose beyond the finite prefix. -/
def OneHoleBeyondPrefix (B : Nat) : Nat → Prop :=
  fun n => n ≠ 2 * (B + 2)

/-- The one-hole predicate is perfect on the checked Goldbach prefix. -/
theorem oneHoleBeyondPrefix_checked (B : Nat) :
    CheckedOnGoldbachPrefix B (OneHoleBeyondPrefix B) := by
  intro n _ hn h
  have hgt : B < n := by
    rw [h]
    exact witnessBeyondPrefix_gt B
  omega

/-- The same one-hole predicate still fails globally on the Goldbach domain. -/
theorem oneHoleBeyondPrefix_not_universal (B : Nat) :
    ¬ UniversalOnGoldbachDomain (OneHoleBeyondPrefix B) := by
  intro h
  exact h (2 * (B + 2)) (witnessBeyondPrefix_mem_domain B) rfl

/-- Perfect finite-prefix verification, at any threshold, does not logically
force the universal binary-Goldbach-shaped statement. -/
theorem finitePrefixCheck_not_global (B : Nat) :
    ∃ P : Nat → Prop,
      CheckedOnGoldbachPrefix B P ∧ ¬ UniversalOnGoldbachDomain P := by
  exact
    ⟨OneHoleBeyondPrefix B, oneHoleBeyondPrefix_checked B,
      oneHoleBeyondPrefix_not_universal B⟩

/-- Specialized at the current strongest finite certificate threshold.  This
does not say anything about primes; it records that the `50000` certificate
still needs a genuine tail theorem. -/
theorem finitePrefixCheck50000_not_global :
    ∃ P : Nat → Prop,
      CheckedOnGoldbachPrefix 50000 P ∧ ¬ UniversalOnGoldbachDomain P :=
  finitePrefixCheck_not_global 50000

end FinitePrefixObstruction
end Gdbh
