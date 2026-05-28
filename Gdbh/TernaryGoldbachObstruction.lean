import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Ternary Goldbach shape obstruction

This file records a small modular obstruction for routes that try to use an
odd/ternary representation theorem as if it were a binary Goldbach theorem.
It is not a statement about primes.  It is a finite residue-class model showing
that ternary coverage of all odd residue classes can coexist with failure of
binary coverage of an even residue class.

The concrete model is modulo `8`: the allowed residues `{1, 3}` cover all odd
residues by sums of three allowed residues, but two allowed residues never sum
to `0` modulo `8`.
-/

namespace Gdbh
namespace TernaryGoldbachObstruction

/-- A finite set of residues covers each target residue by ternary sums
modulo `8`. -/
def TernaryCoversResidues (targets allowed : Finset Nat) : Prop :=
  ∀ r ∈ targets, ∃ a ∈ allowed, ∃ b ∈ allowed, ∃ c ∈ allowed,
    (a + b + c) % 8 = r % 8

/-- A finite set of residues covers each target residue by binary sums
modulo `8`. -/
def BinaryCoversResidues (targets allowed : Finset Nat) : Prop :=
  ∀ r ∈ targets, ∃ a ∈ allowed, ∃ b ∈ allowed, (a + b) % 8 = r % 8

/-- The odd residue classes modulo `8`, represented by least nonnegative
residues. -/
def OddResiduesMod8 : Finset Nat :=
  {1, 3, 5, 7}

/-- The even residue classes modulo `8`, represented by least nonnegative
residues. -/
def EvenResiduesMod8 : Finset Nat :=
  {0, 2, 4, 6}

/-- The toy allowed residue classes. -/
def ToyAllowedResidues : Finset Nat :=
  {1, 3}

/-- The toy residues `{1, 3}` cover every odd residue modulo `8` by ternary
sums. -/
theorem toyAllowedResidues_ternaryCoversOddResidues :
    TernaryCoversResidues OddResiduesMod8 ToyAllowedResidues := by
  intro r hr
  simp [OddResiduesMod8] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨3, by simp [ToyAllowedResidues], 3, by simp [ToyAllowedResidues],
      3, by simp [ToyAllowedResidues], ?_⟩
    norm_num
  · refine ⟨1, by simp [ToyAllowedResidues], 1, by simp [ToyAllowedResidues],
      1, by simp [ToyAllowedResidues], ?_⟩
    norm_num
  · refine ⟨1, by simp [ToyAllowedResidues], 1, by simp [ToyAllowedResidues],
      3, by simp [ToyAllowedResidues], ?_⟩
    norm_num
  · refine ⟨1, by simp [ToyAllowedResidues], 3, by simp [ToyAllowedResidues],
      3, by simp [ToyAllowedResidues], ?_⟩
    norm_num

/-- The toy residues `{1, 3}` do not cover residue `0` modulo `8` by binary
sums. -/
theorem toyAllowedResidues_not_binaryCoversResidueZero :
    ¬ (∃ a ∈ ToyAllowedResidues, ∃ b ∈ ToyAllowedResidues,
      (a + b) % 8 = 0) := by
  rintro ⟨a, ha, b, hb, hsum⟩
  simp [ToyAllowedResidues] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at hsum

/-- The toy residues `{1, 3}` therefore do not cover all even residues modulo
`8` by binary sums. -/
theorem toyAllowedResidues_not_binaryCoversEvenResidues :
    ¬ BinaryCoversResidues EvenResiduesMod8 ToyAllowedResidues := by
  intro hcover
  exact
    toyAllowedResidues_not_binaryCoversResidueZero
      (hcover 0 (by simp [EvenResiduesMod8]))

/-- Ternary coverage of all odd residue classes does not logically force
binary coverage of all even residue classes. -/
theorem ternaryOddResidueCoverage_not_force_binaryEvenResidueCoverage :
    ∃ allowed : Finset Nat,
      TernaryCoversResidues OddResiduesMod8 allowed ∧
        ¬ BinaryCoversResidues EvenResiduesMod8 allowed := by
  exact
    ⟨ToyAllowedResidues, toyAllowedResidues_ternaryCoversOddResidues,
      toyAllowedResidues_not_binaryCoversEvenResidues⟩

end TernaryGoldbachObstruction
end Gdbh
