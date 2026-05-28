import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Finite quotient obstruction

This file records a small formal obstruction for approaches that only use
finite quotient or modular pair-sum data.  It does not address the set of
primes.  Instead, it shows that even perfect pair-sum coverage in every
modulus up to a fixed finite bound is compatible with missing all sufficiently
large natural-number targets.

The point is methodological: a transfer step from finite quotient data to
global Goldbach representations needs genuinely infinite information.
-/

namespace Gdbh
namespace FiniteQuotientObstruction

/-- `PairSums A n` means that `n` is a sum of two elements of the finite set
`A`. -/
def PairSums (A : Finset Nat) (n : Nat) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- `A` covers every residue class modulo `m` by pair sums. -/
def ResiduePairCovers (m : Nat) (A : Finset Nat) : Prop :=
  ∀ r : ZMod m, ∃ a ∈ A, ∃ b ∈ A, ((a + b : Nat) : ZMod m) = r

/-- `A` covers pair sums modulo every positive modulus up to `K`. -/
def ResiduePairCoversUpTo (K : Nat) (A : Finset Nat) : Prop :=
  ∀ m : Nat, 0 < m → m ≤ K → ResiduePairCovers m A

/-- The interval `{0, ..., M}` has no pair sums above `2*M`. -/
theorem no_pairSums_range_above (M n : Nat) (hn : 2 * M < n) :
    ¬ PairSums (Finset.range (M + 1)) n := by
  rintro ⟨a, ha, b, hb, hsum⟩
  have ha_le : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb_le : b ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  omega

/-- If the interval `{0, ..., M}` is at least one complete residue system
modulo `m`, then its pair sums cover all residues modulo `m`. -/
theorem residuePairCovers_range_of_modulus_le
    (m M : Nat) [NeZero m] (hM : m ≤ M + 1) :
    ResiduePairCovers m (Finset.range (M + 1)) := by
  intro r
  refine ⟨r.val, ?_, 0, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    have hr : r.val < m := ZMod.val_lt r
    omega
  · simp
  · simp

/-- Positive-modulus wrapper for `residuePairCovers_range_of_modulus_le`. -/
theorem residuePairCovers_range_of_pos
    (m M : Nat) (hm : 0 < m) (hM : m ≤ M + 1) :
    ResiduePairCovers m (Finset.range (M + 1)) := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact residuePairCovers_range_of_modulus_le m M hM

/-- The interval `{0, ..., K}` has pair-sum coverage modulo every positive
modulus up to `K + 1`. -/
theorem residuePairCoversUpTo_range (K : Nat) :
    ResiduePairCoversUpTo (K + 1) (Finset.range (K + 1)) := by
  intro m hm hmK
  exact residuePairCovers_range_of_pos m K hm hmK

/-- A finite set can have full pair-sum coverage modulo `m` while still missing
every sufficiently large natural-number target. -/
theorem finiteQuotientCoverage_not_global
    (m M : Nat) (hm : 0 < m) (hM : m ≤ M + 1) :
    ResiduePairCovers m (Finset.range (M + 1)) ∧
      ∀ n : Nat, 2 * M < n → ¬ PairSums (Finset.range (M + 1)) n := by
  exact
    ⟨residuePairCovers_range_of_pos m M hm hM,
      fun n hn => no_pairSums_range_above M n hn⟩

/-- Finite quotient data up to any fixed bound does not force global pair-sum
coverage over `Nat`. -/
theorem finiteQuotientDataUpTo_not_global (K : Nat) :
    ResiduePairCoversUpTo (K + 1) (Finset.range (K + 1)) ∧
      ¬ (∀ n : Nat, PairSums (Finset.range (K + 1)) n) := by
  refine ⟨residuePairCoversUpTo_range K, ?_⟩
  intro hglobal
  exact no_pairSums_range_above K (2 * K + 1) (by omega) (hglobal (2 * K + 1))

end FiniteQuotientObstruction
end Gdbh
