import Mathlib.Tactic

/-!
# K-Goldbach shape obstruction

This file records a small predicate-generic obstruction behind the Path C
fallback distinction.  A bounded-list representation theorem, or a theorem
that allows `0`/`1` padding, is not by itself a binary two-core-summand theorem.

The examples below are not statements about primes.  They are logical models
showing that the representation shape and the allowed-summand predicate cannot
be weakened and then silently recovered.
-/

namespace Gdbh
namespace KGoldbachShapeObstruction

/-- The input domain of the binary Goldbach statement. -/
def GoldbachEvenDomain (n : Nat) : Prop :=
  4 ≤ n ∧ Even n

/-- The positive integers, matching the output domain of Schnirelmann's
half-density basis step. -/
def PositiveDomain (n : Nat) : Prop :=
  1 ≤ n

/-- `Allowed` represents every `Domain` input as a bounded list of summands. -/
def KSummandCoverageOn (Domain : Nat → Prop) (K : Nat)
    (Allowed : Nat → Prop) : Prop :=
  ∀ n : Nat, Domain n → ∃ ps : List Nat, ps.length ≤ K ∧
    (∀ p ∈ ps, Allowed p) ∧ ps.sum = n

/-- `Allowed` represents every `Domain` input as exactly a binary pair. -/
def BinaryPairCoverageOn (Domain : Nat → Prop) (Allowed : Nat → Prop) : Prop :=
  ∀ n : Nat, Domain n → ∃ p q : Nat, Allowed p ∧ Allowed q ∧ p + q = n

/-- `Allowed` represents every `Domain` input as a sum of two pair-sums.

This is the predicate-generic analogue of the Path C shape
`sumset (sumset Allowed Allowed) (sumset Allowed Allowed)`. -/
def TwoPairSumsetCoverageOn (Domain : Nat → Prop) (Allowed : Nat → Prop) :
    Prop :=
  ∀ n : Nat, Domain n →
    ∃ a b c d : Nat,
      Allowed a ∧ Allowed b ∧ Allowed c ∧ Allowed d ∧
        (a + b) + (c + d) = n

/-- A two-pair-sumset coverage theorem is, in particular, a four-summand
bounded-list coverage theorem. -/
theorem kSummandCoverage_four_of_twoPairSumsetCoverage
    {Domain : Nat → Prop} {Allowed : Nat → Prop}
    (h : TwoPairSumsetCoverageOn Domain Allowed) :
    KSummandCoverageOn Domain 4 Allowed := by
  intro n hn
  rcases h n hn with ⟨a, b, c, d, ha, hb, hc, hd, hsum⟩
  refine ⟨[a, b, c, d], ?_, ?_, ?_⟩
  · simp
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  · simp only [List.sum_cons, List.sum_nil]
    omega

/-- The padded predicate obtained by adjoining `0` and `1` to a core summand
predicate. -/
def PaddedAllowed (Core : Nat → Prop) (n : Nat) : Prop :=
  Core n ∨ n = 0 ∨ n = 1

/-- A deliberately broad core predicate used for shape counterexamples. -/
def LargeCore (n : Nat) : Prop :=
  4 ≤ n

/-- A second toy predicate: it is broad enough for two-pair-sumset coverage
on the Goldbach even domain, but still has a binary-pair hole at `6`. -/
def SmallLargeCore (n : Nat) : Prop :=
  n = 1 ∨ n = 2 ∨ 7 ≤ n

/-- A padding-aware toy predicate: it contains `0` and `1`, has exact
two-pair-sumset coverage of every positive integer, but still has a binary
hole at `6`. -/
def PaddedSmallLargeCore (n : Nat) : Prop :=
  n = 0 ∨ n = 1 ∨ n = 2 ∨ 7 ≤ n

/-- `LargeCore` gives one-summand coverage on the Goldbach even domain. -/
theorem largeCore_oneSummandCoverage :
    KSummandCoverageOn GoldbachEvenDomain 1 LargeCore := by
  intro n hn
  refine ⟨[n], by simp, ?_, by simp⟩
  intro p hp
  simp at hp
  subst hp
  exact hn.1

/-- The same one-term model gives bounded-list coverage for every
nonzero bound `K`. -/
theorem largeCore_kSummandCoverage_of_one_le (K : Nat) (hK : 1 ≤ K) :
    KSummandCoverageOn GoldbachEvenDomain K LargeCore := by
  intro n hn
  refine ⟨[n], by simpa using hK, ?_, by simp⟩
  intro p hp
  simp at hp
  subst hp
  exact hn.1

/-- `LargeCore` cannot represent `4` as a binary pair of core summands. -/
theorem largeCore_not_binaryPairCoverage :
    ¬ BinaryPairCoverageOn GoldbachEvenDomain LargeCore := by
  intro h
  rcases h 4 ⟨by norm_num, by norm_num⟩ with ⟨p, q, hp, hq, hsum⟩
  unfold LargeCore at hp hq
  omega

/-- Bounded-list coverage does not logically force binary-pair coverage. -/
theorem kSummandCoverage_not_force_binaryPairCoverage :
    ∃ Allowed : Nat → Prop,
      KSummandCoverageOn GoldbachEvenDomain 1 Allowed ∧
        ¬ BinaryPairCoverageOn GoldbachEvenDomain Allowed := by
  exact
    ⟨LargeCore, largeCore_oneSummandCoverage,
      largeCore_not_binaryPairCoverage⟩

/-- For every nonzero list bound `K`, `K`-summand coverage still does not
logically force binary-pair coverage. -/
theorem kSummandCoverage_not_force_binaryPairCoverage_of_one_le
    (K : Nat) (hK : 1 ≤ K) :
    ∃ Allowed : Nat → Prop,
      KSummandCoverageOn GoldbachEvenDomain K Allowed ∧
        ¬ BinaryPairCoverageOn GoldbachEvenDomain Allowed := by
  exact
    ⟨LargeCore, largeCore_kSummandCoverage_of_one_le K hK,
      largeCore_not_binaryPairCoverage⟩

/-- In particular, a six-summand coverage statement has the wrong logical
shape for a binary two-summand conclusion. -/
theorem sixSummandCoverage_not_force_binaryPairCoverage :
    ∃ Allowed : Nat → Prop,
      KSummandCoverageOn GoldbachEvenDomain 6 Allowed ∧
        ¬ BinaryPairCoverageOn GoldbachEvenDomain Allowed := by
  exact kSummandCoverage_not_force_binaryPairCoverage_of_one_le 6 (by norm_num)

/-- The toy predicate `SmallLargeCore` has two-pair-sumset coverage on the
Goldbach even domain.  Small inputs use `1` and `2`; all larger even inputs use
`1 + 1 + 1 + (n - 3)`. -/
theorem smallLargeCore_twoPairSumsetCoverage :
    TwoPairSumsetCoverageOn GoldbachEvenDomain SmallLargeCore := by
  intro n hn
  rcases hn.2 with ⟨k, rfl⟩
  have hk2 : 2 ≤ k := by
    have h4 : 4 ≤ k + k := hn.1
    omega
  by_cases hk_lt : k < 5
  · interval_cases k
    · refine ⟨1, 1, 1, 1, ?_, ?_, ?_, ?_, by norm_num⟩ <;>
        exact Or.inl rfl
    · refine ⟨2, 2, 1, 1, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inl rfl
    · refine ⟨2, 2, 2, 2, ?_, ?_, ?_, ?_, by norm_num⟩ <;>
        exact Or.inr (Or.inl rfl)
  · refine ⟨1, 1, 1, k + k - 3, ?_, ?_, ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by omega))
    · omega

/-- `SmallLargeCore` cannot represent `6` as a binary pair of allowed
summands. -/
theorem smallLargeCore_not_binaryPairCoverage :
    ¬ BinaryPairCoverageOn GoldbachEvenDomain SmallLargeCore := by
  intro h
  rcases h 6 ⟨by norm_num, by norm_num⟩ with ⟨p, q, hp, hq, hsum⟩
  unfold SmallLargeCore at hp hq
  rcases hp with rfl | rfl | hp7 <;>
    rcases hq with rfl | rfl | hq7 <;>
      omega

/-- Even the exact two-pair-sumset shape produced by applying a basis theorem
to a pair-sumset does not logically force binary-pair coverage. -/
theorem twoPairSumsetCoverage_not_force_binaryPairCoverage :
    ∃ Allowed : Nat → Prop,
      TwoPairSumsetCoverageOn GoldbachEvenDomain Allowed ∧
        ¬ BinaryPairCoverageOn GoldbachEvenDomain Allowed := by
  exact
    ⟨SmallLargeCore, smallLargeCore_twoPairSumsetCoverage,
      smallLargeCore_not_binaryPairCoverage⟩

/-- `PaddedSmallLargeCore` has exact two-pair-sumset coverage of every
positive integer.  The six small positive values are handled explicitly; from
`7` onward, use `0 + 0 + 0 + n`. -/
theorem paddedSmallLargeCore_twoPairSumsetCoverage_positive :
    TwoPairSumsetCoverageOn PositiveDomain PaddedSmallLargeCore := by
  intro n hn
  unfold PositiveDomain at hn
  by_cases hn_lt : n < 7
  · interval_cases n
    · refine ⟨0, 0, 0, 1, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · refine ⟨0, 0, 0, 2, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · refine ⟨0, 0, 1, 2, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · refine ⟨0, 0, 2, 2, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
    · refine ⟨0, 1, 2, 2, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
    · refine ⟨1, 1, 2, 2, ?_, ?_, ?_, ?_, by norm_num⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
  · refine ⟨0, 0, 0, n, ?_, ?_, ?_, ?_, by omega⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- `PaddedSmallLargeCore` still cannot represent `6` as a binary pair. -/
theorem paddedSmallLargeCore_not_binaryPairCoverage :
    ¬ BinaryPairCoverageOn GoldbachEvenDomain PaddedSmallLargeCore := by
  intro h
  rcases h 6 ⟨by norm_num, by norm_num⟩ with ⟨p, q, hp, hq, hsum⟩
  unfold PaddedSmallLargeCore at hp hq
  rcases hp with rfl | rfl | rfl | hp7 <;>
    rcases hq with rfl | rfl | rfl | hq7 <;>
      omega

/-- Even positive-integer two-pair-sumset coverage for a predicate containing
`0` and `1` does not logically force binary-pair coverage on the Goldbach even
domain.  This is the predicate-generic shape of the half-density
`primesSumset` handoff. -/
theorem positiveTwoPairSumsetCoverage_with_zero_one_not_force_binaryPairCoverage :
    ∃ Allowed : Nat → Prop,
      Allowed 0 ∧ Allowed 1 ∧
        TwoPairSumsetCoverageOn PositiveDomain Allowed ∧
          ¬ BinaryPairCoverageOn GoldbachEvenDomain Allowed := by
  exact
    ⟨PaddedSmallLargeCore, Or.inl rfl, Or.inr (Or.inl rfl),
      paddedSmallLargeCore_twoPairSumsetCoverage_positive,
      paddedSmallLargeCore_not_binaryPairCoverage⟩

/-- With `0` padding, `LargeCore` has binary-pair coverage by writing
`n = 0 + n`. -/
theorem paddedLargeCore_binaryPairCoverage :
    BinaryPairCoverageOn GoldbachEvenDomain (PaddedAllowed LargeCore) := by
  intro n hn
  refine ⟨0, n, ?_, ?_, by simp⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl hn.1

/-- Binary-pair coverage for a padded predicate does not logically force
binary-pair coverage for the unpadded core predicate. -/
theorem paddedPairCoverage_not_force_coreBinaryPairCoverage :
    ∃ Core : Nat → Prop,
      BinaryPairCoverageOn GoldbachEvenDomain (PaddedAllowed Core) ∧
        ¬ BinaryPairCoverageOn GoldbachEvenDomain Core := by
  exact
    ⟨LargeCore, paddedLargeCore_binaryPairCoverage,
      largeCore_not_binaryPairCoverage⟩

end KGoldbachShapeObstruction
end Gdbh
