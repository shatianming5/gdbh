import Gdbh.Round1Status
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.PrimeCounting

/-!
# Counterexample reduction for the current tail target

This file repackages the remaining `ExplicitGoldbachLowerBound 50000` target as
a no-counterexample statement.  It does not prove Goldbach; it exposes the exact
minimal-counterexample interface that any tail argument must rule out.
-/

namespace Gdbh
namespace CounterexampleReduction

/-- A counterexample to the count-positive tail above `B`. -/
def GoldbachCounterexampleAbove (B n : Nat) : Prop :=
  B < n ∧ Even n ∧ GoldbachCount n = 0

/-- A representation-shaped counterexample above `B`.  This is the same
condition as `GoldbachCounterexampleAbove`, stated with the project-level
`GoldbachRepresentation` predicate rather than the counting predicate. -/
def GoldbachRepresentationCounterexampleAbove (B n : Nat) : Prop :=
  B < n ∧ Even n ∧ ¬ GoldbachRepresentation n

/-- A literal counterexample to the binary Goldbach statement in `goal.md`. -/
def BinaryGoldbachCounterexample (n : Nat) : Prop :=
  4 ≤ n ∧ Even n ∧ ¬ GoldbachRepresentation n

/-- A lower-half prime-complement Goldbach witness.  By symmetry of `p + q`,
any Goldbach representation may be taken with the first prime at most
`n / 2`. -/
def GoldbachHalfWitness (n : Nat) : Prop :=
  ∃ p : Nat, p ≤ n / 2 ∧ Nat.Prime p ∧ Nat.Prime (n - p)

/-- A lower-half witness target above a threshold. -/
def GoldbachHalfWitnessLowerBound (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n → GoldbachHalfWitness n

/-- A lower-half witness counterexample above a threshold. -/
def GoldbachHalfWitnessCounterexampleAbove (B n : Nat) : Prop :=
  B < n ∧ Even n ∧ ¬ GoldbachHalfWitness n

/-- A minimal literal binary counterexample, packaged in the form useful for
descent or induction arguments: `m` is a binary Goldbach counterexample beyond
the current finite certificate, and every smaller even number in the `goal.md`
range already has a Goldbach representation. -/
def MinimalBinaryGoldbachCounterexample (m : Nat) : Prop :=
  BinaryGoldbachCounterexample m ∧
    50000 < m ∧
      ∀ n : Nat, n < m → 4 ≤ n → Even n → GoldbachRepresentation n

/-- The descent obligation for a minimal-counterexample proof: from any
induction-ready minimal binary counterexample, construct a smaller literal
binary counterexample.  This is not proved here; the theorems below show that
this is exactly the kind of infinite descent step that would close the current
tail target. -/
def MinimalBinaryCounterexampleDescent : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ n : Nat, n < m ∧ BinaryGoldbachCounterexample n

/-- The sieve-shaped cover forced by a lower-half witness counterexample:
every lower-half prime `p` has a genuinely composite complement `m - p`, and
therefore some proper prime divisor of that complement. -/
def LowerHalfPrimeComplementDivisorCover (m : Nat) : Prop :=
  ∀ p : Nat, p ≤ m / 2 → Nat.Prime p →
    ∃ r : Nat, Nat.Prime r ∧ r ∣ m - p ∧ r < m - p

/-- The same forced cover in residue language: every lower-half prime `p`
lies in the residue class `m` modulo a proper prime divisor of its complement.
This is the form closest to covering-sieve or CRT arguments. -/
def LowerHalfPrimeComplementResidueCover (m : Nat) : Prop :=
  ∀ p : Nat, p ≤ m / 2 → Nat.Prime p →
    ∃ r : Nat, Nat.Prime r ∧ r < m - p ∧ p ≡ m [MOD r]

/-- The finite universe of prime moduli below a candidate counterexample. -/
def PrimeModuliBelow (m : Nat) : Finset Nat :=
  (Finset.range m).filter Nat.Prime

/-- The finite set of lower-half primes for a candidate counterexample. -/
def LowerHalfPrimes (m : Nat) : Finset Nat :=
  (Finset.range (m / 2 + 1)).filter Nat.Prime

/-- A finite-universe version of the residue cover: all covering moduli are
drawn from the finite set of primes below `m`.  The strict `r < m - p`
condition is retained, so this still says every complement is genuinely
composite rather than merely congruent to `0` modulo itself. -/
def LowerHalfPrimeComplementFiniteResidueCover (m : Nat) : Prop :=
  ∀ p : Nat, p ≤ m / 2 → Nat.Prime p →
    ∃ r : Nat, r ∈ PrimeModuliBelow m ∧ r < m - p ∧ p ≡ m [MOD r]

/-- A lower-half prime that escapes every finite bad congruence class forced
by proper prime divisors.  Such a `p` has no proper prime divisor of
`m - p`, and therefore turns into a Goldbach half-witness. -/
def LowerHalfPrimeFiniteResidueEscape (m : Nat) : Prop :=
  ∃ p : Nat, p ≤ m / 2 ∧ Nat.Prime p ∧
    ∀ r : Nat, r ∈ PrimeModuliBelow m → r < m - p →
      ¬ p ≡ m [MOD r]

/-- Lower-half primes lying in one finite bad residue class. -/
def BadLowerHalfPrimeResidueClass (m r : Nat) : Finset Nat :=
  (LowerHalfPrimes m).filter (fun p => r < m - p ∧ p ≡ m [MOD r])

/-- The finite set of lower-half primes covered by at least one finite bad
residue class. -/
def BadLowerHalfPrimes (m : Nat) : Finset Nat :=
  (PrimeModuliBelow m).biUnion (BadLowerHalfPrimeResidueClass m)

/-- A finite cardinality surplus criterion: there are more lower-half primes
than lower-half primes covered by the finite bad residue classes.  Proving this
for every alleged minimal counterexample would give an escaping prime. -/
def LowerHalfPrimeResidueSurplus (m : Nat) : Prop :=
  (BadLowerHalfPrimes m).card < (LowerHalfPrimes m).card

/-- The sum of the sizes of all finite bad residue classes.  This is the
standard union-bound majorant for `BadLowerHalfPrimes m`. -/
def BadLowerHalfPrimeResidueClassCardSum (m : Nat) : Nat :=
  (PrimeModuliBelow m).sum fun r => (BadLowerHalfPrimeResidueClass m r).card

/-- A union-bound version of the finite cardinality-surplus criterion: even
the sum of the individual bad residue class sizes is smaller than the number
of lower-half primes. -/
def LowerHalfPrimeResidueUnionBoundSurplus (m : Nat) : Prop :=
  BadLowerHalfPrimeResidueClassCardSum m < (LowerHalfPrimes m).card

/-- The prime moduli below `m`, restricted to the small-modulus range
`r ≤ R`. -/
def PrimeModuliBelowAtMost (m R : Nat) : Finset Nat :=
  (PrimeModuliBelow m).filter fun r => r ≤ R

/-- The prime moduli below `m`, restricted to the large-modulus range
`R < r`. -/
def PrimeModuliBelowAbove (m R : Nat) : Finset Nat :=
  (PrimeModuliBelow m).filter fun r => R < r

/-- Lower-half primes covered by bad residue classes with small moduli. -/
def BadLowerHalfPrimesSmallModuli (m R : Nat) : Finset Nat :=
  (PrimeModuliBelowAtMost m R).biUnion (BadLowerHalfPrimeResidueClass m)

/-- Lower-half primes covered by bad residue classes with large moduli. -/
def BadLowerHalfPrimesLargeModuli (m R : Nat) : Finset Nat :=
  (PrimeModuliBelowAbove m R).biUnion (BadLowerHalfPrimeResidueClass m)

/-- The union-bound majorant using only the small-modulus bad residue
classes. -/
def BadLowerHalfPrimeSmallResidueClassCardSum (m R : Nat) : Nat :=
  (PrimeModuliBelowAtMost m R).sum fun r =>
    (BadLowerHalfPrimeResidueClass m r).card

/-- A point-counting majorant for the small-modulus bad residue classes:
inside `0 ≤ p ≤ m / 2`, a fixed residue class modulo `r` has at most
`m / 2 / r + 1` elements. -/
def BadLowerHalfPrimeSmallResidueClassPointBoundSum (m R : Nat) : Nat :=
  (PrimeModuliBelowAtMost m R).sum fun r => m / 2 / r + 1

/-- A parity-aware point-counting majorant for the small-modulus bad residue
classes.  The modulus `2` is kept separate: for an even counterexample, the
bad class modulo `2` contains at most the single prime `2`, while the remaining
odd prime moduli use the generic residue-class point bound
`m / 2 / r + 1`. -/
def BadLowerHalfPrimeSmallResidueClassParityPointBoundSum (m R : Nat) : Nat :=
  (if 2 ∈ PrimeModuliBelowAtMost m R then 1 else 0) +
    ((PrimeModuliBelowAtMost m R).erase 2).sum fun r => m / 2 / r + 1

/-- A split finite cardinality-surplus criterion: after choosing a threshold
`R`, the small-modulus covered set plus the large-modulus covered set is still
smaller than the full lower-half prime set. -/
def LowerHalfPrimeResidueSplitSurplus (m R : Nat) : Prop :=
  (BadLowerHalfPrimesSmallModuli m R).card +
      (BadLowerHalfPrimesLargeModuli m R).card <
    (LowerHalfPrimes m).card

/-- A split criterion in the form used by a future two-range sieve: the small
moduli are bounded by the sum of their residue-class sizes, while the large
moduli remain as an exact covered set to be controlled separately. -/
def LowerHalfPrimeResidueSmallUnionBoundSplitSurplus
    (m R : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m R +
      (BadLowerHalfPrimesLargeModuli m R).card <
    (LowerHalfPrimes m).card

/-- Cofactor witnesses for the large-modulus bad set: a pair `(r, k)` records
that the complement has the shape `m - p = r * k`, with `r` a large prime
modulus and `k ≥ 2`, and recovers the lower-half prime as `p = m - r * k`. -/
def LargeBadLowerHalfPrimeCofactorPairs (m R : Nat) :
    Finset (Nat × Nat) :=
  ((PrimeModuliBelowAbove m R).product (Finset.range (m + 1))).filter
    fun rk => 2 ≤ rk.2 ∧ m - rk.1 * rk.2 ∈ LowerHalfPrimes m

/-- The lower-half primes recovered from large-modulus cofactor witnesses. -/
def LargeBadLowerHalfPrimeCofactorImage (m R : Nat) : Finset Nat :=
  (LargeBadLowerHalfPrimeCofactorPairs m R).image
    fun rk => m - rk.1 * rk.2

/-- The same cofactor witnesses with the divisor-size consequence of
`R < r` built into the finite universe: since `m - p = r * k` and `R < r`,
the cofactor satisfies `k ≤ m / (R + 1)`. -/
def LargeBadLowerHalfPrimeBoundedCofactorPairs (m R : Nat) :
    Finset (Nat × Nat) :=
  ((PrimeModuliBelowAbove m R).product
      (Finset.range (m / (R + 1) + 1))).filter
    fun rk => 2 ≤ rk.2 ∧ m - rk.1 * rk.2 ∈ LowerHalfPrimes m

/-- The rectangular cofactor box containing all intrinsically bounded
large-modulus cofactor witnesses: `r` is a large prime modulus and the
cofactor satisfies `2 ≤ k ≤ m / (R + 1)`. -/
def LargeBadLowerHalfPrimeCofactorBox (m R : Nat) :
    Finset (Nat × Nat) :=
  (PrimeModuliBelowAbove m R).product (Finset.Icc 2 (m / (R + 1)))

/-- A split criterion that bounds the small moduli by a union-bound sum and
bounds the large-modulus covered set by cofactor-witness pairs. -/
def LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus
    (m R : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m R +
      (LargeBadLowerHalfPrimeCofactorPairs m R).card <
    (LowerHalfPrimes m).card

/-- A still sharper cofactor split criterion, using the intrinsic bound
`k ≤ m / (R + 1)` for large-modulus cofactors. -/
def LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
    (m R : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m R +
      (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card <
    (LowerHalfPrimes m).card

/-- A cruder but explicit rectangular-box cofactor split criterion: after
bounding large-modulus cofactor witnesses by the box
`r ∈ PrimeModuliBelowAbove m R`, `2 ≤ k ≤ m / (R + 1)`, it remains enough for
that product bound plus the small-modulus union-bound sum to be below the
lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus
    (m R : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m R +
      (PrimeModuliBelowAbove m R).card *
        (Finset.Icc 2 (m / (R + 1))).card <
    (LowerHalfPrimes m).card

/-- The same cofactor-box criterion with the interval cardinality simplified:
`#Icc 2 (m / (R + 1)) = m / (R + 1) - 1`. -/
def LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
    (m R : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m R +
      (PrimeModuliBelowAbove m R).card *
        (m / (R + 1) - 1) <
    (LowerHalfPrimes m).card

/-- The cofactor-box product criterion with the large-prime modulus count
rewritten as a prime-counting window.  The side condition `R < m` keeps the
window `π(m - 1) - π(R)` definitionally aligned with
`PrimeModuliBelowAbove m R`. -/
def LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
    (m R : Nat) : Prop :=
  R < m ∧
    BadLowerHalfPrimeSmallResidueClassCardSum m R +
        (Nat.primeCounting (m - 1) - Nat.primeCounting R) *
          (m / (R + 1) - 1) <
      (LowerHalfPrimes m).card

/-- The prime-counting window criterion with the lower-half prime count also
rewritten as `π(m / 2)`.  This is the same arithmetic handoff as the previous
criterion, but with the large-modulus count and the lower-half prime target
both expressed using `Nat.primeCounting`. -/
def LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
    (m R : Nat) : Prop :=
  R < m ∧
    BadLowerHalfPrimeSmallResidueClassCardSum m R +
        (Nat.primeCounting (m - 1) - Nat.primeCounting R) *
          (m / (R + 1) - 1) <
      Nat.primeCounting (m / 2)

/-- A fully arithmetic prime-counting split criterion whose small-modulus
contribution is bounded by the elementary point count
`Σ_{r ≤ R} (m / 2 / r + 1)` over prime moduli below `m`. -/
def LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
    (m R : Nat) : Prop :=
  R < m ∧
    BadLowerHalfPrimeSmallResidueClassPointBoundSum m R +
        (Nat.primeCounting (m - 1) - Nat.primeCounting R) *
          (m / (R + 1) - 1) <
      Nat.primeCounting (m / 2)

/-- A parity-aware replacement for the dead-end point-bound criterion.  It
requires `m` to be even, treats the modulus `2` by the sharp one-point bound,
and applies the generic point bound only to the remaining small prime moduli. -/
def LowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (m R : Nat) : Prop :=
  Even m ∧ R < m ∧
    BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R +
        (Nat.primeCounting (m - 1) - Nat.primeCounting R) *
          (m / (R + 1) - 1) <
      Nat.primeCounting (m / 2)

/-- The future sieve obligation dual to the finite-cover package: every
induction-ready minimal counterexample should contain a lower-half prime that
escapes all finite bad congruence classes. -/
def MinimalCounterexampleFiniteResidueEscape : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeFiniteResidueEscape m

/-- A stronger future sieve obligation: every induction-ready minimal
counterexample has a strict finite cardinality surplus of lower-half primes
over the lower-half primes covered by bad residue classes. -/
def MinimalCounterexampleFiniteResidueSurplus : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSurplus m

/-- A still stronger future sieve obligation: every induction-ready minimal
counterexample has a strict union-bound surplus. -/
def MinimalCounterexampleFiniteResidueUnionBoundSurplus : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueUnionBoundSurplus m

/-- A future two-range sieve obligation: every induction-ready minimal
counterexample admits some modulus threshold with a strict split surplus. -/
def MinimalCounterexampleFiniteResidueSplitSurplus : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat, LowerHalfPrimeResidueSplitSurplus m R

/-- A stronger two-range sieve obligation: the small moduli may be handled by
a union bound, while the large-modulus covered set is left exact. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat, LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R

/-- A still more arithmetic two-range obligation: the small moduli are handled
by a union bound, and the large-modulus contribution is bounded by explicit
complement cofactor pairs. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R

/-- The bounded cofactor version of the two-range obligation.  This exposes
the finite search space a future large-modulus estimate should control:
`r > R`, `k ≤ m / (R + 1)`, and `m - r * k` a lower-half prime. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus m R

/-- The cofactor-box version of the two-range obligation.  This replaces the
large-modulus exact cofactor-pair count by the rectangular cardinality
`#PrimeModuliBelowAbove m R * #Icc 2 (m / (R + 1))`. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R

/-- The cofactor-box product version of the two-range obligation, using the
pure natural-number factor `m / (R + 1) - 1` for the cofactor interval length. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus m R

/-- The cofactor-box product two-range obligation with the side condition
`R < m` made explicit.  This is the exact non-prime-counting form of the
prime-counting-window obligation. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      R < m ∧
        LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
          m R

/-- The prime-counting window version of the two-range obligation.  This
keeps the same cofactor-box product handoff, but records the large-modulus
range as `π(m - 1) - π(R)` and requires `R < m`. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R

/-- The full prime-counting version of the two-range obligation, with the
large-modulus count written as `π(m - 1) - π(R)` and the lower-half prime count
written as `π(m / 2)`. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
        m R

/-- The point-bound full prime-counting version of the two-range obligation:
for every induction-ready minimal counterexample, some threshold `R` makes
the elementary small-modulus point bound plus the large-modulus
prime-counting cofactor window smaller than `π(m / 2)`. -/
def MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
        m R

/-- The parity-aware point-bound full prime-counting version of the two-range
obligation: every induction-ready minimal counterexample should admit a
threshold `R` for which the sharp `r = 2` contribution plus the generic odd
prime-modulus point bound and the large-modulus prime-counting cofactor window
are smaller than `π(m / 2)`. -/
def MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    ∃ R : Nat,
      LowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
        m R

/-- A minimal counterexample packaged together with its forced lower-half
prime-complement divisor cover.  This is an exact restatement of the minimal
counterexample route, but in the shape a future sieve/covering argument would
need to refute. -/
def MinimalCounterexamplePrimeDivisorCover (m : Nat) : Prop :=
  MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeComplementDivisorCover m

/-- A minimal counterexample packaged with the same forced cover, stated as
residue classes modulo proper prime divisors of the lower-half complements. -/
def MinimalCounterexamplePrimeResidueCover (m : Nat) : Prop :=
  MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeComplementResidueCover m

/-- A minimal counterexample packaged with the finite-universe version of the
forced prime-residue cover. -/
def MinimalCounterexampleFinitePrimeResidueCover (m : Nat) : Prop :=
  MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeComplementFiniteResidueCover m

/-- The count-zero and representation-failure counterexample predicates are
equivalent pointwise. -/
theorem counterexampleAbove_iff_representationCounterexampleAbove
    {B n : Nat} :
    GoldbachCounterexampleAbove B n ↔
      GoldbachRepresentationCounterexampleAbove B n := by
  constructor
  · intro h
    rcases h with ⟨hnB, hnEven, hzero⟩
    refine ⟨hnB, hnEven, ?_⟩
    intro representation
    have hpos : 0 < GoldbachCount n :=
      goldbachCount_pos_of_representation representation
    omega
  · intro h
    rcases h with ⟨hnB, hnEven, hnot⟩
    refine ⟨hnB, hnEven, ?_⟩
    rcases Nat.eq_zero_or_pos (GoldbachCount n) with hzero | hpos
    · exact hzero
    · exact False.elim (hnot (goldbachRepresentation_of_count_pos hpos))

/-- Goldbach representations are equivalent to lower-half prime-complement
witnesses. -/
theorem goldbachRepresentation_iff_halfWitness {n : Nat} :
    GoldbachRepresentation n ↔ GoldbachHalfWitness n := by
  constructor
  · intro h
    rcases h with ⟨p, q, hp, hq, hsum⟩
    by_cases hpq : p ≤ q
    · have htwo : p * 2 ≤ n := by omega
      have hp_half : p ≤ n / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr htwo
      have hsub : n - p = q := by
        rw [← hsum]
        exact Nat.add_sub_cancel_left p q
      exact ⟨p, hp_half, hp, by simpa [hsub] using hq⟩
    · have hqp : q ≤ p := le_of_not_ge hpq
      have htwo : q * 2 ≤ n := by omega
      have hq_half : q ≤ n / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr htwo
      have hsub : n - q = p := by
        rw [← hsum]
        exact Nat.add_sub_cancel_right p q
      exact ⟨q, hq_half, hq, by simpa [hsub] using hp⟩
  · intro h
    rcases h with ⟨p, hp_half, hp, hq⟩
    have hp_le : p ≤ n :=
      le_trans hp_half (Nat.div_le_self n 2)
    exact goldbachRepresentation_of_prime_sub hp hq hp_le

/-- The explicit lower-bound target above `B` can be stated using lower-half
prime-complement witnesses. -/
theorem explicitLowerBound_iff_halfWitnessLowerBound (B : Nat) :
    ExplicitGoldbachLowerBound B ↔ GoldbachHalfWitnessLowerBound B := by
  constructor
  · intro lower_bound n hnB hnEven
    exact goldbachRepresentation_iff_halfWitness.mp
      (goldbachRepresentation_of_count_pos (lower_bound n hnB hnEven))
  · intro half_bound n hnB hnEven
    exact goldbachCount_pos_of_representation
      (goldbachRepresentation_iff_halfWitness.mpr
        (half_bound n hnB hnEven))

/-- Representation-shaped and lower-half-witness counterexamples are the same
pointwise. -/
theorem representationCounterexampleAbove_iff_halfWitnessCounterexampleAbove
    {B n : Nat} :
    GoldbachRepresentationCounterexampleAbove B n ↔
      GoldbachHalfWitnessCounterexampleAbove B n := by
  constructor
  · intro h
    rcases h with ⟨hnB, hnEven, hnot⟩
    exact ⟨hnB, hnEven, fun hhalf =>
      hnot (goldbachRepresentation_iff_halfWitness.mpr hhalf)⟩
  · intro h
    rcases h with ⟨hnB, hnEven, hnot⟩
    exact ⟨hnB, hnEven, fun hrep =>
      hnot (goldbachRepresentation_iff_halfWitness.mp hrep)⟩

/-- The exact binary Goldbach statement is equivalent to having no literal
binary counterexample. -/
theorem binaryGoldbachConjecture_iff_no_binary_counterexample :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ n : Nat, BinaryGoldbachCounterexample n := by
  constructor
  · intro h counter
    rcases counter with ⟨n, hn4, hnEven, hnot⟩
    exact hnot (h n hn4 hnEven)
  · intro no_counter n hn4 hnEven
    by_contra hnot
    exact no_counter ⟨n, hn4, hnEven, hnot⟩

/-- Failure of the exact binary Goldbach statement is equivalent to existence
of a literal binary counterexample. -/
theorem not_binaryGoldbachConjecture_iff_exists_binary_counterexample :
    ¬ Round1Status.BinaryGoldbachConjecture ↔
      ∃ n : Nat, BinaryGoldbachCounterexample n := by
  constructor
  · intro h
    by_contra no_counter
    exact h (binaryGoldbachConjecture_iff_no_binary_counterexample.mpr no_counter)
  · intro counter h
    exact (binaryGoldbachConjecture_iff_no_binary_counterexample.mp h) counter

/-- The current finite certificate rules out all literal binary
counterexamples at or below `50000`. -/
theorem not_binaryCounterexample_of_le50000 {n : Nat}
    (hnle : n ≤ 50000) :
    ¬ BinaryGoldbachCounterexample n := by
  intro h
  rcases h with ⟨hn4, hnEven, hnot⟩
  have hn2 : 2 < n := by omega
  exact hnot
    (goldbachUpTo50000_of_chunkedCertificate2To50000 n hn2 hnle hnEven)

/-- Therefore every literal binary counterexample, if one exists, lies beyond
the current `50000` finite certificate. -/
theorem binaryCounterexample_gt50000 {n : Nat}
    (h : BinaryGoldbachCounterexample n) :
    50000 < n := by
  by_contra hnot
  exact not_binaryCounterexample_of_le50000 (Nat.le_of_not_gt hnot) h

/-- After the current finite certificate, literal binary counterexamples are
exactly representation-shaped tail counterexamples above `50000`. -/
theorem binaryCounterexample_iff_representationCounterexampleAbove50000
    {n : Nat} :
    BinaryGoldbachCounterexample n ↔
      GoldbachRepresentationCounterexampleAbove 50000 n := by
  constructor
  · intro h
    exact ⟨binaryCounterexample_gt50000 h, h.2.1, h.2.2⟩
  · intro h
    have hn50000 : 50000 < n := h.1
    exact ⟨by omega, h.2.1, h.2.2⟩

/-- Existence of a literal binary counterexample is therefore equivalent to
existence of a representation-shaped tail counterexample above `50000`. -/
theorem exists_binary_counterexample_iff_exists_representationCounterexampleAbove50000 :
    (∃ n : Nat, BinaryGoldbachCounterexample n) ↔
      ∃ n : Nat, GoldbachRepresentationCounterexampleAbove 50000 n := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    exact ⟨n, binaryCounterexample_iff_representationCounterexampleAbove50000.mp hn⟩
  · intro h
    rcases h with ⟨n, hn⟩
    exact ⟨n, binaryCounterexample_iff_representationCounterexampleAbove50000.mpr hn⟩

/-- The explicit lower-bound target above `B` is exactly the assertion that
there is no count-zero even input above `B`. -/
theorem explicitLowerBound_iff_no_counterexample_above (B : Nat) :
    ExplicitGoldbachLowerBound B ↔
      ¬ ∃ n : Nat, GoldbachCounterexampleAbove B n := by
  constructor
  · intro lower_bound counter
    rcases counter with ⟨n, hnB, hnEven, hzero⟩
    have hpos : 0 < GoldbachCount n := lower_bound n hnB hnEven
    omega
  · intro no_counter n hnB hnEven
    rcases Nat.eq_zero_or_pos (GoldbachCount n) with hzero | hpos
    · exfalso
      exact no_counter ⟨n, hnB, hnEven, hzero⟩
    · exact hpos

/-- Failure of the explicit lower-bound target is equivalent to an actual
count-zero counterexample above the same threshold. -/
theorem not_explicitLowerBound_iff_exists_counterexample_above (B : Nat) :
    ¬ ExplicitGoldbachLowerBound B ↔
      ∃ n : Nat, GoldbachCounterexampleAbove B n := by
  constructor
  · intro h
    by_contra no_counter
    exact h ((explicitLowerBound_iff_no_counterexample_above B).mpr no_counter)
  · intro counter lower_bound
    exact (explicitLowerBound_iff_no_counterexample_above B).mp lower_bound counter

/-- The explicit lower-bound target above `B` is also exactly the assertion
that there is no representation-shaped counterexample above `B`. -/
theorem explicitLowerBound_iff_no_representation_counterexample_above
    (B : Nat) :
    ExplicitGoldbachLowerBound B ↔
      ¬ ∃ n : Nat, GoldbachRepresentationCounterexampleAbove B n := by
  constructor
  · intro lower_bound h
    rcases h with ⟨n, hn⟩
    exact
      (explicitLowerBound_iff_no_counterexample_above B).mp lower_bound
        ⟨n, (counterexampleAbove_iff_representationCounterexampleAbove.mpr hn)⟩
  · intro no_counter
    exact
      (explicitLowerBound_iff_no_counterexample_above B).mpr
        (by
          intro h
          rcases h with ⟨n, hn⟩
          exact no_counter
            ⟨n, (counterexampleAbove_iff_representationCounterexampleAbove.mp hn)⟩)

/-- The explicit lower-bound target above `B` is equivalently the absence of
lower-half-witness counterexamples above `B`. -/
theorem explicitLowerBound_iff_no_halfWitnessCounterexample_above
    (B : Nat) :
    ExplicitGoldbachLowerBound B ↔
      ¬ ∃ n : Nat, GoldbachHalfWitnessCounterexampleAbove B n := by
  constructor
  · intro lower_bound h
    rcases h with ⟨n, hn⟩
    exact
      (explicitLowerBound_iff_no_representation_counterexample_above B).mp
        lower_bound
        ⟨n, (representationCounterexampleAbove_iff_halfWitnessCounterexampleAbove.mpr hn)⟩
  · intro no_counter
    exact
      (explicitLowerBound_iff_no_representation_counterexample_above B).mpr
        (by
          intro h
          rcases h with ⟨n, hn⟩
          exact no_counter
            ⟨n, (representationCounterexampleAbove_iff_halfWitnessCounterexampleAbove.mp hn)⟩)

/-- The current status target is equivalent to having no counterexample above
the `50000` certificate threshold. -/
theorem currentFormalTarget50000_iff_no_counterexample_above :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ n : Nat, GoldbachCounterexampleAbove 50000 n := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound_iff_no_counterexample_above 50000

/-- The exact `goal.md` statement is equivalent to ruling out all
counterexamples above the current `50000` finite certificate. -/
theorem binaryGoldbachConjecture_iff_no_counterexample_above50000 :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ n : Nat, GoldbachCounterexampleAbove 50000 n :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.trans
    currentFormalTarget50000_iff_no_counterexample_above

/-- The current status target is equivalent to having no
representation-shaped counterexample above the `50000` certificate threshold. -/
theorem currentFormalTarget50000_iff_no_representation_counterexample_above :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ n : Nat,
        GoldbachRepresentationCounterexampleAbove 50000 n := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound_iff_no_representation_counterexample_above 50000

/-- The current status target is equivalent to the lower-half witness target
above the current finite certificate threshold. -/
theorem currentFormalTarget50000_iff_halfWitnessLowerBound :
    Round1Status.CurrentFormalTarget50000 ↔
      GoldbachHalfWitnessLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound_iff_halfWitnessLowerBound 50000

/-- The current status target is equivalent to having no lower-half-witness
counterexample above the current finite certificate threshold. -/
theorem currentFormalTarget50000_iff_no_halfWitnessCounterexample_above :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ n : Nat, GoldbachHalfWitnessCounterexampleAbove 50000 n := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound_iff_no_halfWitnessCounterexample_above 50000

/-- The exact `goal.md` statement is equivalent to ruling out all
representation-shaped counterexamples above the current `50000` finite
certificate. -/
theorem binaryGoldbachConjecture_iff_no_representation_counterexample_above50000 :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ n : Nat, GoldbachRepresentationCounterexampleAbove 50000 n :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.trans
    currentFormalTarget50000_iff_no_representation_counterexample_above

/-- The exact `goal.md` statement is equivalent to proving lower-half
prime-complement witnesses above the current finite certificate threshold. -/
theorem binaryGoldbachConjecture_iff_halfWitnessLowerBound50000 :
    Round1Status.BinaryGoldbachConjecture ↔
      GoldbachHalfWitnessLowerBound 50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.trans
    currentFormalTarget50000_iff_halfWitnessLowerBound

/-- The exact `goal.md` statement is equivalent to ruling out all
lower-half-witness counterexamples above the current finite certificate. -/
theorem binaryGoldbachConjecture_iff_no_halfWitnessCounterexample_above50000 :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ n : Nat, GoldbachHalfWitnessCounterexampleAbove 50000 n :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.trans
    currentFormalTarget50000_iff_no_halfWitnessCounterexample_above

/-- If the exact binary Goldbach statement fails, then there is a counterexample
above the current `50000` certificate threshold. -/
theorem exists_counterexample_above50000_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ n : Nat, GoldbachCounterexampleAbove 50000 n := by
  have htail : ¬ ExplicitGoldbachLowerBound 50000 := by
    intro lower_bound
    exact h
      (Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000.mpr
        lower_bound)
  exact (not_explicitLowerBound_iff_exists_counterexample_above 50000).mp htail

/-- If the exact binary Goldbach statement fails, then there is a
representation-shaped counterexample above the current `50000` certificate
threshold. -/
theorem exists_representation_counterexample_above50000_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ n : Nat, GoldbachRepresentationCounterexampleAbove 50000 n := by
  rcases exists_counterexample_above50000_of_not_binaryGoldbachConjecture h with
    ⟨n, hn⟩
  exact ⟨n, (counterexampleAbove_iff_representationCounterexampleAbove.mp hn)⟩

/-- If the exact binary Goldbach statement fails, then there is a literal
binary counterexample, and it is necessarily above the current finite
certificate threshold. -/
theorem exists_binary_counterexample_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ n : Nat, BinaryGoldbachCounterexample n :=
  (not_binaryGoldbachConjecture_iff_exists_binary_counterexample).mp h

/-- Failure of the exact binary Goldbach statement is equivalent to a
representation-shaped tail counterexample above the current finite certificate. -/
theorem not_binaryGoldbachConjecture_iff_exists_representationCounterexampleAbove50000 :
    ¬ Round1Status.BinaryGoldbachConjecture ↔
      ∃ n : Nat, GoldbachRepresentationCounterexampleAbove 50000 n := by
  constructor
  · exact exists_representation_counterexample_above50000_of_not_binaryGoldbachConjecture
  · intro counter h
    exact
      (binaryGoldbachConjecture_iff_no_representation_counterexample_above50000.mp h)
        counter

/-- Failure of the exact binary Goldbach statement is equivalent to a
lower-half-witness counterexample above the current finite certificate. -/
theorem not_binaryGoldbachConjecture_iff_exists_halfWitnessCounterexampleAbove50000 :
    ¬ Round1Status.BinaryGoldbachConjecture ↔
      ∃ n : Nat, GoldbachHalfWitnessCounterexampleAbove 50000 n := by
  constructor
  · intro h
    rcases
      (not_binaryGoldbachConjecture_iff_exists_representationCounterexampleAbove50000.mp h)
      with ⟨n, hn⟩
    exact
      ⟨n, (representationCounterexampleAbove_iff_halfWitnessCounterexampleAbove.mp hn)⟩
  · intro counter h
    exact
      (binaryGoldbachConjecture_iff_no_halfWitnessCounterexample_above50000.mp h)
        counter

/-- Any nonempty set of tail counterexamples has a least counterexample. -/
theorem exists_minimal_counterexample_above {B : Nat}
    (h : ∃ n : Nat, GoldbachCounterexampleAbove B n) :
    ∃ m : Nat,
      GoldbachCounterexampleAbove B m ∧
        ∀ n : Nat, GoldbachCounterexampleAbove B n → m ≤ n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro n hn
  exact Nat.find_min' h hn

/-- Therefore any failure of the exact binary Goldbach statement has a least
counterexample above the current finite certificate threshold. -/
theorem exists_minimal_counterexample_above50000_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ m : Nat,
      GoldbachCounterexampleAbove 50000 m ∧
        ∀ n : Nat, GoldbachCounterexampleAbove 50000 n → m ≤ n :=
  exists_minimal_counterexample_above
    (exists_counterexample_above50000_of_not_binaryGoldbachConjecture h)

/-- Any nonempty set of representation-shaped tail counterexamples has a least
counterexample. -/
theorem exists_minimal_representation_counterexample_above {B : Nat}
    (h : ∃ n : Nat, GoldbachRepresentationCounterexampleAbove B n) :
    ∃ m : Nat,
      GoldbachRepresentationCounterexampleAbove B m ∧
        ∀ n : Nat, GoldbachRepresentationCounterexampleAbove B n → m ≤ n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro n hn
  exact Nat.find_min' h hn

/-- Therefore any failure of the exact binary Goldbach statement has a least
representation-shaped counterexample above the current finite certificate
threshold. -/
theorem exists_minimal_representation_counterexample_above50000_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ m : Nat,
      GoldbachRepresentationCounterexampleAbove 50000 m ∧
        ∀ n : Nat,
          GoldbachRepresentationCounterexampleAbove 50000 n → m ≤ n :=
  exists_minimal_representation_counterexample_above
    (exists_representation_counterexample_above50000_of_not_binaryGoldbachConjecture h)

/-- Therefore any failure of the exact binary Goldbach statement has a least
literal binary counterexample; the current finite certificate proves that this
least counterexample is above `50000`. -/
theorem exists_minimal_binary_counterexample_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ m : Nat,
      BinaryGoldbachCounterexample m ∧
        50000 < m ∧
          ∀ n : Nat, BinaryGoldbachCounterexample n → m ≤ n := by
  classical
  have hnonempty :
      ∃ n : Nat, BinaryGoldbachCounterexample n :=
    exists_binary_counterexample_of_not_binaryGoldbachConjecture h
  refine ⟨Nat.find hnonempty, Nat.find_spec hnonempty, ?_, ?_⟩
  · exact binaryCounterexample_gt50000 (Nat.find_spec hnonempty)
  · intro n hn
    exact Nat.find_min' hnonempty hn

/-- A least literal binary counterexample supplies the induction-style minimal
counterexample package: all smaller even numbers in the `goal.md` range have
representations. -/
theorem minimalBinaryCounterexample_of_least_binaryCounterexample
    {m : Nat}
    (hm : BinaryGoldbachCounterexample m)
    (hmin : ∀ n : Nat, BinaryGoldbachCounterexample n → m ≤ n) :
    MinimalBinaryGoldbachCounterexample m := by
  refine ⟨hm, binaryCounterexample_gt50000 hm, ?_⟩
  intro n hnm hn4 hnEven
  by_contra hnot
  have hnCounter : BinaryGoldbachCounterexample n := ⟨hn4, hnEven, hnot⟩
  have hle : m ≤ n := hmin n hnCounter
  omega

/-- Therefore any failure of the exact binary Goldbach statement has a minimal
binary counterexample in the induction-ready form. -/
theorem exists_minimalBinaryCounterexample_of_not_binaryGoldbachConjecture
    (h : ¬ Round1Status.BinaryGoldbachConjecture) :
    ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  rcases exists_minimal_binary_counterexample_of_not_binaryGoldbachConjecture h with
    ⟨m, hm, _hmgt, hmin⟩
  exact ⟨m, minimalBinaryCounterexample_of_least_binaryCounterexample hm hmin⟩

/-- The exact binary Goldbach statement is equivalent to the nonexistence of
an induction-ready minimal binary counterexample. -/
theorem binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  constructor
  · intro h hminimal
    rcases hminimal with ⟨m, hm⟩
    exact hm.1.2.2 (h m hm.1.1 hm.1.2.1)
  · intro hno
    by_contra hnot
    exact hno (exists_minimalBinaryCounterexample_of_not_binaryGoldbachConjecture hnot)

/-- The current `ExplicitGoldbachLowerBound 50000` target is also equivalent to
the nonexistence of an induction-ready minimal binary counterexample. -/
theorem currentFormalTarget50000_iff_no_minimalBinaryCounterexample :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.symm.trans
    binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample

/-- The same equivalence stated directly for the remaining Lean target. -/
theorem explicitLowerBound50000_iff_no_minimalBinaryCounterexample :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_iff_no_minimalBinaryCounterexample

/-- A future proof may close the exact binary Goldbach statement by ruling out
the induction-ready minimal counterexample package. -/
theorem binaryGoldbachConjecture_of_no_minimalBinaryCounterexample
    (h : ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.mpr h

/-- A minimal binary counterexample has no lower-half prime-complement
witness. -/
theorem not_halfWitness_of_minimalBinaryCounterexample {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    ¬ GoldbachHalfWitness m := by
  intro hhalf
  exact hm.1.2.2 (goldbachRepresentation_iff_halfWitness.mpr hhalf)

/-- Equivalently, for every lower-half prime `p`, the complement `m - p` is
not prime in a minimal binary counterexample. -/
theorem not_prime_complement_of_minimalBinaryCounterexample
    {m p : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m)
    (hp_half : p ≤ m / 2)
    (hp : Nat.Prime p) :
    ¬ Nat.Prime (m - p) := by
  intro hq
  exact not_halfWitness_of_minimalBinaryCounterexample hm
    ⟨p, hp_half, hp, hq⟩

/-- A lower-half prime has a complement at least `2`.  This isolates the small
arithmetic side condition needed to extract prime divisors from composite
complements. -/
theorem two_le_complement_of_half_prime
    {m p : Nat}
    (hp_half : p ≤ m / 2)
    (hp : Nat.Prime p) :
    2 ≤ m - p := by
  have htwo : p * 2 ≤ m :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hp_half
  have htwo' : 2 * p ≤ m := by simpa [Nat.mul_comm] using htwo
  have hadd : p + p ≤ m := by simpa [two_mul] using htwo'
  have hp_le_sub : p ≤ m - p := Nat.le_sub_of_add_le hadd
  exact le_trans hp.two_le hp_le_sub

/-- A divisor cover for the lower-half prime complements rules out a
lower-half Goldbach witness. -/
theorem not_halfWitness_of_lowerHalfPrimeComplementDivisorCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementDivisorCover m) :
    ¬ GoldbachHalfWitness m := by
  intro hhalf
  rcases hhalf with ⟨p, hp_half, hp, hq⟩
  rcases hcover p hp_half hp with ⟨r, hr, hrdvd, hrlt⟩
  exact (Nat.not_prime_of_dvd_of_lt hrdvd hr.two_le hrlt) hq

/-- Every induction-ready minimal binary counterexample forces a proper-prime
divisor cover of all lower-half prime complements. -/
theorem lowerHalfPrimeComplementDivisorCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    LowerHalfPrimeComplementDivisorCover m := by
  intro p hp_half hp
  have hcomp_ge_two : 2 ≤ m - p :=
    two_le_complement_of_half_prime hp_half hp
  have hnot : ¬ Nat.Prime (m - p) :=
    not_prime_complement_of_minimalBinaryCounterexample hm hp_half hp
  refine ⟨Nat.minFac (m - p), Nat.minFac_prime ?_, Nat.minFac_dvd _, ?_⟩
  · omega
  · exact (Nat.not_prime_iff_minFac_lt hcomp_ge_two).mp hnot

/-- Divisibility of the lower-half complement is the same as the congruence
`p ≡ m [MOD r]`, so the proper-prime divisor cover can be restated as a
proper-prime residue cover. -/
theorem lowerHalfPrimeComplementResidueCover_of_divisorCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementDivisorCover m) :
    LowerHalfPrimeComplementResidueCover m := by
  intro p hp_half hp
  rcases hcover p hp_half hp with ⟨r, hr, hrdvd, hrlt⟩
  have hp_le_m : p ≤ m := le_trans hp_half (Nat.div_le_self m 2)
  exact ⟨r, hr, hrlt, (Nat.modEq_iff_dvd' hp_le_m).mpr hrdvd⟩

/-- The residue-cover formulation still carries the original proper-divisor
information for every lower-half complement. -/
theorem lowerHalfPrimeComplementDivisorCover_of_residueCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementResidueCover m) :
    LowerHalfPrimeComplementDivisorCover m := by
  intro p hp_half hp
  rcases hcover p hp_half hp with ⟨r, hr, hrlt, hmod⟩
  have hp_le_m : p ≤ m := le_trans hp_half (Nat.div_le_self m 2)
  exact ⟨r, hr, (Nat.modEq_iff_dvd' hp_le_m).mp hmod, hrlt⟩

/-- The divisor-cover and residue-cover formulations are equivalent. -/
theorem lowerHalfPrimeComplementDivisorCover_iff_residueCover
    {m : Nat} :
    LowerHalfPrimeComplementDivisorCover m ↔
      LowerHalfPrimeComplementResidueCover m := by
  constructor
  · exact lowerHalfPrimeComplementResidueCover_of_divisorCover
  · exact lowerHalfPrimeComplementDivisorCover_of_residueCover

/-- Membership in the finite prime-modulus universe is just primality plus
being below the candidate counterexample. -/
theorem mem_primeModuliBelow_iff {m r : Nat} :
    r ∈ PrimeModuliBelow m ↔ Nat.Prime r ∧ r < m := by
  simp [PrimeModuliBelow, and_comm]

/-- Membership in the finite lower-half prime set. -/
theorem mem_lowerHalfPrimes_iff {m p : Nat} :
    p ∈ LowerHalfPrimes m ↔ p ≤ m / 2 ∧ Nat.Prime p := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hmem, hpprime⟩
    exact ⟨Nat.lt_add_one_iff.mp (Finset.mem_range.mp hmem), hpprime⟩
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hp.1), hp.2⟩

/-- Membership in a single finite bad residue class. -/
theorem mem_badLowerHalfPrimeResidueClass_iff {m r p : Nat} :
    p ∈ BadLowerHalfPrimeResidueClass m r ↔
      p ∈ LowerHalfPrimes m ∧ r < m - p ∧ p ≡ m [MOD r] := by
  simp [BadLowerHalfPrimeResidueClass]

/-- Membership in the finite union of bad residue classes. -/
theorem mem_badLowerHalfPrimes_iff {m p : Nat} :
    p ∈ BadLowerHalfPrimes m ↔
      p ∈ LowerHalfPrimes m ∧
        ∃ r : Nat, r ∈ PrimeModuliBelow m ∧ r < m - p ∧ p ≡ m [MOD r] := by
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨r, hrmem, hpbad⟩
    rcases mem_badLowerHalfPrimeResidueClass_iff.mp hpbad with
      ⟨hplower, hrlt, hmod⟩
    exact ⟨hplower, ⟨r, hrmem, hrlt, hmod⟩⟩
  · intro hp
    rcases hp with ⟨hplower, r, hrmem, hrlt, hmod⟩
    exact Finset.mem_biUnion.mpr
      ⟨r, hrmem,
        mem_badLowerHalfPrimeResidueClass_iff.mpr
          ⟨hplower, hrlt, hmod⟩⟩

/-- Every finite bad-residue prime is still a lower-half prime. -/
theorem badLowerHalfPrimes_subset_lowerHalfPrimes {m : Nat} :
    BadLowerHalfPrimes m ⊆ LowerHalfPrimes m := by
  intro p hp
  exact (mem_badLowerHalfPrimes_iff.mp hp).1

/-- The finite union of bad residue classes is bounded by the sum of the sizes
of the individual bad residue classes. -/
theorem badLowerHalfPrimes_card_le_badResidueClassCardSum (m : Nat) :
    (BadLowerHalfPrimes m).card ≤
      BadLowerHalfPrimeResidueClassCardSum m := by
  simpa [BadLowerHalfPrimes, BadLowerHalfPrimeResidueClassCardSum] using
    (Finset.card_biUnion_le
      (s := PrimeModuliBelow m)
      (t := BadLowerHalfPrimeResidueClass m))

/-- The union-bound surplus criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_unionBoundSurplus
    {m : Nat}
    (hsurplus : LowerHalfPrimeResidueUnionBoundSurplus m) :
    LowerHalfPrimeResidueSurplus m := by
  unfold LowerHalfPrimeResidueUnionBoundSurplus at hsurplus
  unfold LowerHalfPrimeResidueSurplus
  exact Nat.lt_of_le_of_lt
    (badLowerHalfPrimes_card_le_badResidueClassCardSum m) hsurplus

/-- Every bad lower-half prime is covered either by a small modulus or by a
large modulus, for any chosen split threshold `R`. -/
theorem badLowerHalfPrimes_subset_small_union_large
    (m R : Nat) :
    BadLowerHalfPrimes m ⊆
      BadLowerHalfPrimesSmallModuli m R ∪
        BadLowerHalfPrimesLargeModuli m R := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨r, hrmem, hpbad⟩
  by_cases hrle : r ≤ R
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_biUnion.mpr
        ⟨r, Finset.mem_filter.mpr ⟨hrmem, hrle⟩, hpbad⟩
  · have hRlt : R < r := Nat.lt_of_not_ge hrle
    exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_biUnion.mpr
        ⟨r, Finset.mem_filter.mpr ⟨hrmem, hRlt⟩, hpbad⟩

/-- The full bad-residue cover is bounded by the sum of the small- and
large-modulus covered set sizes. -/
theorem badLowerHalfPrimes_card_le_small_add_large
    (m R : Nat) :
    (BadLowerHalfPrimes m).card ≤
      (BadLowerHalfPrimesSmallModuli m R).card +
        (BadLowerHalfPrimesLargeModuli m R).card := by
  have hsubset :
      BadLowerHalfPrimes m ⊆
        BadLowerHalfPrimesSmallModuli m R ∪
          BadLowerHalfPrimesLargeModuli m R :=
    badLowerHalfPrimes_subset_small_union_large m R
  exact le_trans (Finset.card_le_card hsubset)
    (Finset.card_union_le
      (BadLowerHalfPrimesSmallModuli m R)
      (BadLowerHalfPrimesLargeModuli m R))

/-- A small/large split surplus implies the actual finite residue surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_splitSurplus
    {m R : Nat}
    (hsurplus : LowerHalfPrimeResidueSplitSurplus m R) :
    LowerHalfPrimeResidueSurplus m := by
  unfold LowerHalfPrimeResidueSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSurplus
  exact Nat.lt_of_le_of_lt
    (badLowerHalfPrimes_card_le_small_add_large m R) hsurplus

/-- The small-modulus covered set is bounded by the sum of its residue-class
sizes. -/
theorem badLowerHalfPrimesSmallModuli_card_le_smallResidueClassCardSum
    (m R : Nat) :
    (BadLowerHalfPrimesSmallModuli m R).card ≤
      BadLowerHalfPrimeSmallResidueClassCardSum m R := by
  simpa [BadLowerHalfPrimesSmallModuli,
    BadLowerHalfPrimeSmallResidueClassCardSum] using
    (Finset.card_biUnion_le
      (s := PrimeModuliBelowAtMost m R)
      (t := BadLowerHalfPrimeResidueClass m))

/-- The two-range criterion with a small-modulus union bound implies the
split surplus criterion. -/
theorem lowerHalfPrimeResidueSplitSurplus_of_smallUnionBoundSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R) :
    LowerHalfPrimeResidueSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSplitSurplus
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right
      (badLowerHalfPrimesSmallModuli_card_le_smallResidueClassCardSum m R)
      (BadLowerHalfPrimesLargeModuli m R).card)
    hsurplus

/-- The two-range criterion with a small-modulus union bound implies the
actual finite residue surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_smallUnionBoundSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_splitSurplus
    (lowerHalfPrimeResidueSplitSurplus_of_smallUnionBoundSplitSurplus
      hsurplus)

/-- Every lower-half prime covered by a large modulus is recovered from an
explicit complement cofactor pair. -/
theorem badLowerHalfPrimesLargeModuli_subset_cofactorImage
    (m R : Nat) :
    BadLowerHalfPrimesLargeModuli m R ⊆
      LargeBadLowerHalfPrimeCofactorImage m R := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨r, hrmem, hpbad⟩
  rcases mem_badLowerHalfPrimeResidueClass_iff.mp hpbad with
    ⟨hplower, hrlt, hmod⟩
  rcases mem_lowerHalfPrimes_iff.mp hplower with ⟨hp_half, _hpprime⟩
  have hp_le_m : p ≤ m := le_trans hp_half (Nat.div_le_self m 2)
  have hrdvd : r ∣ m - p := (Nat.modEq_iff_dvd' hp_le_m).mp hmod
  rcases exists_eq_mul_right_of_dvd hrdvd with ⟨k, hk⟩
  have hrprime : Nat.Prime r :=
    (mem_primeModuliBelow_iff.mp (Finset.mem_filter.mp hrmem).1).1
  have hk_mem : k ∈ Finset.range (m + 1) := by
    have hk_le_prod : k ≤ r * k := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right k hrprime.pos
    have hprod_le_m : r * k ≤ m := by
      rw [← hk]
      exact Nat.sub_le m p
    exact Finset.mem_range.mpr
      (Nat.lt_add_one_iff.mpr (le_trans hk_le_prod hprod_le_m))
  have hk_two : 2 ≤ k := by
    by_contra hklt
    have hklt' : k < 2 := Nat.lt_of_not_ge hklt
    interval_cases k
    · simp at hk
      omega
    · simp at hk
      omega
  have hp_eq : m - r * k = p := by
    rw [← hk]
    omega
  have hpair :
      (r, k) ∈ LargeBadLowerHalfPrimeCofactorPairs m R := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_product.mpr ⟨hrmem, hk_mem⟩,
      hk_two, by simpa [hp_eq] using hplower⟩
  exact Finset.mem_image.mpr ⟨(r, k), hpair, hp_eq⟩

/-- Conversely, every point in the cofactor image is genuinely covered by a
large-modulus bad residue class.  Thus the cofactor image is not merely a
loose universe: its elements are exactly large-modulus covered lower-half
primes. -/
theorem largeBadLowerHalfPrimeCofactorImage_subset_largeModuli
    (m R : Nat) :
    LargeBadLowerHalfPrimeCofactorImage m R ⊆
      BadLowerHalfPrimesLargeModuli m R := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨rk, hrk, hp_eq⟩
  rcases rk with ⟨r, k⟩
  rcases Finset.mem_filter.mp hrk with ⟨hrkprod, hk_two, hplower⟩
  rcases Finset.mem_product.mp hrkprod with ⟨hrmem, _hk_mem⟩
  have hp_eq' : p = m - r * k := by simpa using hp_eq.symm
  have hsub_prime : Nat.Prime (m - r * k) :=
    (mem_lowerHalfPrimes_iff.mp hplower).2
  have hrk_le_m : r * k ≤ m := by
    have htwo : 2 ≤ m - r * k := hsub_prime.two_le
    omega
  have hp_le_m : p ≤ m := by omega
  have hm_sub_p : m - p = r * k := by omega
  have hrlt : r < m - p := by
    rw [hm_sub_p]
    have hrpos : 0 < r :=
      (mem_primeModuliBelow_iff.mp (Finset.mem_filter.mp hrmem).1).1.pos
    nlinarith [hk_two]
  have hmod : p ≡ m [MOD r] := by
    have hdiv : r ∣ m - p := by
      rw [hm_sub_p]
      exact dvd_mul_right r k
    exact (Nat.modEq_iff_dvd' hp_le_m).mpr hdiv
  have hpbad : p ∈ BadLowerHalfPrimeResidueClass m r :=
    mem_badLowerHalfPrimeResidueClass_iff.mpr
      ⟨by simpa [hp_eq'] using hplower, hrlt, hmod⟩
  exact Finset.mem_biUnion.mpr ⟨r, hrmem, hpbad⟩

/-- The large-modulus covered set is exactly the image of the complement
cofactor witness relation. -/
theorem largeBadLowerHalfPrimeCofactorImage_eq_largeModuli
    (m R : Nat) :
    LargeBadLowerHalfPrimeCofactorImage m R =
      BadLowerHalfPrimesLargeModuli m R :=
  Finset.Subset.antisymm
    (largeBadLowerHalfPrimeCofactorImage_subset_largeModuli m R)
    (badLowerHalfPrimesLargeModuli_subset_cofactorImage m R)

/-- Cardinality form of the exact cofactor-image representation of the
large-modulus covered set. -/
theorem largeBadLowerHalfPrimeCofactorImage_card_eq_largeModuli_card
    (m R : Nat) :
    (LargeBadLowerHalfPrimeCofactorImage m R).card =
      (BadLowerHalfPrimesLargeModuli m R).card := by
  rw [largeBadLowerHalfPrimeCofactorImage_eq_largeModuli]

/-- The large-modulus covered set is bounded by the number of complement
cofactor pairs. -/
theorem badLowerHalfPrimesLargeModuli_card_le_cofactorPairs_card
    (m R : Nat) :
    (BadLowerHalfPrimesLargeModuli m R).card ≤
      (LargeBadLowerHalfPrimeCofactorPairs m R).card := by
  exact le_trans
    (Finset.card_le_card
      (badLowerHalfPrimesLargeModuli_subset_cofactorImage m R))
    (Finset.card_image_le)

/-- Cofactor pairs attached to large moduli automatically satisfy
`k ≤ m / (R + 1)`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_subset_bounded
    (m R : Nat) :
    LargeBadLowerHalfPrimeCofactorPairs m R ⊆
      LargeBadLowerHalfPrimeBoundedCofactorPairs m R := by
  intro rk hrk
  rcases Finset.mem_filter.mp hrk with ⟨hrkprod, hk_two, hplower⟩
  rcases Finset.mem_product.mp hrkprod with ⟨hrmem, _hk_mem⟩
  rcases mem_lowerHalfPrimes_iff.mp hplower with ⟨_hp_half, hpprime⟩
  have hRlt : R < rk.1 := (Finset.mem_filter.mp hrmem).2
  have hsucc_le : R + 1 ≤ rk.1 := Nat.succ_le_of_lt hRlt
  have hrk_le_m : rk.1 * rk.2 ≤ m := by
    have hsub_two : 2 ≤ m - rk.1 * rk.2 := hpprime.two_le
    omega
  have hsmall_mul : rk.2 * (R + 1) ≤ m := by
    have hmul_le : (R + 1) * rk.2 ≤ rk.1 * rk.2 :=
      Nat.mul_le_mul_right rk.2 hsucc_le
    simpa [Nat.mul_comm] using le_trans hmul_le hrk_le_m
  have hk_bound : rk.2 ≤ m / (R + 1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos R)).mpr hsmall_mul
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨hrmem,
        Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hk_bound)⟩,
      hk_two, hplower⟩

/-- The unbounded cofactor-pair count is bounded by the intrinsically bounded
cofactor-pair count. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_le_bounded
    (m R : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m R).card ≤
      (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card :=
  Finset.card_le_card (largeBadLowerHalfPrimeCofactorPairs_subset_bounded m R)

/-- The built-in bounded cofactor universe is not larger than the original
unbounded one: the bound `k ≤ m / (R + 1)` still implies `k ≤ m`. -/
theorem largeBadLowerHalfPrimeBoundedCofactorPairs_subset_pairs
    (m R : Nat) :
    LargeBadLowerHalfPrimeBoundedCofactorPairs m R ⊆
      LargeBadLowerHalfPrimeCofactorPairs m R := by
  intro rk hrk
  rcases Finset.mem_filter.mp hrk with ⟨hrkprod, hk_two, hplower⟩
  rcases Finset.mem_product.mp hrkprod with ⟨hrmem, hk_mem⟩
  have hk_le_bound : rk.2 ≤ m / (R + 1) := by
    exact Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk_mem)
  have hk_le_m : rk.2 ≤ m := by
    exact le_trans hk_le_bound (Nat.div_le_self m (R + 1))
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨hrmem, Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hk_le_m)⟩,
      hk_two, hplower⟩

/-- The intrinsic bounded-cofactor relation is exactly the original cofactor
relation.  The bounded definition only shrinks the ambient finite universe to
the range already forced by `r > R`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_eq_bounded
    (m R : Nat) :
    LargeBadLowerHalfPrimeCofactorPairs m R =
      LargeBadLowerHalfPrimeBoundedCofactorPairs m R :=
  Finset.Subset.antisymm
    (largeBadLowerHalfPrimeCofactorPairs_subset_bounded m R)
    (largeBadLowerHalfPrimeBoundedCofactorPairs_subset_pairs m R)

/-- Cardinality form of the exact bounded/unbounded cofactor-pair
identification. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_eq_bounded
    (m R : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m R).card =
      (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card := by
  rw [largeBadLowerHalfPrimeCofactorPairs_eq_bounded]

/-- Intrinsically bounded cofactor witnesses lie in the rectangular cofactor
box `r ∈ PrimeModuliBelowAbove m R`, `2 ≤ k ≤ m / (R + 1)`. -/
theorem largeBadLowerHalfPrimeBoundedCofactorPairs_subset_cofactorBox
    (m R : Nat) :
    LargeBadLowerHalfPrimeBoundedCofactorPairs m R ⊆
      LargeBadLowerHalfPrimeCofactorBox m R := by
  intro rk hrk
  rcases Finset.mem_filter.mp hrk with ⟨hrkprod, hk_two, _hplower⟩
  rcases Finset.mem_product.mp hrkprod with ⟨hrmem, hk_mem⟩
  have hk_lt : rk.2 < m / (R + 1) + 1 := Finset.mem_range.mp hk_mem
  have hk_bound : rk.2 ≤ m / (R + 1) := by
    omega
  exact Finset.mem_product.mpr
    ⟨hrmem, Finset.mem_Icc.mpr ⟨hk_two, hk_bound⟩⟩

/-- The bounded cofactor-pair count is at most the rectangular cofactor-box
count. -/
theorem largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBox
    (m R : Nat) :
    (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card ≤
      (LargeBadLowerHalfPrimeCofactorBox m R).card :=
  Finset.card_le_card
    (largeBadLowerHalfPrimeBoundedCofactorPairs_subset_cofactorBox m R)

/-- The rectangular cofactor box has the expected product cardinality. -/
theorem largeBadLowerHalfPrimeCofactorBox_card
    (m R : Nat) :
    (LargeBadLowerHalfPrimeCofactorBox m R).card =
      (PrimeModuliBelowAbove m R).card *
        (Finset.Icc 2 (m / (R + 1))).card := by
  simp [LargeBadLowerHalfPrimeCofactorBox]

/-- The bounded cofactor-pair count is bounded by the explicit rectangular
product `#PrimeModuliBelowAbove m R * #Icc 2 (m / (R + 1))`. -/
theorem largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBoxProduct
    (m R : Nat) :
    (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card ≤
      (PrimeModuliBelowAbove m R).card *
        (Finset.Icc 2 (m / (R + 1))).card := by
  calc
    (LargeBadLowerHalfPrimeBoundedCofactorPairs m R).card ≤
        (LargeBadLowerHalfPrimeCofactorBox m R).card :=
      largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBox m R
    _ = (PrimeModuliBelowAbove m R).card *
        (Finset.Icc 2 (m / (R + 1))).card :=
      largeBadLowerHalfPrimeCofactorBox_card m R

/-- The explicit cofactor-box product with `#Icc 2 N` simplified. -/
theorem cofactorBoxProduct_card_eq
    (m R : Nat) :
    (PrimeModuliBelowAbove m R).card *
        (Finset.Icc 2 (m / (R + 1))).card =
      (PrimeModuliBelowAbove m R).card *
        (m / (R + 1) - 1) := by
  rw [Nat.card_Icc]
  congr 1

/-- The finite prime-modulus universe below a positive `m` has cardinality
`π(m - 1)`. -/
theorem primeModuliBelow_card_eq_primeCounting_pred_of_pos
    {m : Nat} (hm : 0 < m) :
    (PrimeModuliBelow m).card = Nat.primeCounting (m - 1) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hmrange : m - 1 + 1 = m := by omega
  rw [hmrange]
  rfl

/-- If the threshold lies below `m`, the small-prime-modulus set has
cardinality `π(R)`. -/
theorem primeModuliBelowAtMost_card_eq_primeCounting_of_lt
    {m R : Nat} (hR : R < m) :
    (PrimeModuliBelowAtMost m R).card = Nat.primeCounting R := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext r
  simp only [PrimeModuliBelowAtMost, PrimeModuliBelow, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · intro h
    exact ⟨by omega, h.1.2⟩
  · intro h
    exact ⟨⟨by omega, h.2⟩, by omega⟩

/-- Splitting the finite prime-modulus universe at `R` partitions it into
small and large moduli. -/
theorem primeModuliBelowAtMost_card_add_primeModuliBelowAbove_card
    (m R : Nat) :
    (PrimeModuliBelowAtMost m R).card +
        (PrimeModuliBelowAbove m R).card =
      (PrimeModuliBelow m).card := by
  unfold PrimeModuliBelowAtMost PrimeModuliBelowAbove
  simpa [not_le] using
    (Finset.card_filter_add_card_filter_not
      (s := PrimeModuliBelow m) (p := fun r => r ≤ R))

/-- For `R < m`, the large prime-modulus count is exactly the prime-counting
window `π(m - 1) - π(R)`. -/
theorem primeModuliBelowAbove_card_eq_primeCounting_sub_of_lt
    {m R : Nat} (hR : R < m) :
    (PrimeModuliBelowAbove m R).card =
      Nat.primeCounting (m - 1) - Nat.primeCounting R := by
  have hmpos : 0 < m := by omega
  have hbelow :
      (PrimeModuliBelow m).card = Nat.primeCounting (m - 1) :=
    primeModuliBelow_card_eq_primeCounting_pred_of_pos hmpos
  have hatmost :
      (PrimeModuliBelowAtMost m R).card = Nat.primeCounting R :=
    primeModuliBelowAtMost_card_eq_primeCounting_of_lt hR
  have hpart :
      (PrimeModuliBelowAtMost m R).card +
          (PrimeModuliBelowAbove m R).card =
        (PrimeModuliBelow m).card :=
    primeModuliBelowAtMost_card_add_primeModuliBelowAbove_card m R
  have hsum :
      Nat.primeCounting R + (PrimeModuliBelowAbove m R).card =
        Nat.primeCounting (m - 1) := by
    simpa [hatmost, hbelow] using hpart
  omega

/-- The finite set of lower-half primes has cardinality `π(m / 2)`. -/
theorem lowerHalfPrimes_card_eq_primeCounting_half
    (m : Nat) :
    (LowerHalfPrimes m).card = Nat.primeCounting (m / 2) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

/-- The number of values `0 ≤ p ≤ N` in a fixed residue class modulo `r` is
at most `N / r + 1`.  The proof uses the quotient map `p ↦ p / r`, which is
injective on one residue class by `Nat.div_add_mod`. -/
theorem card_filter_range_modEq_le_div_add_one
    (N a r : Nat) :
    ((Finset.range (N + 1)).filter (fun p => p % r = a % r)).card ≤
      N / r + 1 := by
  let S := (Finset.range (N + 1)).filter (fun p => p % r = a % r)
  let f : Nat → Nat := fun p => p / r
  have hinj : Set.InjOn f (↑S : Set Nat) := by
    intro p hp q hq hdiv
    have hpmod : p % r = a % r := (Finset.mem_filter.mp hp).2
    have hqmod : q % r = a % r := (Finset.mem_filter.mp hq).2
    have hdiv' : p / r = q / r := by
      simpa [f] using hdiv
    calc
      p = r * (p / r) + p % r := (Nat.div_add_mod p r).symm
      _ = r * (q / r) + q % r := by rw [hdiv', hpmod, hqmod]
      _ = q := Nat.div_add_mod q r
  have hcard : (Finset.image f S).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hsubset : Finset.image f S ⊆ Finset.range (N / r + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hpS, rfl⟩
    have hp_range : p ∈ Finset.range (N + 1) :=
      (Finset.mem_filter.mp hpS).1
    have hp_le : p ≤ N :=
      Nat.lt_add_one_iff.mp (Finset.mem_range.mp hp_range)
    exact Finset.mem_range.mpr <| Nat.lt_add_one_iff.mpr <|
      Nat.div_le_div_right hp_le
  calc
    S.card = (Finset.image f S).card := hcard.symm
    _ ≤ (Finset.range (N / r + 1)).card := Finset.card_le_card hsubset
    _ = N / r + 1 := Finset.card_range _

/-- A single bad lower-half prime residue class is bounded by the elementary
point count for one residue class in `0 ≤ p ≤ m / 2`. -/
theorem badLowerHalfPrimeResidueClass_card_le_pointBound
    (m r : Nat) :
    (BadLowerHalfPrimeResidueClass m r).card ≤ m / 2 / r + 1 := by
  have hsubset :
      BadLowerHalfPrimeResidueClass m r ⊆
        (Finset.range (m / 2 + 1)).filter (fun p => p % r = m % r) := by
    intro p hp
    rcases mem_badLowerHalfPrimeResidueClass_iff.mp hp with
      ⟨hplower, _hrlt, hmod⟩
    have hp_half : p ≤ m / 2 := (mem_lowerHalfPrimes_iff.mp hplower).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hp_half), by
        simpa [Nat.ModEq] using hmod⟩
  exact le_trans (Finset.card_le_card hsubset)
    (card_filter_range_modEq_le_div_add_one (m / 2) m r)

/-- In an even candidate, the bad residue class modulo `2` contains at most
the prime `2`. -/
theorem badLowerHalfPrimeResidueClass_two_card_le_one_of_even
    {m : Nat} (hm : Even m) :
    (BadLowerHalfPrimeResidueClass m 2).card ≤ 1 := by
  have hsubset : BadLowerHalfPrimeResidueClass m 2 ⊆ ({2} : Finset Nat) := by
    intro p hpbad
    rcases mem_badLowerHalfPrimeResidueClass_iff.mp hpbad with
      ⟨hplower, _hrlt, hmod⟩
    have hpprime : Nat.Prime p := (mem_lowerHalfPrimes_iff.mp hplower).2
    have hp2 : p = 2 := by
      rcases hpprime.eq_two_or_odd with hp2 | hpodd
      · exact hp2
      · have hm0 : m % 2 = 0 := by
          simpa [Nat.even_iff] using hm
        have hp0 : p % 2 = 0 := by
          simpa [Nat.ModEq, hm0] using hmod
        omega
    simp [hp2]
  exact le_trans (Finset.card_le_card hsubset) (by simp)

/-- Summing the point-counting bound over small prime moduli majorizes the
small-modulus bad residue-class union-bound sum. -/
theorem badLowerHalfPrimeSmallResidueClassCardSum_le_pointBoundSum
    (m R : Nat) :
    BadLowerHalfPrimeSmallResidueClassCardSum m R ≤
      BadLowerHalfPrimeSmallResidueClassPointBoundSum m R := by
  simpa [BadLowerHalfPrimeSmallResidueClassCardSum,
    BadLowerHalfPrimeSmallResidueClassPointBoundSum] using
    (Finset.sum_le_sum
      (s := PrimeModuliBelowAtMost m R)
      (fun r _hr => badLowerHalfPrimeResidueClass_card_le_pointBound m r))

/-- For even `m`, the parity-aware point-counting sum majorizes the
small-modulus bad residue-class union-bound sum while avoiding the crude
`r = 2` overcount. -/
theorem badLowerHalfPrimeSmallResidueClassCardSum_le_parityPointBoundSum_of_even
    {m R : Nat} (hm : Even m) :
    BadLowerHalfPrimeSmallResidueClassCardSum m R ≤
      BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
  classical
  let S := PrimeModuliBelowAtMost m R
  let cardTerm : Nat → Nat := fun r =>
    (BadLowerHalfPrimeResidueClass m r).card
  let pointTerm : Nat → Nat := fun r => m / 2 / r + 1
  have hsum_erase :
      (S.erase 2).sum cardTerm ≤ (S.erase 2).sum pointTerm := by
    exact Finset.sum_le_sum fun r _hr =>
      badLowerHalfPrimeResidueClass_card_le_pointBound m r
  by_cases h2 : 2 ∈ S
  · have hsplit :
        S.sum cardTerm = cardTerm 2 + (S.erase 2).sum cardTerm := by
      exact (Finset.add_sum_erase S cardTerm h2).symm
    have hle :
        cardTerm 2 + (S.erase 2).sum cardTerm ≤
          1 + (S.erase 2).sum pointTerm := by
      exact Nat.add_le_add
        (badLowerHalfPrimeResidueClass_two_card_le_one_of_even hm)
        hsum_erase
    calc
      BadLowerHalfPrimeSmallResidueClassCardSum m R = S.sum cardTerm := by
        simp [BadLowerHalfPrimeSmallResidueClassCardSum, S, cardTerm]
      _ = cardTerm 2 + (S.erase 2).sum cardTerm := hsplit
      _ ≤ 1 + (S.erase 2).sum pointTerm := hle
      _ = BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
        simp [BadLowerHalfPrimeSmallResidueClassParityPointBoundSum, S,
          pointTerm, h2]
  · calc
      BadLowerHalfPrimeSmallResidueClassCardSum m R = S.sum cardTerm := by
        simp [BadLowerHalfPrimeSmallResidueClassCardSum, S, cardTerm]
      _ = (S.erase 2).sum cardTerm := by
        rw [Finset.erase_eq_of_notMem h2]
      _ ≤ (S.erase 2).sum pointTerm := hsum_erase
      _ = BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
        simp [BadLowerHalfPrimeSmallResidueClassParityPointBoundSum, S,
          pointTerm, h2]

/-- The cofactor-pair two-range criterion implies the two-range criterion
where the large-modulus contribution is the exact covered set. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundSplitSurplus
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_left
      (badLowerHalfPrimesLargeModuli_card_le_cofactorPairs_card m R)
      (BadLowerHalfPrimeSmallResidueClassCardSum m R))
    hsurplus

/-- The cofactor-pair two-range criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_cofactorSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_smallUnionBoundSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus
      hsurplus)

/-- The bounded-cofactor criterion implies the cofactor-pair criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_boundedCofactorSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_left
      (largeBadLowerHalfPrimeCofactorPairs_card_le_bounded m R)
      (BadLowerHalfPrimeSmallResidueClassCardSum m R))
    hsurplus

/-- Conversely, because the bounded cofactor relation is exactly the original
cofactor relation, the cofactor-pair criterion also implies the bounded
cofactor criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
      m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
  simpa [largeBadLowerHalfPrimeCofactorPairs_card_eq_bounded m R] using
    hsurplus

/-- The cofactor-pair and bounded-cofactor two-range local criteria are
equivalent. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_iff_boundedCofactorSplitSurplus
    (m R : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R ↔
      LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
        m R :=
  ⟨lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorSplitSurplus,
    lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_boundedCofactorSplitSurplus⟩

/-- The bounded-cofactor criterion implies the actual finite residue surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_boundedCofactorSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_boundedCofactorSplitSurplus
      hsurplus)

/-- The cofactor-box criterion implies the bounded-cofactor criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_left
      (largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBoxProduct
        m R)
      (BadLowerHalfPrimeSmallResidueClassCardSum m R))
    hsurplus

/-- The cofactor-box criterion implies the actual finite residue surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_cofactorBoxSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_boundedCofactorSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus
      hsurplus)

/-- The cofactor-box product criterion is the cofactor-box criterion with the
interval cardinality simplified. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus
  simpa [cofactorBoxProduct_card_eq m R] using hsurplus

/-- Conversely, the cofactor-box criterion supplies the cofactor-box product
criterion because the interval cardinality simplification is exact. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorBoxSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
      m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
  simpa [cofactorBoxProduct_card_eq m R] using hsurplus

/-- The cofactor-box and cofactor-box product local criteria are equivalent;
the latter only simplifies the interval cardinality. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_iff_cofactorBoxProductSplitSurplus
    (m R : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus m R ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
        m R :=
  ⟨lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorBoxSplitSurplus,
    lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus⟩

/-- The cofactor-box product criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_cofactorBoxProductSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorBoxSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus
      hsurplus)

/-- The prime-counting window criterion is the cofactor-box product criterion
with `#PrimeModuliBelowAbove m R` rewritten as `π(m - 1) - π(R)`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
      m R := by
  rcases hsurplus with ⟨hR, hineq⟩
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
  rw [primeModuliBelowAbove_card_eq_primeCounting_sub_of_lt hR]
  exact hineq

/-- If the threshold is known to lie below `m`, the cofactor-box product
criterion implies the prime-counting-window criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorBoxProductSplitSurplus_of_lt
    {m R : Nat} (hR : R < m)
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
      m R := by
  refine ⟨hR, ?_⟩
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus at hsurplus
  simpa [primeModuliBelowAbove_card_eq_primeCounting_sub_of_lt hR] using hsurplus

/-- The prime-counting-window local criterion is exactly the cofactor-box product
criterion together with the side condition `R < m`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_iff_lt_and_cofactorBoxProductSplitSurplus
    (m R : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R ↔
      R < m ∧
        LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
          m R := by
  constructor
  · intro hsurplus
    exact ⟨hsurplus.1,
      lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
        hsurplus⟩
  · intro hsurplus
    exact
      lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorBoxProductSplitSurplus_of_lt
        hsurplus.1 hsurplus.2

/-- The prime-counting window criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorBoxProductSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
      hsurplus)

/-- The full prime-counting criterion is the prime-counting window criterion
with `(LowerHalfPrimes m).card` rewritten as `π(m / 2)`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
      m R := by
  rcases hsurplus with ⟨hR, hineq⟩
  refine ⟨hR, ?_⟩
  simpa [lowerHalfPrimes_card_eq_primeCounting_half m] using hineq

/-- Conversely, the prime-counting window criterion supplies the full
prime-counting criterion because the lower-half-prime cardinality rewrite is
exact. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_cofactorPrimeCountingSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
      m R := by
  rcases hsurplus with ⟨hR, hineq⟩
  refine ⟨hR, ?_⟩
  simpa [lowerHalfPrimes_card_eq_primeCounting_half m] using hineq

/-- The prime-counting window and full prime-counting local criteria are
equivalent; the full form only rewrites `(LowerHalfPrimes m).card` as
`π(m / 2)`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus
    (m R : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus
        m R ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
        m R :=
  ⟨lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_cofactorPrimeCountingSplitSurplus,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus⟩

/-- The full prime-counting criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The small-modulus point-bound criterion implies the full prime-counting
criterion with the exact small-modulus residue-class sum. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
      m R := by
  rcases hsurplus with ⟨hR, hineq⟩
  refine ⟨hR, ?_⟩
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right
      (badLowerHalfPrimeSmallResidueClassCardSum_le_pointBoundSum m R)
      ((Nat.primeCounting (m - 1) - Nat.primeCounting R) *
        (m / (R + 1) - 1)))
    hineq

/-- The small-modulus point-bound criterion implies the actual finite residue
surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The parity-aware small-modulus point-bound criterion implies the full
prime-counting criterion with the exact small-modulus residue-class sum. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
      m R := by
  rcases hsurplus with ⟨hmEven, hR, hineq⟩
  refine ⟨hR, ?_⟩
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right
      (badLowerHalfPrimeSmallResidueClassCardSum_le_parityPointBoundSum_of_even
        hmEven)
      ((Nat.primeCounting (m - 1) - Nat.primeCounting R) *
        (m / (R + 1) - 1)))
    hineq

/-- The parity-aware small-modulus point-bound criterion implies the actual
finite residue surplus. -/
theorem lowerHalfPrimeResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
        m R) :
    LowerHalfPrimeResidueSurplus m :=
  lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A residue cover may be viewed as a finite-universe cover, since every
proper divisor `r < m - p` is automatically below `m`. -/
theorem lowerHalfPrimeComplementFiniteResidueCover_of_residueCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementResidueCover m) :
    LowerHalfPrimeComplementFiniteResidueCover m := by
  intro p hp_half hp
  rcases hcover p hp_half hp with ⟨r, hr, hrlt, hmod⟩
  have hr_m : r < m := lt_of_lt_of_le hrlt (Nat.sub_le m p)
  exact ⟨r, mem_primeModuliBelow_iff.mpr ⟨hr, hr_m⟩, hrlt, hmod⟩

/-- The finite-universe cover forgets no information: membership in
`PrimeModuliBelow m` supplies the required primality of each modulus. -/
theorem lowerHalfPrimeComplementResidueCover_of_finiteResidueCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementFiniteResidueCover m) :
    LowerHalfPrimeComplementResidueCover m := by
  intro p hp_half hp
  rcases hcover p hp_half hp with ⟨r, hrmem, hrlt, hmod⟩
  exact ⟨r, (mem_primeModuliBelow_iff.mp hrmem).1, hrlt, hmod⟩

/-- The residue-cover and finite-universe residue-cover formulations are
equivalent. -/
theorem lowerHalfPrimeComplementResidueCover_iff_finiteResidueCover
    {m : Nat} :
    LowerHalfPrimeComplementResidueCover m ↔
      LowerHalfPrimeComplementFiniteResidueCover m := by
  constructor
  · exact lowerHalfPrimeComplementFiniteResidueCover_of_residueCover
  · exact lowerHalfPrimeComplementResidueCover_of_finiteResidueCover

/-- The finite-universe residue cover rules out lower-half Goldbach witnesses. -/
theorem not_halfWitness_of_lowerHalfPrimeComplementFiniteResidueCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementFiniteResidueCover m) :
    ¬ GoldbachHalfWitness m :=
  not_halfWitness_of_lowerHalfPrimeComplementDivisorCover
    (lowerHalfPrimeComplementDivisorCover_of_residueCover
      (lowerHalfPrimeComplementResidueCover_of_finiteResidueCover hcover))

/-- Every induction-ready minimal binary counterexample forces the
finite-universe residue cover. -/
theorem lowerHalfPrimeComplementFiniteResidueCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    LowerHalfPrimeComplementFiniteResidueCover m :=
  lowerHalfPrimeComplementFiniteResidueCover_of_residueCover
    (lowerHalfPrimeComplementResidueCover_of_divisorCover
      (lowerHalfPrimeComplementDivisorCover_of_minimalBinaryCounterexample hm))

/-- If a lower-half prime avoids every finite bad congruence class, then its
complement is prime.  Otherwise the complement's least prime factor would be
one of the forbidden finite moduli. -/
theorem prime_complement_of_finiteResidueEscape_witness
    {m p : Nat}
    (hp_half : p ≤ m / 2)
    (hp : Nat.Prime p)
    (havoid : ∀ r : Nat, r ∈ PrimeModuliBelow m → r < m - p →
      ¬ p ≡ m [MOD r]) :
    Nat.Prime (m - p) := by
  by_contra hnot
  have hcomp_ge_two : 2 ≤ m - p :=
    two_le_complement_of_half_prime hp_half hp
  have hrprime : Nat.Prime (Nat.minFac (m - p)) :=
    Nat.minFac_prime (by omega)
  have hrdvd : Nat.minFac (m - p) ∣ m - p :=
    Nat.minFac_dvd (m - p)
  have hrlt : Nat.minFac (m - p) < m - p :=
    (Nat.not_prime_iff_minFac_lt hcomp_ge_two).mp hnot
  have hr_m : Nat.minFac (m - p) < m :=
    lt_of_lt_of_le hrlt (Nat.sub_le m p)
  have hp_le_m : p ≤ m := le_trans hp_half (Nat.div_le_self m 2)
  have hmod : p ≡ m [MOD Nat.minFac (m - p)] :=
    (Nat.modEq_iff_dvd' hp_le_m).mpr hrdvd
  exact havoid (Nat.minFac (m - p))
    (mem_primeModuliBelow_iff.mpr ⟨hrprime, hr_m⟩) hrlt hmod

/-- A finite residue escape gives a lower-half Goldbach witness. -/
theorem halfWitness_of_finiteResidueEscape
    {m : Nat}
    (hesc : LowerHalfPrimeFiniteResidueEscape m) :
    GoldbachHalfWitness m := by
  rcases hesc with ⟨p, hp_half, hp, havoid⟩
  exact ⟨p, hp_half, hp,
    prime_complement_of_finiteResidueEscape_witness hp_half hp havoid⟩

/-- A finite residue escape contradicts the finite residue cover. -/
theorem not_finiteResidueCover_of_finiteResidueEscape
    {m : Nat}
    (hesc : LowerHalfPrimeFiniteResidueEscape m) :
    ¬ LowerHalfPrimeComplementFiniteResidueCover m := by
  intro hcover
  rcases hesc with ⟨p, hp_half, hp, havoid⟩
  rcases hcover p hp_half hp with ⟨r, hrmem, hrlt, hmod⟩
  exact havoid r hrmem hrlt hmod

/-- The finite residue cover is exactly the assertion that no lower-half prime
escapes all finite bad congruence classes. -/
theorem lowerHalfPrimeComplementFiniteResidueCover_iff_no_finiteResidueEscape
    {m : Nat} :
    LowerHalfPrimeComplementFiniteResidueCover m ↔
      ¬ LowerHalfPrimeFiniteResidueEscape m := by
  constructor
  · intro hcover hesc
    exact not_finiteResidueCover_of_finiteResidueEscape hesc hcover
  · intro hno p hp_half hp
    by_contra hnone
    exact hno ⟨p, hp_half, hp, by
      intro r hrmem hrlt hmod
      exact hnone ⟨r, hrmem, hrlt, hmod⟩⟩

/-- A lower-half prime outside the finite union of bad residue classes gives
the finite-residue escape witness. -/
theorem lowerHalfPrimeFiniteResidueEscape_of_not_mem_badLowerHalfPrimes
    {m p : Nat}
    (hplower : p ∈ LowerHalfPrimes m)
    (hpbad : p ∉ BadLowerHalfPrimes m) :
    LowerHalfPrimeFiniteResidueEscape m := by
  rcases mem_lowerHalfPrimes_iff.mp hplower with ⟨hp_half, hpprime⟩
  refine ⟨p, hp_half, hpprime, ?_⟩
  intro r hrmem hrlt hmod
  exact hpbad (mem_badLowerHalfPrimes_iff.mpr
    ⟨hplower, r, hrmem, hrlt, hmod⟩)

/-- A strict cardinality surplus of lower-half primes over finite bad-residue
coverage produces an escaping lower-half prime. -/
theorem lowerHalfPrimeFiniteResidueEscape_of_residueSurplus
    {m : Nat}
    (hsurplus : LowerHalfPrimeResidueSurplus m) :
    LowerHalfPrimeFiniteResidueEscape m := by
  by_contra hno
  have hcover : LowerHalfPrimeComplementFiniteResidueCover m :=
    (lowerHalfPrimeComplementFiniteResidueCover_iff_no_finiteResidueEscape).mpr hno
  have hsubset : LowerHalfPrimes m ⊆ BadLowerHalfPrimes m := by
    intro p hplower
    rcases mem_lowerHalfPrimes_iff.mp hplower with ⟨hp_half, hpprime⟩
    rcases hcover p hp_half hpprime with ⟨r, hrmem, hrlt, hmod⟩
    exact mem_badLowerHalfPrimes_iff.mpr
      ⟨hplower, r, hrmem, hrlt, hmod⟩
  have hle : (LowerHalfPrimes m).card ≤ (BadLowerHalfPrimes m).card :=
    Finset.card_le_card hsubset
  unfold LowerHalfPrimeResidueSurplus at hsurplus
  omega

/-- The union-bound surplus criterion produces an escaping lower-half prime. -/
theorem lowerHalfPrimeFiniteResidueEscape_of_unionBoundSurplus
    {m : Nat}
    (hsurplus : LowerHalfPrimeResidueUnionBoundSurplus m) :
    LowerHalfPrimeFiniteResidueEscape m :=
  lowerHalfPrimeFiniteResidueEscape_of_residueSurplus
    (lowerHalfPrimeResidueSurplus_of_unionBoundSurplus hsurplus)

/-- A small/large split surplus produces an escaping lower-half prime. -/
theorem lowerHalfPrimeFiniteResidueEscape_of_splitSurplus
    {m R : Nat}
    (hsurplus : LowerHalfPrimeResidueSplitSurplus m R) :
    LowerHalfPrimeFiniteResidueEscape m :=
  lowerHalfPrimeFiniteResidueEscape_of_residueSurplus
    (lowerHalfPrimeResidueSurplus_of_splitSurplus hsurplus)

/-- The two-range criterion with a small-modulus union bound produces an
escaping lower-half prime. -/
theorem lowerHalfPrimeFiniteResidueEscape_of_smallUnionBoundSplitSurplus
    {m R : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R) :
    LowerHalfPrimeFiniteResidueEscape m :=
  lowerHalfPrimeFiniteResidueEscape_of_residueSurplus
    (lowerHalfPrimeResidueSurplus_of_smallUnionBoundSplitSurplus hsurplus)

/-- A residue cover also rules out a lower-half Goldbach witness, because it
is equivalent to a proper-divisor cover of the complements. -/
theorem not_halfWitness_of_lowerHalfPrimeComplementResidueCover
    {m : Nat}
    (hcover : LowerHalfPrimeComplementResidueCover m) :
    ¬ GoldbachHalfWitness m :=
  not_halfWitness_of_lowerHalfPrimeComplementDivisorCover
    (lowerHalfPrimeComplementDivisorCover_of_residueCover hcover)

/-- Every induction-ready minimal binary counterexample forces the residue
cover of all lower-half prime complements. -/
theorem lowerHalfPrimeComplementResidueCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    LowerHalfPrimeComplementResidueCover m :=
  lowerHalfPrimeComplementResidueCover_of_divisorCover
    (lowerHalfPrimeComplementDivisorCover_of_minimalBinaryCounterexample hm)

/-- Package a minimal counterexample with its forced lower-half complement
divisor cover. -/
theorem minimalCounterexamplePrimeDivisorCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    MinimalCounterexamplePrimeDivisorCover m :=
  ⟨hm, lowerHalfPrimeComplementDivisorCover_of_minimalBinaryCounterexample hm⟩

/-- The sieve-shaped package is pointwise equivalent to the minimal
counterexample package: the divisor cover is forced, not an extra assumption. -/
theorem minimalBinaryCounterexample_iff_primeDivisorCoverPackage
    {m : Nat} :
    MinimalBinaryGoldbachCounterexample m ↔
      MinimalCounterexamplePrimeDivisorCover m := by
  constructor
  · exact minimalCounterexamplePrimeDivisorCover_of_minimalBinaryCounterexample
  · intro h
    exact h.1

/-- Package a minimal counterexample with its forced lower-half complement
residue cover. -/
theorem minimalCounterexamplePrimeResidueCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    MinimalCounterexamplePrimeResidueCover m :=
  ⟨hm, lowerHalfPrimeComplementResidueCover_of_minimalBinaryCounterexample hm⟩

/-- The residue-cover package is also pointwise equivalent to the minimal
counterexample package: the residue cover is forced, not an extra assumption. -/
theorem minimalBinaryCounterexample_iff_primeResidueCoverPackage
    {m : Nat} :
    MinimalBinaryGoldbachCounterexample m ↔
      MinimalCounterexamplePrimeResidueCover m := by
  constructor
  · exact minimalCounterexamplePrimeResidueCover_of_minimalBinaryCounterexample
  · intro h
    exact h.1

/-- The divisor-cover and residue-cover packages are equivalent pointwise. -/
theorem minimalCounterexamplePrimeDivisorCover_iff_primeResidueCover
    {m : Nat} :
    MinimalCounterexamplePrimeDivisorCover m ↔
      MinimalCounterexamplePrimeResidueCover m := by
  rw [← minimalBinaryCounterexample_iff_primeDivisorCoverPackage,
    ← minimalBinaryCounterexample_iff_primeResidueCoverPackage]

/-- Package a minimal counterexample with its forced finite-universe
prime-residue cover. -/
theorem minimalCounterexampleFinitePrimeResidueCover_of_minimalBinaryCounterexample
    {m : Nat}
    (hm : MinimalBinaryGoldbachCounterexample m) :
    MinimalCounterexampleFinitePrimeResidueCover m :=
  ⟨hm, lowerHalfPrimeComplementFiniteResidueCover_of_minimalBinaryCounterexample hm⟩

/-- The finite prime-residue-cover package is also pointwise equivalent to
the minimal counterexample package: the finite cover is forced, not an extra
assumption. -/
theorem minimalBinaryCounterexample_iff_finitePrimeResidueCoverPackage
    {m : Nat} :
    MinimalBinaryGoldbachCounterexample m ↔
      MinimalCounterexampleFinitePrimeResidueCover m := by
  constructor
  · exact minimalCounterexampleFinitePrimeResidueCover_of_minimalBinaryCounterexample
  · intro h
    exact h.1

/-- The residue-cover package and the finite prime-residue-cover package are
equivalent pointwise. -/
theorem minimalCounterexamplePrimeResidueCover_iff_finitePrimeResidueCover
    {m : Nat} :
    MinimalCounterexamplePrimeResidueCover m ↔
      MinimalCounterexampleFinitePrimeResidueCover m := by
  rw [← minimalBinaryCounterexample_iff_primeResidueCoverPackage,
    ← minimalBinaryCounterexample_iff_finitePrimeResidueCoverPackage]

/-- The exact goal is equivalent to the nonexistence of a minimal
counterexample carrying its forced prime-divisor cover. -/
theorem binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeDivisorCover :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeDivisorCover m := by
  rw [binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample]
  constructor
  · intro hno hcover
    rcases hcover with ⟨m, hm⟩
    exact hno ⟨m, minimalBinaryCounterexample_iff_primeDivisorCoverPackage.mpr hm⟩
  · intro hno hminimal
    rcases hminimal with ⟨m, hm⟩
    exact hno
      ⟨m, minimalBinaryCounterexample_iff_primeDivisorCoverPackage.mp hm⟩

/-- The current machine-status tail target is equivalent to ruling out the
sieve-shaped minimal counterexample package. -/
theorem currentFormalTarget50000_iff_no_minimalCounterexamplePrimeDivisorCover :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeDivisorCover m :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.symm.trans
    binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeDivisorCover

/-- The same equivalence stated directly for the remaining Lean target. -/
theorem explicitLowerBound50000_iff_no_minimalCounterexamplePrimeDivisorCover :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeDivisorCover m := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_iff_no_minimalCounterexamplePrimeDivisorCover

/-- A future proof may close the exact binary Goldbach statement by ruling out
the sieve-shaped minimal counterexample package. -/
theorem binaryGoldbachConjecture_of_no_minimalCounterexamplePrimeDivisorCover
    (h : ¬ ∃ m : Nat, MinimalCounterexamplePrimeDivisorCover m) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeDivisorCover.mpr h

/-- The exact goal is equivalently the nonexistence of a minimal
counterexample carrying the forced prime-residue cover. -/
theorem binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeResidueCover :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeResidueCover m := by
  rw [binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample]
  constructor
  · intro hno hcover
    rcases hcover with ⟨m, hm⟩
    exact hno ⟨m, minimalBinaryCounterexample_iff_primeResidueCoverPackage.mpr hm⟩
  · intro hno hminimal
    rcases hminimal with ⟨m, hm⟩
    exact hno
      ⟨m, minimalBinaryCounterexample_iff_primeResidueCoverPackage.mp hm⟩

/-- The current machine-status tail target is equivalent to ruling out the
residue-cover minimal counterexample package. -/
theorem currentFormalTarget50000_iff_no_minimalCounterexamplePrimeResidueCover :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeResidueCover m :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.symm.trans
    binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeResidueCover

/-- The same residue-cover equivalence stated directly for the remaining
Lean target. -/
theorem explicitLowerBound50000_iff_no_minimalCounterexamplePrimeResidueCover :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexamplePrimeResidueCover m := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_iff_no_minimalCounterexamplePrimeResidueCover

/-- A future proof may close the exact binary Goldbach statement by ruling out
the residue-cover minimal counterexample package. -/
theorem binaryGoldbachConjecture_of_no_minimalCounterexamplePrimeResidueCover
    (h : ¬ ∃ m : Nat, MinimalCounterexamplePrimeResidueCover m) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeResidueCover.mpr h

/-- The exact goal is equivalently the nonexistence of a minimal
counterexample carrying the forced finite prime-residue cover. -/
theorem binaryGoldbachConjecture_iff_no_minimalCounterexampleFinitePrimeResidueCover :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ ∃ m : Nat, MinimalCounterexampleFinitePrimeResidueCover m := by
  rw [binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample]
  constructor
  · intro hno hcover
    rcases hcover with ⟨m, hm⟩
    exact hno
      ⟨m, minimalBinaryCounterexample_iff_finitePrimeResidueCoverPackage.mpr hm⟩
  · intro hno hminimal
    rcases hminimal with ⟨m, hm⟩
    exact hno
      ⟨m, minimalBinaryCounterexample_iff_finitePrimeResidueCoverPackage.mp hm⟩

/-- The current machine-status tail target is equivalent to ruling out the
finite prime-residue-cover minimal counterexample package. -/
theorem currentFormalTarget50000_iff_no_minimalCounterexampleFinitePrimeResidueCover :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexampleFinitePrimeResidueCover m :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.symm.trans
    binaryGoldbachConjecture_iff_no_minimalCounterexampleFinitePrimeResidueCover

/-- The same finite-cover equivalence stated directly for the remaining Lean
target. -/
theorem explicitLowerBound50000_iff_no_minimalCounterexampleFinitePrimeResidueCover :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ ∃ m : Nat, MinimalCounterexampleFinitePrimeResidueCover m := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_iff_no_minimalCounterexampleFinitePrimeResidueCover

/-- A future proof may close the exact binary Goldbach statement by ruling out
the finite prime-residue-cover minimal counterexample package. -/
theorem binaryGoldbachConjecture_of_no_minimalCounterexampleFinitePrimeResidueCover
    (h : ¬ ∃ m : Nat, MinimalCounterexampleFinitePrimeResidueCover m) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_no_minimalCounterexampleFinitePrimeResidueCover.mpr h

/-- The finite-residue-escape obligation closes the exact binary Goldbach
statement: an escaping lower-half prime gives a half-witness, contradicting
minimality of any alleged counterexample. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueEscape
    (hesc : MinimalCounterexampleFiniteResidueEscape) :
    Round1Status.BinaryGoldbachConjecture := by
  refine binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.mpr ?_
  intro hminimal
  rcases hminimal with ⟨m, hm⟩
  have hhalf : GoldbachHalfWitness m :=
    halfWitness_of_finiteResidueEscape (hesc m hm)
  exact not_halfWitness_of_minimalBinaryCounterexample hm hhalf

/-- The exact binary Goldbach statement supplies the finite-residue-escape
obligation vacuously, since it rules out all minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueEscape_of_binaryGoldbachConjecture
    (hgoal : Round1Status.BinaryGoldbachConjecture) :
    MinimalCounterexampleFiniteResidueEscape := by
  intro m hm
  have hno : ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m :=
    binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.mp hgoal
  exact False.elim (hno ⟨m, hm⟩)

/-- The finite-residue-escape obligation is an exact reformulation of the
binary Goldbach target under the current minimal-counterexample setup. -/
theorem binaryGoldbachConjecture_iff_minimalCounterexampleFiniteResidueEscape :
    Round1Status.BinaryGoldbachConjecture ↔
      MinimalCounterexampleFiniteResidueEscape :=
  ⟨minimalCounterexampleFiniteResidueEscape_of_binaryGoldbachConjecture,
   binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueEscape⟩

/-- The current machine-status tail target is equivalent to the
finite-residue-escape obligation. -/
theorem currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueEscape :
    Round1Status.CurrentFormalTarget50000 ↔
      MinimalCounterexampleFiniteResidueEscape :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.symm.trans
    binaryGoldbachConjecture_iff_minimalCounterexampleFiniteResidueEscape

/-- The same finite-residue-escape equivalence stated directly for the
remaining Lean target. -/
theorem explicitLowerBound50000_iff_minimalCounterexampleFiniteResidueEscape :
    ExplicitGoldbachLowerBound 50000 ↔
      MinimalCounterexampleFiniteResidueEscape := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueEscape

/-- A future proof of the finite-residue-escape obligation closes the literal
remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueEscape
    (hesc : MinimalCounterexampleFiniteResidueEscape) :
    ExplicitGoldbachLowerBound 50000 := by
  exact explicitLowerBound50000_iff_minimalCounterexampleFiniteResidueEscape.mpr hesc

/-- The finite cardinality-surplus obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSurplus) :
    MinimalCounterexampleFiniteResidueEscape := by
  intro m hm
  exact lowerHalfPrimeFiniteResidueEscape_of_residueSurplus (hsurplus m hm)

/-- A future proof of the finite cardinality-surplus obligation closes the
exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueEscape
    (minimalCounterexampleFiniteResidueEscape_of_residueSurplus hsurplus)

/-- A future proof of the finite cardinality-surplus obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
      hsurplus)

/-- A future proof of the finite cardinality-surplus obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSurplus
      hsurplus

/-- The finite union-bound-surplus obligation supplies the finite
cardinality-surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_unionBoundSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueUnionBoundSurplus) :
    MinimalCounterexampleFiniteResidueSurplus := by
  intro m hm
  exact lowerHalfPrimeResidueSurplus_of_unionBoundSurplus (hsurplus m hm)

/-- The finite union-bound-surplus obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_unionBoundSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueUnionBoundSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_unionBoundSurplus hsurplus)

/-- A future proof of the finite union-bound-surplus obligation closes the
exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueUnionBoundSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueUnionBoundSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_unionBoundSurplus hsurplus)

/-- A future proof of the finite union-bound-surplus obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueUnionBoundSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueUnionBoundSurplus
      hsurplus)

/-- A future proof of the finite union-bound-surplus obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueUnionBoundSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus
      hsurplus

/-- The finite small/large split-surplus obligation supplies the finite
cardinality-surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_splitSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact lowerHalfPrimeResidueSurplus_of_splitSurplus hR

/-- The finite small/large split-surplus obligation supplies the
finite-residue escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_splitSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_splitSurplus hsurplus)

/-- A future proof of the finite small/large split-surplus obligation closes
the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSplitSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_splitSurplus hsurplus)

/-- A future proof of the finite small/large split-surplus obligation closes
the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSplitSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSplitSurplus
      hsurplus)

/-- A future proof of the finite small/large split-surplus obligation closes
the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSplitSurplus
    (hsurplus : MinimalCounterexampleFiniteResidueSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSplitSurplus
      hsurplus

/-- The two-range small-union-bound split obligation supplies the split
surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSplitSurplus_of_smallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    MinimalCounterexampleFiniteResidueSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSplitSurplus_of_smallUnionBoundSplitSurplus hR⟩

/-- The two-range small-union-bound split obligation supplies the finite
cardinality-surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_smallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_splitSurplus
    (minimalCounterexampleFiniteResidueSplitSurplus_of_smallUnionBoundSplitSurplus
      hsurplus)

/-- The two-range small-union-bound split obligation supplies the
finite-residue escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_smallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallUnionBoundSplitSurplus
      hsurplus)

/-- A future proof of the two-range small-union-bound split obligation closes
the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallUnionBoundSplitSurplus
      hsurplus)

/-- A future proof of the two-range small-union-bound split obligation closes
the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus
      hsurplus)

/-- A future proof of the two-range small-union-bound split obligation closes
the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus
      hsurplus

/-- The cofactor-pair two-range obligation supplies the small-union-bound
split obligation. -/
theorem minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus
      hR⟩

/-- The cofactor-pair two-range obligation supplies the finite cardinality
surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_smallUnionBoundSplitSurplus
    (minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus
      hsurplus)

/-- The cofactor-pair two-range obligation supplies the finite-residue escape
obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_cofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-pair two-range obligation closes the exact
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-pair two-range obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-pair two-range obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
      hsurplus

/-- The bounded-cofactor two-range obligation supplies the cofactor-pair
two-range obligation. -/
theorem minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_boundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_boundedCofactorSplitSurplus
      hR⟩

/-- Conversely, the cofactor-pair two-range obligation supplies the bounded
cofactor two-range obligation because the two local criteria are equivalent. -/
theorem minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorSplitSurplus
      hR⟩

/-- The cofactor-pair and bounded-cofactor minimal-counterexample obligations
are equivalent. -/
theorem minimalCounterexampleFiniteResidueCofactorSplitSurplus_iff_boundedCofactorSplitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus :=
  ⟨minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorSplitSurplus,
    minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_boundedCofactorSplitSurplus⟩

/-- The bounded-cofactor two-range obligation supplies the finite cardinality
surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_boundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_boundedCofactorSplitSurplus
      hsurplus)

/-- The bounded-cofactor two-range obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_boundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_boundedCofactorSplitSurplus
      hsurplus)

/-- A future proof of the bounded-cofactor two-range obligation closes the
exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_boundedCofactorSplitSurplus
      hsurplus)

/-- A future proof of the bounded-cofactor two-range obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus
      hsurplus)

/-- A future proof of the bounded-cofactor two-range obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus
      hsurplus

/-- The cofactor-box two-range obligation supplies the bounded-cofactor
two-range obligation. -/
theorem minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus
      hR⟩

/-- The cofactor-box two-range obligation supplies the finite cardinality
surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_boundedCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus
      hsurplus)

/-- The cofactor-box two-range obligation supplies the finite-residue escape
obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_cofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box two-range obligation closes the exact
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box two-range obligation closes the current
machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box two-range obligation closes the literal
remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus
      hsurplus

/-- The cofactor-box product two-range obligation supplies the cofactor-box
two-range obligation. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus
      hR⟩

/-- Conversely, the cofactor-box two-range obligation supplies the product
form because the local interval-cardinality simplification is exact. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus_of_cofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorBoxSplitSurplus
      hR⟩

/-- The cofactor-box and cofactor-box product minimal-counterexample
obligations are equivalent. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_iff_cofactorBoxProductSplitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus :=
  ⟨minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus_of_cofactorBoxSplitSurplus,
    minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus⟩

/-- The cofactor-box product two-range obligation supplies the finite
cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus
      hsurplus)

/-- The cofactor-box product two-range obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_cofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box product two-range obligation closes the
exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box product two-range obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus
      hsurplus)

/-- A future proof of the cofactor-box product two-range obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus
      hsurplus

/-- The prime-counting window two-range obligation supplies the cofactor-box
product two-range obligation. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
      hR⟩

/-- The prime-counting window obligation supplies the cofactor-box product
obligation with the required side condition `R < m` kept explicit. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt_of_cofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R, hR.1,
    lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
      hR⟩

/-- Conversely, a cofactor-box product witness with `R < m` supplies the
prime-counting window obligation. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorBoxProductSplitSurplusWithLt
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hRlt, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorBoxProductSplitSurplus_of_lt
      hRlt hR⟩

/-- The prime-counting window minimal-counterexample obligation is exactly the
cofactor-box product obligation together with the side condition `R < m`. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_iff_cofactorBoxProductSplitSurplusWithLt :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt :=
  ⟨minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt_of_cofactorPrimeCountingSplitSurplus,
    minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorBoxProductSplitSurplusWithLt⟩

/-- The cofactor-box product-with-`R < m` obligation supplies the finite
cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplusWithLt
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt) :
    MinimalCounterexampleFiniteResidueSurplus := by
  exact minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus
    (fun m hm => by
      rcases hsurplus m hm with ⟨R, _hRlt, hR⟩
      exact ⟨R, hR⟩)

/-- A future proof of the cofactor-box product-with-`R < m` obligation closes
the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplusWithLt
      hsurplus)

/-- A future proof of the cofactor-box product-with-`R < m` obligation closes
the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt
      hsurplus)

/-- A future proof of the cofactor-box product-with-`R < m` obligation closes
the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt
      hsurplus

/-- The prime-counting window two-range obligation supplies the finite
cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus
      hsurplus)

/-- The prime-counting window two-range obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_cofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingSplitSurplus
      hsurplus)

/-- A future proof of the prime-counting window two-range obligation closes
the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingSplitSurplus
      hsurplus)

/-- A future proof of the prime-counting window two-range obligation closes
the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus
      hsurplus)

/-- A future proof of the prime-counting window two-range obligation closes
the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus
      hsurplus

/-- The full prime-counting two-range obligation supplies the prime-counting
window two-range obligation. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus
      hR⟩

/-- Conversely, the prime-counting window two-range obligation supplies the
full prime-counting form because the local lower-half-prime cardinality
rewrite is exact. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_cofactorPrimeCountingSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_cofactorPrimeCountingSplitSurplus
      hR⟩

/-- The prime-counting window and full prime-counting minimal-counterexample
obligations are equivalent. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus :=
  ⟨minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_cofactorPrimeCountingSplitSurplus,
    minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus⟩

/-- The full prime-counting two-range obligation supplies the finite
cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The full prime-counting two-range obligation supplies the finite-residue
escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_cofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the full prime-counting two-range obligation closes the
exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the full prime-counting two-range obligation closes the
current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the full prime-counting two-range obligation closes the
literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
      hsurplus

/-- Generic exact-strength diagnostic for minimal-counterexample handoffs.

Any obligation of the form "every induction-ready minimal counterexample
satisfies `P`" is exactly as strong as ruling out induction-ready minimal
counterexamples, once a proof of that obligation is known to close the binary
Goldbach target.  The reverse direction is vacuous after minimal
counterexamples have been ruled out. -/
theorem minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
    {P : Nat → Prop}
    (hclose :
      (∀ m : Nat, MinimalBinaryGoldbachCounterexample m → P m) →
        Round1Status.BinaryGoldbachConjecture) :
    (∀ m : Nat, MinimalBinaryGoldbachCounterexample m → P m) ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  constructor
  · intro hP
    exact binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.mp
      (hclose hP)
  · intro hno m hm
    exact False.elim (hno ⟨m, hm⟩)

/-- The same generic diagnostic stated against the current `50000` tail
target. -/
theorem minimalCounterexampleObligation_iff_explicitLowerBound50000
    {P : Nat → Prop}
    (hclose :
      (∀ m : Nat, MinimalBinaryGoldbachCounterexample m → P m) →
        Round1Status.BinaryGoldbachConjecture) :
    (∀ m : Nat, MinimalBinaryGoldbachCounterexample m → P m) ↔
      ExplicitGoldbachLowerBound 50000 :=
  (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
    (P := P) hclose).trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The finite-residue escape handoff is exact-strength: it is equivalent to
there being no induction-ready minimal binary counterexample. -/
theorem minimalCounterexampleFiniteResidueEscape_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueEscape ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [MinimalCounterexampleFiniteResidueEscape] using
    (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
      (P := fun m => LowerHalfPrimeFiniteResidueEscape m)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueEscape)

/-- The finite-residue escape handoff is exactly the current remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueEscape_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueEscape ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueEscape_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The finite cardinality-surplus handoff is exact-strength once stated over
induction-ready minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSurplus_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueSurplus ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [MinimalCounterexampleFiniteResidueSurplus] using
    (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
      (P := fun m => LowerHalfPrimeResidueSurplus m)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus)

/-- The finite cardinality-surplus handoff is exactly the current remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSurplus ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueSurplus_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The finite union-bound surplus handoff is also exact-strength. -/
theorem minimalCounterexampleFiniteResidueUnionBoundSurplus_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueUnionBoundSurplus ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [MinimalCounterexampleFiniteResidueUnionBoundSurplus] using
    (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
      (P := fun m => LowerHalfPrimeResidueUnionBoundSurplus m)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueUnionBoundSurplus)

/-- The finite union-bound surplus handoff is exactly the current remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueUnionBoundSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueUnionBoundSurplus ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueUnionBoundSurplus_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The cofactor-box-product-with-`R < m` handoff is exact-strength, not a
weaker independent target. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt] using
    (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
      (P := fun m =>
        ∃ R : Nat,
          R < m ∧
            LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus
              m R)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt)

/-- The cofactor-box-product-with-`R < m` handoff is exactly the current
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplusWithLt_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The full prime-counting two-range handoff is exact-strength once it is
quantified over induction-ready minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus] using
    (minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample
      (P := fun m =>
        ∃ R : Nat,
          LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
            m R)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus)

/-- The full prime-counting two-range handoff is exactly the current remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The point-bound full prime-counting two-range obligation supplies the
full prime-counting two-range obligation with the exact small-modulus
union-bound sum. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
      hR⟩

/-- The point-bound full prime-counting two-range obligation supplies the
finite cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The point-bound full prime-counting two-range obligation supplies the
finite-residue escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the point-bound full prime-counting two-range obligation
closes the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the point-bound full prime-counting two-range obligation
closes the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the point-bound full prime-counting two-range obligation
closes the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus

/-- The parity-aware point-bound full prime-counting two-range obligation
supplies the full prime-counting two-range obligation with the exact
small-modulus union-bound sum. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus := by
  intro m hm
  rcases hsurplus m hm with ⟨R, hR⟩
  exact ⟨R,
    lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hR⟩

/-- The parity-aware point-bound full prime-counting two-range obligation
supplies the finite cardinality surplus obligation. -/
theorem minimalCounterexampleFiniteResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSurplus :=
  minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The parity-aware point-bound full prime-counting two-range obligation
supplies the finite-residue escape obligation. -/
theorem minimalCounterexampleFiniteResidueEscape_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueEscape :=
  minimalCounterexampleFiniteResidueEscape_of_residueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the parity-aware point-bound full prime-counting
two-range obligation closes the exact binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus
    (minimalCounterexampleFiniteResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the parity-aware point-bound full prime-counting
two-range obligation closes the current machine-status target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the parity-aware point-bound full prime-counting
two-range obligation closes the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
      hsurplus

/-- A deliberately crude elementary upper bound for the prime-counting
function.  It is strong enough to diagnose that the point-bound small-modulus
handoff below has overshot: a single small modulus already consumes the whole
target scale. -/
theorem primeCounting_le_half_add_one (N : Nat) :
    Nat.primeCounting N ≤ N / 2 + 1 := by
  by_cases hN : 2 ≤ N
  · have hpc := Nat.primeCounting'_add_le (a := 2) (k := 3)
      (by norm_num) (by norm_num) (N - 2)
    have harg : 3 + (N - 2) = N + 1 := by omega
    have hpc' : Nat.primeCounting' (N + 1) ≤
        Nat.primeCounting' 3 + Nat.totient 2 * ((N - 2) / 2 + 1) := by
      simpa [harg] using hpc
    have hprime3 : Nat.primeCounting' 3 = 1 := by decide
    have htot : Nat.totient 2 = 1 := by decide
    have hmain : Nat.primeCounting N ≤ 1 + ((N - 2) / 2 + 1) := by
      simpa [Nat.primeCounting, hprime3, htot] using hpc'
    have hdiv : 1 + ((N - 2) / 2 + 1) ≤ N / 2 + 1 := by omega
    exact le_trans hmain hdiv
  · have hNle : N ≤ 1 := by omega
    have hzero : Nat.primeCounting N = 0 :=
      Nat.primeCounting_eq_zero_iff.mpr hNle
    omega

/-- For `m ≥ 8`, the interval below `m` already contains the primes `2` and
`3`. -/
theorem two_le_primeCounting_pred_of_eight_le {m : Nat} (hm : 8 ≤ m) :
    2 ≤ Nat.primeCounting (m - 1) := by
  have hmono : Nat.primeCounting 3 ≤ Nat.primeCounting (m - 1) :=
    Nat.monotone_primeCounting (by omega)
  have hpi3 : Nat.primeCounting 3 = 2 := by decide
  omega

/-- For `m ≥ 8`, the interval below `m` already contains the four primes
`2`, `3`, `5`, and `7`. -/
theorem four_le_primeCounting_pred_of_eight_le {m : Nat} (hm : 8 ≤ m) :
    4 ≤ Nat.primeCounting (m - 1) := by
  have hmono : Nat.primeCounting 7 ≤ Nat.primeCounting (m - 1) :=
    Nat.monotone_primeCounting (by omega)
  have hpi7 : Nat.primeCounting 7 = 4 := by decide
  omega

/-- Once the small-modulus threshold reaches `3`, the parity-aware point-bound
sum already contains the sharp `r = 2` contribution and the generic `r = 3`
contribution. -/
theorem parityPointBoundSum_ge_two_three_of_three_le
    {m R : Nat} (hm : 8 ≤ m) (hR : 3 ≤ R) :
    1 + (m / 2 / 3 + 1) ≤
      BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
  classical
  let S := PrimeModuliBelowAtMost m R
  let pointTerm : Nat → Nat := fun r => m / 2 / r + 1
  have h2mem : 2 ∈ S := by
    simp [S, PrimeModuliBelowAtMost, mem_primeModuliBelow_iff, Nat.prime_two]
    omega
  have h3mem : 3 ∈ S.erase 2 := by
    simp [S, PrimeModuliBelowAtMost, mem_primeModuliBelow_iff,
      Nat.prime_three]
    omega
  have h3le : pointTerm 3 ≤ (S.erase 2).sum pointTerm := by
    exact Finset.single_le_sum
      (fun r _hr => Nat.zero_le (pointTerm r)) h3mem
  have h3le' : m / 2 / 3 + 1 ≤ (S.erase 2).sum pointTerm := by
    simpa [pointTerm] using h3le
  have hdef :
      BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R =
        1 + (S.erase 2).sum pointTerm := by
    simp [BadLowerHalfPrimeSmallResidueClassParityPointBoundSum, S,
      pointTerm, h2mem]
  rw [hdef]
  omega

/-- Once the small-modulus threshold reaches `5`, the parity-aware point-bound
sum contains the sharp `r = 2` contribution and the generic `r = 3, 5`
contributions. -/
theorem parityPointBoundSum_ge_two_three_five_of_five_le
    {m R : Nat} (hm : 8 ≤ m) (hR : 5 ≤ R) :
    1 + (m / 2 / 3 + 1) + (m / 2 / 5 + 1) ≤
      BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
  classical
  let S := PrimeModuliBelowAtMost m R
  let pointTerm : Nat → Nat := fun r => m / 2 / r + 1
  have h2mem : 2 ∈ S := by
    simp [S, PrimeModuliBelowAtMost, mem_primeModuliBelow_iff, Nat.prime_two]
    omega
  have h3mem : 3 ∈ S.erase 2 := by
    simp [S, PrimeModuliBelowAtMost, mem_primeModuliBelow_iff,
      Nat.prime_three]
    omega
  have h5mem : 5 ∈ (S.erase 2).erase 3 := by
    simp [S, PrimeModuliBelowAtMost, mem_primeModuliBelow_iff,
      Nat.prime_five]
    omega
  have hsplit :
      (S.erase 2).sum pointTerm =
        pointTerm 3 + ((S.erase 2).erase 3).sum pointTerm := by
    exact (Finset.add_sum_erase (S.erase 2) pointTerm h3mem).symm
  have h5le : pointTerm 5 ≤ ((S.erase 2).erase 3).sum pointTerm := by
    exact Finset.single_le_sum
      (fun r _hr => Nat.zero_le (pointTerm r)) h5mem
  have hpair :
      m / 2 / 3 + 1 + (m / 2 / 5 + 1) ≤
        (S.erase 2).sum pointTerm := by
    rw [hsplit]
    simpa [pointTerm] using Nat.add_le_add_left h5le (pointTerm 3)
  have hdef :
      BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R =
        1 + (S.erase 2).sum pointTerm := by
    simp [BadLowerHalfPrimeSmallResidueClassParityPointBoundSum, S,
      pointTerm, h2mem]
  rw [hdef]
  omega

/-- Catch for the point-bound split handoff: once `m ≥ 8`, the elementary
point-bound criterion is impossible for every threshold `R`.

If `R ≥ 2`, the small-modulus sum already includes the modulus `2`, giving
`m / 2 / 2 + 1`, while `π(m / 2) ≤ (m / 2) / 2 + 1`.  If `R < 2`, the
large-modulus cofactor window is already too large because the primes `2` and
`3` both lie below `m`. -/
theorem not_lowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le
    {m R : Nat} (hm : 8 ≤ m) :
    ¬ LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
        m R := by
  intro h
  rcases h with ⟨_hRltm, hineq⟩
  have hpi_le : Nat.primeCounting (m / 2) ≤ (m / 2) / 2 + 1 :=
    primeCounting_le_half_add_one (m / 2)
  by_cases hR2 : 2 ≤ R
  · have hmem2 : 2 ∈ PrimeModuliBelowAtMost m R := by
      simp [PrimeModuliBelowAtMost, mem_primeModuliBelow_iff, Nat.prime_two,
        hR2]
      omega
    have hsmall_ge :
        m / 2 / 2 + 1 ≤
          BadLowerHalfPrimeSmallResidueClassPointBoundSum m R := by
      simpa [BadLowerHalfPrimeSmallResidueClassPointBoundSum] using
        (Finset.single_le_sum
          (s := PrimeModuliBelowAtMost m R)
          (f := fun r => m / 2 / r + 1)
          (fun r _hr => Nat.zero_le (m / 2 / r + 1)) hmem2)
    have hsmall_lt :
        BadLowerHalfPrimeSmallResidueClassPointBoundSum m R <
          Nat.primeCounting (m / 2) := by
      exact lt_of_le_of_lt (by omega) hineq
    omega
  · have hRlt2 : R < 2 := Nat.lt_of_not_ge hR2
    have hpi_m_ge : 2 ≤ Nat.primeCounting (m - 1) :=
      two_le_primeCounting_pred_of_eight_le hm
    interval_cases R
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 0 := by
        have hzero : Nat.primeCounting 0 = 0 :=
          Nat.primeCounting_eq_zero_iff.mpr (by omega)
        omega
      have hlarge_ge :
          2 * (m - 1) ≤
            (Nat.primeCounting (m - 1) - Nat.primeCounting 0) *
              (m / (0 + 1) - 1) := by
        have hfactor : m / (0 + 1) - 1 = m - 1 := by omega
        rw [hfactor]
        exact Nat.mul_le_mul_right (m - 1) hwindow
      have hlarge_lt :
          (Nat.primeCounting (m - 1) - Nat.primeCounting 0) *
              (m / (0 + 1) - 1) <
            Nat.primeCounting (m / 2) := by
        exact lt_of_le_of_lt (by omega) hineq
      have hgt : (m / 2) / 2 + 1 < 2 * (m - 1) := by omega
      omega
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 1 := by
        have hone : Nat.primeCounting 1 = 0 :=
          Nat.primeCounting_eq_zero_iff.mpr (by omega)
        omega
      have hlarge_ge :
          2 * (m / 2 - 1) ≤
            (Nat.primeCounting (m - 1) - Nat.primeCounting 1) *
              (m / (1 + 1) - 1) := by
        exact Nat.mul_le_mul_right (m / 2 - 1) hwindow
      have hlarge_lt :
          (Nat.primeCounting (m - 1) - Nat.primeCounting 1) *
              (m / (1 + 1) - 1) <
            Nat.primeCounting (m / 2) := by
        exact lt_of_le_of_lt (by omega) hineq
      have hgt : (m / 2) / 2 + 1 < 2 * (m / 2 - 1) := by omega
      omega

/-- Consequently, the point-bound minimal-counterexample obligation rules out
minimal counterexamples only because its local inequality cannot hold at any
candidate minimal counterexample. -/
theorem no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus) :
    ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  rintro ⟨m, hm⟩
  rcases hsurplus m hm with ⟨R, hR⟩
  exact
    not_lowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le
      (by have hmgt : 50000 < m := hm.2.1; omega) hR

/-- The point-bound minimal-counterexample obligation is therefore equivalent
to the absence of minimal binary counterexamples, not a separate viable
large-counterexample inequality. -/
theorem minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  constructor
  · exact
      no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus
  · intro hno m hm
    exact False.elim (hno ⟨m, hm⟩)

/-- The crude point-bound minimal-counterexample obligation is exactly as
strong as the exact `goal.md` binary Goldbach statement.  It is therefore a
diagnostic dead end, not a separate easier sieve route. -/
theorem minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_binaryGoldbachConjecture :
    MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      Round1Status.BinaryGoldbachConjecture :=
  minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample.trans
    binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.symm

/-- Under the current finite certificate, the crude point-bound
minimal-counterexample obligation is exactly as strong as the remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The same crude point-bound dead end, stated in the project status-layer
target vocabulary. -/
theorem minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_currentFormalTarget50000 :
    MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      Round1Status.CurrentFormalTarget50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000

/-- The crude point-bound dead end is also exactly the lower-half witness tail
target above the current finite certificate. -/
theorem minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_halfWitnessLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      GoldbachHalfWitnessLowerBound 50000 :=
  minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000.trans
    (explicitLowerBound_iff_halfWitnessLowerBound 50000)

/-- Catch for the parity-aware point-bound split handoff: separating the
modulus `2` still does not make the point-bound criterion viable.

For thresholds `R < 5`, the large-modulus cofactor window is already too large
using only the small primes below `m`.  For thresholds `R ≥ 5`, the small
point-bound sum already includes the `2`, `3`, and `5` contributions, which is
at least the crude upper bound for `π(m / 2)`. -/
theorem not_lowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le
    {m R : Nat} (hm : 8 ≤ m) :
    ¬ LowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
        m R := by
  intro h
  rcases h with ⟨_hmEven, _hRltm, hineq⟩
  have hpi_le : Nat.primeCounting (m / 2) ≤ (m / 2) / 2 + 1 :=
    primeCounting_le_half_add_one (m / 2)
  by_cases hR5 : 5 ≤ R
  · have hsmall_ge :=
      parityPointBoundSum_ge_two_three_five_of_five_le hm hR5
    have hactual_ge_pi :
        Nat.primeCounting (m / 2) ≤
          BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R +
              (Nat.primeCounting (m - 1) - Nat.primeCounting R) *
                (m / (R + 1) - 1) := by
      have hupper_le_small :
          (m / 2) / 2 + 1 ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m R := by
        omega
      omega
    omega
  · have hRlt5 : R < 5 := Nat.lt_of_not_ge hR5
    have hpi_m_ge2 : 2 ≤ Nat.primeCounting (m - 1) :=
      two_le_primeCounting_pred_of_eight_le hm
    have hpi_m_ge4 : 4 ≤ Nat.primeCounting (m - 1) :=
      four_le_primeCounting_pred_of_eight_le hm
    interval_cases R
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 0 := by
        have hzero : Nat.primeCounting 0 = 0 :=
          Nat.primeCounting_eq_zero_iff.mpr (by omega)
        omega
      have hactual_ge_pi :
          Nat.primeCounting (m / 2) ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m 0 +
                (Nat.primeCounting (m - 1) - Nat.primeCounting 0) *
                  (m / (0 + 1) - 1) := by
        have hlarge_ge :
            2 * (m - 1) ≤
              (Nat.primeCounting (m - 1) - Nat.primeCounting 0) *
                (m / (0 + 1) - 1) := by
          have hfactor : m / (0 + 1) - 1 = m - 1 := by omega
          rw [hfactor]
          exact Nat.mul_le_mul_right (m - 1) hwindow
        omega
      omega
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 1 := by
        have hone : Nat.primeCounting 1 = 0 :=
          Nat.primeCounting_eq_zero_iff.mpr (by omega)
        omega
      have hactual_ge_pi :
          Nat.primeCounting (m / 2) ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m 1 +
                (Nat.primeCounting (m - 1) - Nat.primeCounting 1) *
                  (m / (1 + 1) - 1) := by
        have hlarge_ge :
            2 * (m / 2 - 1) ≤
              (Nat.primeCounting (m - 1) - Nat.primeCounting 1) *
                (m / (1 + 1) - 1) := by
          exact Nat.mul_le_mul_right (m / 2 - 1) hwindow
        omega
      omega
    · have hwindow :
          3 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 2 := by
        have hpi2 : Nat.primeCounting 2 = 1 := by decide
        omega
      have hactual_ge_pi :
          Nat.primeCounting (m / 2) ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m 2 +
                (Nat.primeCounting (m - 1) - Nat.primeCounting 2) *
                  (m / (2 + 1) - 1) := by
        have hlarge_ge :
            3 * (m / 3 - 1) ≤
              (Nat.primeCounting (m - 1) - Nat.primeCounting 2) *
                (m / (2 + 1) - 1) := by
          exact Nat.mul_le_mul_right (m / 3 - 1) hwindow
        omega
      omega
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 3 := by
        have hpi3 : Nat.primeCounting 3 = 2 := by decide
        omega
      have hsmall_ge :=
        parityPointBoundSum_ge_two_three_of_three_le (m := m) (R := 3)
          hm (by norm_num)
      have hactual_ge_pi :
          Nat.primeCounting (m / 2) ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m 3 +
                (Nat.primeCounting (m - 1) - Nat.primeCounting 3) *
                  (m / (3 + 1) - 1) := by
        have hlarge_ge :
            2 * (m / 4 - 1) ≤
              (Nat.primeCounting (m - 1) - Nat.primeCounting 3) *
                (m / (3 + 1) - 1) := by
          exact Nat.mul_le_mul_right (m / 4 - 1) hwindow
        omega
      omega
    · have hwindow :
          2 ≤ Nat.primeCounting (m - 1) - Nat.primeCounting 4 := by
        have hpi4 : Nat.primeCounting 4 = 2 := by decide
        omega
      have hsmall_ge :=
        parityPointBoundSum_ge_two_three_of_three_le (m := m) (R := 4)
          hm (by norm_num)
      have hactual_ge_pi :
          Nat.primeCounting (m / 2) ≤
            BadLowerHalfPrimeSmallResidueClassParityPointBoundSum m 4 +
                (Nat.primeCounting (m - 1) - Nat.primeCounting 4) *
                  (m / (4 + 1) - 1) := by
        have hlarge_ge :
            2 * (m / 5 - 1) ≤
              (Nat.primeCounting (m - 1) - Nat.primeCounting 4) *
                (m / (4 + 1) - 1) := by
          exact Nat.mul_le_mul_right (m / 5 - 1) hwindow
        omega
      omega

/-- Consequently, the parity-aware point-bound minimal-counterexample
obligation also rules out minimal counterexamples only because its local
inequality cannot hold at any candidate minimal counterexample. -/
theorem no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus) :
    ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  rintro ⟨m, hm⟩
  rcases hsurplus m hm with ⟨R, hR⟩
  exact
    not_lowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le
      (by have hmgt : 50000 < m := hm.2.1; omega) hR

/-- The parity-aware point-bound minimal-counterexample obligation is
therefore equivalent to the absence of minimal binary counterexamples, not a
separate viable large-counterexample inequality. -/
theorem minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample :
    MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  constructor
  · exact
      no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus
  · intro hno m hm
    exact False.elim (hno ⟨m, hm⟩)

/-- The parity-aware point-bound minimal-counterexample obligation is also
exactly as strong as the exact `goal.md` binary Goldbach statement. -/
theorem minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_binaryGoldbachConjecture :
    MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      Round1Status.BinaryGoldbachConjecture :=
  minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample.trans
    binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample.symm

/-- Under the current finite certificate, the parity-aware point-bound
minimal-counterexample obligation is exactly as strong as the remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 :=
  minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample.trans
    explicitLowerBound50000_iff_no_minimalBinaryCounterexample.symm

/-- The same parity-aware point-bound dead end, stated in the project
status-layer target vocabulary. -/
theorem minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_currentFormalTarget50000 :
    MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      Round1Status.CurrentFormalTarget50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000

/-- The parity-aware point-bound dead end is also exactly the lower-half
witness tail target above the current finite certificate. -/
theorem minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_halfWitnessLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus ↔
      GoldbachHalfWitnessLowerBound 50000 :=
  minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000.trans
    (explicitLowerBound_iff_halfWitnessLowerBound 50000)

/-- A descent step from every induction-ready minimal counterexample rules out
all such minimal counterexamples. -/
theorem no_minimalBinaryCounterexample_of_descent
    (hdescent : MinimalBinaryCounterexampleDescent) :
    ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  intro h
  rcases h with ⟨m, hm⟩
  rcases hdescent m hm with ⟨n, hnm, hnCounter⟩
  exact hnCounter.2.2 (hm.2.2 n hnm hnCounter.1 hnCounter.2.1)

/-- The descent interface is equivalent to ruling out induction-ready
minimal counterexamples outright.  If a minimal counterexample existed, its
minimality would contradict any smaller counterexample returned by the
descent step; conversely, if no minimal counterexample exists, the descent
obligation is vacuous. -/
theorem minimalBinaryCounterexampleDescent_iff_no_minimalBinaryCounterexample :
    MinimalBinaryCounterexampleDescent ↔
      ¬ ∃ m : Nat, MinimalBinaryGoldbachCounterexample m := by
  constructor
  · exact no_minimalBinaryCounterexample_of_descent
  · intro hno m hm
    exact False.elim (hno ⟨m, hm⟩)

/-- Therefore a proof of the descent obligation closes the exact `goal.md`
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalBinaryCounterexampleDescent
    (hdescent : MinimalBinaryCounterexampleDescent) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_no_minimalBinaryCounterexample
    (no_minimalBinaryCounterexample_of_descent hdescent)

/-- The same descent obligation closes the current machine-status tail target. -/
theorem currentFormalTarget50000_of_minimalBinaryCounterexampleDescent
    (hdescent : MinimalBinaryCounterexampleDescent) :
    Round1Status.CurrentFormalTarget50000 :=
  Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000.mp
    (binaryGoldbachConjecture_of_minimalBinaryCounterexampleDescent hdescent)

/-- The same descent obligation closes the literal remaining Lean target. -/
theorem explicitLowerBound50000_of_minimalBinaryCounterexampleDescent
    (hdescent : MinimalBinaryCounterexampleDescent) :
    ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    currentFormalTarget50000_of_minimalBinaryCounterexampleDescent hdescent

/-- Proving the lower-half witness target above `50000` supplies the descent
interface, because any alleged minimal counterexample would already have a
witness at its own value. -/
theorem minimalBinaryCounterexampleDescent_of_halfWitnessLowerBound50000
    (hhalf : GoldbachHalfWitnessLowerBound 50000) :
    MinimalBinaryCounterexampleDescent := by
  intro m hm
  have hmwitness : GoldbachHalfWitness m :=
    hhalf m hm.2.1 hm.1.2.1
  exact False.elim
    (not_halfWitness_of_minimalBinaryCounterexample hm hmwitness)

/-- The descent obligation is logically equivalent to the exact binary
Goldbach statement.  The forward direction is the descent closure above; the
reverse direction is vacuous because the exact statement rules out the minimal
counterexample hypothesis. -/
theorem minimalBinaryCounterexampleDescent_iff_binaryGoldbachConjecture :
    MinimalBinaryCounterexampleDescent ↔
      Round1Status.BinaryGoldbachConjecture := by
  constructor
  · exact binaryGoldbachConjecture_of_minimalBinaryCounterexampleDescent
  · intro h m hm
    exact False.elim (hm.1.2.2 (h m hm.1.1 hm.1.2.1))

/-- The same descent obligation is exactly as strong as the current
`ExplicitGoldbachLowerBound 50000` target under the finite certificate. -/
theorem minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000 :
    MinimalBinaryCounterexampleDescent ↔ ExplicitGoldbachLowerBound 50000 :=
  minimalBinaryCounterexampleDescent_iff_binaryGoldbachConjecture.trans
    Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000

/-- The same exact-strength descent interface, stated in the project
status-layer target vocabulary. -/
theorem minimalBinaryCounterexampleDescent_iff_currentFormalTarget50000 :
    MinimalBinaryCounterexampleDescent ↔
      Round1Status.CurrentFormalTarget50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000

/-- The descent handoff is also exactly as strong as the lower-half witness
target above the current finite certificate. -/
theorem minimalBinaryCounterexampleDescent_iff_halfWitnessLowerBound50000 :
    MinimalBinaryCounterexampleDescent ↔
      GoldbachHalfWitnessLowerBound 50000 :=
  minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000.trans
    (explicitLowerBound_iff_halfWitnessLowerBound 50000)

/-- The descent handoff is equivalently the absence of lower-half witness
counterexamples above the current finite certificate. -/
theorem minimalBinaryCounterexampleDescent_iff_no_halfWitnessCounterexampleAbove50000 :
    MinimalBinaryCounterexampleDescent ↔
      ¬ ∃ n : Nat, GoldbachHalfWitnessCounterexampleAbove 50000 n :=
  minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000.trans
    (explicitLowerBound_iff_no_halfWitnessCounterexample_above 50000)

end CounterexampleReduction
end Gdbh
