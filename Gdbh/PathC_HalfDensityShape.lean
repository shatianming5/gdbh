/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Goldbach Project Contributors
-/
import Gdbh.PathC_BasisHalfDensity

/-!
# Path C half-density shape handoff

This file records the exact output shape of the already-formalized
Schnirelmann half-density step when it is applied to
`PathCKGoldbach.primesSumset`.

If one proves the still-missing analytic input

```
  1 / 2 <= schnirelmannDensity PathCKGoldbach.primesSumset,
```

then the closed half-density theorem gives coverage by two elements of
`primesSumset`.  Since each `primesSumset` element is itself a sum of two
`primesAndOne` elements, the resulting endpoint is a four-summand
`primesAndOne` representation.  This is useful bookkeeping, but it is not
binary Goldbach: the list may contain four entries and may use the padding
values `0` and `1`.
-/

namespace Gdbh
namespace PathCHalfDensityShape

open Gdbh.PathCPrimesDensity (primesAndOne)
open Gdbh.PathCKGoldbach (primesSumset)

/-- Convert membership in `primesAndOne` to the predicate shape used by the
status and handoff files. -/
lemma prime_or_zero_or_one_of_primesAndOne {p : ℕ}
    (hp : primesAndOne p) : Nat.Prime p ∨ p = 0 ∨ p = 1 := by
  unfold primesAndOne at hp
  rcases hp with h0 | h1 | hPrime
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr h1)
  · exact Or.inl hPrime

/-- Applying the closed half-density basis theorem to `primesSumset` gives a
four-summand `primesAndOne` representation.

The analytic hypothesis here is intentionally strong and explicit: it is a
half-density statement for `primesSumset`, not a binary Goldbach conclusion.
The output list has length at most four and its entries may be primes, `0`,
or `1`. -/
theorem primesAndOne_fourSummandCoverage_of_primesSumset_halfDensity
    (hσ : (1 : ℝ) / 2 ≤ schnirelmannDensity primesSumset) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ 4 ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  intro n hn
  have hpair : sumset primesSumset primesSumset n :=
    Gdbh.PathCBasisHalfDensity.schnirelmannBasisHalfDensity_holds
      primesSumset
      Gdbh.PathCKGoldbach.primesSumset_zero
      Gdbh.PathCKGoldbach.primesSumset_one
      hσ n hn
  rw [sumset_iff] at hpair
  obtain ⟨a, b, ha, hb, hab⟩ := hpair
  unfold primesSumset at ha
  rw [sumset_iff] at ha
  obtain ⟨a1, a2, ha1, ha2, ha12⟩ := ha
  unfold primesSumset at hb
  rw [sumset_iff] at hb
  obtain ⟨b1, b2, hb1, hb2, hb12⟩ := hb
  refine ⟨[a1, a2, b1, b2], ?_, ?_, ?_⟩
  · simp
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact prime_or_zero_or_one_of_primesAndOne ha1
    · exact prime_or_zero_or_one_of_primesAndOne ha2
    · exact prime_or_zero_or_one_of_primesAndOne hb1
    · exact prime_or_zero_or_one_of_primesAndOne hb2
  · simp only [List.sum_cons, List.sum_nil]
    omega

end PathCHalfDensityShape
end Gdbh
