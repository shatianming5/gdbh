/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T2 (Phase 19 / Path C — Mertens 1st UPPER bound)
-/
import Gdbh.PathC_MertensSecondProof
import Gdbh.PathC_MertensFirstClosure

/-!
# Path C — Mertens 1st theorem UPPER bound (P19-T2)

The existing chain (P14/P16/Phase-16 closure) closes the **two-sided**
absolute-value form

```
∃ B, ∃ z₀, ∀ z ≥ z₀,
  |Σ_{p ≤ z, p prime} log p / p − log z| ≤ B
```

as `Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds`.
Since `|x − y| ≤ B ↔ −B ≤ x − y ∧ x − y ≤ B`, the absolute-value form
gives **both** the lower bound (used by `MertensFirstTheoremBound` →
`MertensSecondLowerBoundFull` via Abel inversion) and the upper bound
needed for the Brun/Mertens 3rd lower-gap (Kernel B of Path C).

This file extracts the **upper direction** as a separately-named Prop
and closes it from the already-closed two-sided bound.

## Main results

* `MertensFirstTheoremUpperBound` — `∃ C, ∃ N₀, ∀ N ≥ N₀,
  Σ_{p ≤ N, p prime} log p / p ≤ log N + C`.
* `mertensFirstTheoremUpperBound_holds` — closure, axiom-clean.

## Note on indexing

The task spec asks for `(Finset.Icc 1 N).filter Nat.Prime`.  Because
`Nat.Prime p ↔ p ≥ 2 ∧ …`, the filter excludes `1`, so this set is
**equal** to `(Finset.Icc 2 N).filter Nat.Prime` (the form used by the
existing two-sided bound).  We prove this equality inline.
-/

namespace Gdbh
namespace PathCMertensFirstUpper

open Gdbh.PathCMertensSecondProof (MertensFirstTheoremBound)

/-- Mertens 1st theorem **UPPER bound**:
`Σ_{p ≤ N, p prime} log p / p ≤ log N + C` for some absolute
constant `C` and all `N ≥ N₀`.

The matching LOWER bound (and the symmetric two-sided form) is closed
in `PathC_MertensFirstClosure.mertensFirstTheoremBound_holds`. -/
def MertensFirstTheoremUpperBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (N : ℝ) + C

/-- The filter `Nat.Prime` over `Finset.Icc 1 N` and over `Finset.Icc 2 N`
yield the same set, since `1` is not prime. -/
lemma filter_prime_Icc_one_eq_Icc_two (N : ℕ) :
    (Finset.Icc 1 N).filter Nat.Prime = (Finset.Icc 2 N).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hpN⟩, hprime⟩
    have h2 : 2 ≤ p := hprime.two_le
    exact ⟨⟨h2, hpN⟩, hprime⟩
  · rintro ⟨⟨h2, hpN⟩, hprime⟩
    exact ⟨⟨by omega, hpN⟩, hprime⟩

/-- **Closure of `MertensFirstTheoremUpperBound`** (P19-T2).

Strategy:  The existing closure
`Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds`
gives the two-sided absolute-value bound

```
|Σ_{p ≤ z, p prime} log p / p − log z| ≤ B
```

From `|x − y| ≤ B` we extract `x − y ≤ B`, i.e.
`Σ ≤ log z + B`.  This is exactly the upper direction.

The `Finset.Icc 2 z` indexing of the existing bound matches our
`Finset.Icc 1 N` indexing after filtering by `Nat.Prime`, by the
lemma `filter_prime_Icc_one_eq_Icc_two`. -/
theorem mertensFirstTheoremUpperBound_holds :
    MertensFirstTheoremUpperBound := by
  -- Get the two-sided closed form.
  obtain ⟨B, z₀, hBound⟩ :=
    Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds
  -- Use the same constants for the upper direction.
  refine ⟨B, z₀, ?_⟩
  intro N hN
  -- Apply the two-sided bound at `z = N`.
  have habs := hBound N hN
  -- Translate `Icc 1 N` to `Icc 2 N` after filtering.
  rw [filter_prime_Icc_one_eq_Icc_two]
  -- `|x − y| ≤ B → x − y ≤ B → x ≤ y + B`.
  have hxy_le : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)) - Real.log (N : ℝ) ≤ B :=
    (abs_le.mp habs).2
  linarith

end PathCMertensFirstUpper
end Gdbh
