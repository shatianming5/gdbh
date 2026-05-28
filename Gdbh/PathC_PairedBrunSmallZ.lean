/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P17-T1 (Phase 17 / Path C — `PairedBrunSmallZClosed` sub-Prop)
-/
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_GoldbachRBound
import Gdbh.PathC_MertensProof

/-!
# Path C — `PairedBrunSmallZClosed` (small-`z` case, P17-T1)

This file is the **P17-T1 deliverable** in Phase 17 (Path C closure).
It closes the *small-`z`* slice of the named refined main-term Prop
`Gdbh.PathCBrunRefinedComposition.BrunGoldbachPairedMainTermRefined`.

## Mathematical content

`Gdbh.PathCMertensProof.pairedBrunFactor` is defined as

```
pairedBrunFactor z  =  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 - 2/p) ,
```

so for `z ≤ 2` the index set `(Finset.Icc 3 z).filter Nat.Prime` is empty
and the product collapses to `1` (the empty product).  Hence with `C₁ = 1`
the paired main-term inequality

```
goldbachSiftedPair n z  ≤  1 · n · pairedBrunFactor z + refinedReservoir n z
                        =  n + refinedReservoir n z
```

is *strictly* implied by the trivial cardinal bound
`goldbachSiftedPair n z ≤ n` (already in `PathC_GoldbachRBound.lean`),
together with non-negativity of the refined reservoir.

This is the first of six sub-Props in the Phase 17 decomposition of
`BrunGoldbachPairedMainTermRefined`.

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext` are transitively used.
-/

namespace Gdbh
namespace PathCPairedBrunSmallZ

open Gdbh.PathCGoldbachRBound (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir)

/-! ## Section 1 — The small-`z` slice of `pairedBrunFactor`

For `z ≤ 2`, the index set of `pairedBrunFactor z` is empty, so the
product is `1`. -/

/-- For `z ≤ 2`, the filtered Icc indexing `pairedBrunFactor` is empty. -/
lemma filter_prime_Icc3_eq_empty_of_le_two {z : ℕ} (hz : z ≤ 2) :
    (Finset.Icc 3 z).filter Nat.Prime = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro p hp
  rcases Finset.mem_Icc.mp hp with ⟨hp3, hpz⟩
  intro _hprime
  -- `3 ≤ p ≤ z ≤ 2` is impossible.
  omega

/-- For `z ≤ 2`, `pairedBrunFactor z = 1` (empty product). -/
lemma pairedBrunFactor_eq_one_of_le_two {z : ℕ} (hz : z ≤ 2) :
    pairedBrunFactor z = 1 := by
  unfold pairedBrunFactor
  rw [filter_prime_Icc3_eq_empty_of_le_two hz]
  exact Finset.prod_empty

/-! ## Section 2 — Non-negativity of the refined reservoir

The refined reservoir `n / (log n)^2` is non-negative for every
`n : ℕ`, since both numerator and denominator (a square) are
non-negative and division by zero is defined as `0` in `ℝ`. -/

/-- The refined reservoir is non-negative for every `n z : ℕ`. -/
lemma refinedReservoir_nonneg (n z : ℕ) :
    0 ≤ refinedReservoir n z := by
  unfold refinedReservoir
  exact div_nonneg (by exact_mod_cast Nat.zero_le _) (sq_nonneg _)

/-! ## Section 3 — The `PairedBrunSmallZClosed` Prop and its closure -/

/-- **`PairedBrunSmallZClosed`.**  For `z ≤ 2`, `pairedBrunFactor z = 1`
(empty product), so the paired main-term inequality holds with `C₁ = 1`
and the trivial bound `goldbachSiftedPair n z ≤ n`, plus non-negativity
of the refined reservoir.

This is the small-`z` slice of
`Gdbh.PathCBrunRefinedComposition.BrunGoldbachPairedMainTermRefined`. -/
def PairedBrunSmallZClosed : Prop :=
  ∀ n z : ℕ, 0 < n → z ≤ 2 →
    (Gdbh.PathCGoldbachRBound.goldbachSiftedPair n z : ℝ)
      ≤ 1 * (n : ℝ) * Gdbh.PathCMertensProof.pairedBrunFactor z
        + Gdbh.PathCBrunRefinedComposition.refinedReservoir n z

/-- **Closure of `PairedBrunSmallZClosed`.**  The trivial cardinal bound
`goldbachSiftedPair n z ≤ n`, combined with `pairedBrunFactor z = 1`
for `z ≤ 2` and `refinedReservoir n z ≥ 0`, closes the small-`z` slice. -/
theorem pairedBrunSmallZClosed_holds : PairedBrunSmallZClosed := by
  intro n z _hn hz
  -- `pairedBrunFactor z = 1` for `z ≤ 2`.
  have hM : pairedBrunFactor z = 1 := pairedBrunFactor_eq_one_of_le_two hz
  -- Trivial cardinal bound on `goldbachSiftedPair`.
  have hSift : (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le n z
  -- Refined reservoir is non-negative.
  have hRes : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
  -- Compute RHS.
  have hRHS :
      1 * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z
        = (n : ℝ) + refinedReservoir n z := by
    rw [hM]; ring
  -- Conclude.
  rw [hRHS]
  linarith

end PathCPairedBrunSmallZ
end Gdbh
