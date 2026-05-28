/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P21-T5 (Phase 21 / Path C — Finite enumeration closure of the
        FixA' inequality `FixAStrong_at_n n` for `n ∈ [4, 16]`, the
        small-`n` companion to the asymptotic T4 deliverable.)
-/
import Gdbh.PathC_FixAStrongReservoir
import Gdbh.PathC_DecidableSmallN

/-!
# Path C — P21-T5: Finite enumeration of `FixA'` at small `n`

## Mission

The FixA' chain Prop at the canonical sieve threshold `z = Nat.sqrt n`
takes the existential form

```
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (goldbachSiftedPair n √n : ℝ)
        ≤ C₁ · n · pairedBrunFactor √n
          + refinedReservoirCorrectedStrong n √n .
```

P21-T4 (the parallel asymptotic task) handles `n ≥ N_threshold` for
some threshold.  This file (P21-T5) is the **finite-enumeration**
companion:  it closes the `C₁ = 1` per-`n` form of the FixA' inequality

```
FixAStrong_at_n (n : ℕ) : Prop :=
  ∀ C₁ : ℝ, 1 ≤ C₁ →
    (goldbachSiftedPair n √n : ℝ)
      ≤ C₁ · n · pairedBrunFactor √n
        + refinedReservoirCorrectedStrong n √n
```

for every `n ∈ [4, 16]`, by explicit finite computation using the
already-closed strict Brun-Goldbach inequalities from
`Gdbh.PathCDecidableSmallN` (which give
`goldbachSiftedPair n √n ≤ n · pairedBrunFactor √n` for these `n`).

## Mathematical content

For `n ∈ [4, 16]`, the strict Brun-Goldbach inequality
`goldbachSiftedPair n √n ≤ n · pairedBrunFactor √n` holds (closed in
`Gdbh.PathCDecidableSmallN.strict_4 .. strict_16`).  With `C₁ ≥ 1` and
`pairedBrunFactor √n > 0`, the LHS

```
(goldbachSiftedPair n √n : ℝ)  ≤  n · pBF(√n)  ≤  C₁ · n · pBF(√n) .
```

Adding the (non-negative) FixA' reservoir on the right yields

```
(goldbachSiftedPair n √n : ℝ)  ≤  C₁ · n · pBF(√n) + reservoir' .
```

Reservoir non-negativity for `n ≥ 3` is closed in
`PathCFixAStrongReservoir.refinedReservoirCorrectedStrong_nonneg_of_three_le`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target:  `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.
* File **only adds**; it does not modify any other file.
-/

namespace Gdbh
namespace PathCFixAStrongSmallN

open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCFixAStrongReservoir
  (refinedReservoirCorrectedStrong refinedReservoirCorrectedStrong_def
   refinedReservoirCorrectedStrong_nonneg_of_three_le
   BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)
open Gdbh.PathCDecidableSmallN
  (strict_4 strict_5 strict_6 strict_7 strict_8
   strict_9 strict_10 strict_11 strict_12 strict_13
   strict_14 strict_15 strict_16)

/-! ## Section 1 — The per-`n` slice of FixA' at `C₁ ≥ 1`.

We expose `FixAStrong_at_n n`:  for every `C₁ ≥ 1`, the FixA'
inequality at this fixed `n` and at sieve threshold `√n` holds.  This
is the *closed quantifier form* of the per-`n` slice. -/

/-- **Per-`n` FixA' slice.**  For a fixed `n : ℕ`, the FixA' inequality
holds for every constant `C₁ ≥ 1`. -/
def FixAStrong_at_n (n : ℕ) : Prop :=
  ∀ C₁ : ℝ, 1 ≤ C₁ →
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + refinedReservoirCorrectedStrong n (Nat.sqrt n)

/-! ## Section 2 — Reduction from the strict Brun-Goldbach bound.

The closed strict bound `LHS ≤ n · pBF(√n)` combined with `C₁ ≥ 1` and
`pBF(√n) ≥ 0` gives `LHS ≤ C₁ · n · pBF(√n)`.  Adding the non-negative
FixA' reservoir on the right yields `FixAStrong_at_n n`. -/

/-- **Reduction lemma.**  Given the *strict* Brun-Goldbach bound

```
goldbachSiftedPair n √n ≤ n · pBF(√n)
```

and `n ≥ 3` (so the reservoir is non-negative), the per-`n` FixA'
inequality holds for every `C₁ ≥ 1`. -/
theorem fixAStrong_atN_of_strict
    {n : ℕ}
    (hn : 3 ≤ n)
    (hStrict : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                  ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)) :
    FixAStrong_at_n n := by
  intro C₁ hC₁
  -- Step 1:  C₁ · n · pBF(√n) ≥ 1 · n · pBF(√n) = n · pBF(√n).
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_pbf_pos : 0 < pairedBrunFactor (Nat.sqrt n) :=
    pairedBrunFactor_pos _
  have h_pbf_nn : 0 ≤ pairedBrunFactor (Nat.sqrt n) :=
    le_of_lt h_pbf_pos
  have h_n_pbf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
    mul_nonneg h_n_nn h_pbf_nn
  have h_main_ge :
      (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
    have h_step : 1 * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
                    ≤ C₁ * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) :=
      mul_le_mul_of_nonneg_right hC₁ h_n_pbf_nn
    have h_eq_l : 1 * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
                    = (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := one_mul _
    have h_eq_r : C₁ * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
                    = C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by ring
    linarith
  -- Step 2:  reservoir' ≥ 0 for n ≥ 3.
  have h_res_nn :
      (0 : ℝ) ≤ refinedReservoirCorrectedStrong n (Nat.sqrt n) :=
    refinedReservoirCorrectedStrong_nonneg_of_three_le n (Nat.sqrt n) hn
  -- Step 3:  combine.
  linarith

/-! ## Section 3 — Per-`n` closure for `n ∈ [4, 16]`.

For each `n ∈ [4, 16]`, the strict Brun-Goldbach inequality
`goldbachSiftedPair n √n ≤ n · pBF(√n)` is closed in
`Gdbh.PathCDecidableSmallN.strict_n`.  Composing with
`fixAStrong_atN_of_strict` gives the per-`n` FixA' slice. -/

theorem fixAStrong_at_4  : FixAStrong_at_n 4  :=
  fixAStrong_atN_of_strict (by norm_num) strict_4
theorem fixAStrong_at_5  : FixAStrong_at_n 5  :=
  fixAStrong_atN_of_strict (by norm_num) strict_5
theorem fixAStrong_at_6  : FixAStrong_at_n 6  :=
  fixAStrong_atN_of_strict (by norm_num) strict_6
theorem fixAStrong_at_7  : FixAStrong_at_n 7  :=
  fixAStrong_atN_of_strict (by norm_num) strict_7
theorem fixAStrong_at_8  : FixAStrong_at_n 8  :=
  fixAStrong_atN_of_strict (by norm_num) strict_8
theorem fixAStrong_at_9  : FixAStrong_at_n 9  :=
  fixAStrong_atN_of_strict (by norm_num) strict_9
theorem fixAStrong_at_10 : FixAStrong_at_n 10 :=
  fixAStrong_atN_of_strict (by norm_num) strict_10
theorem fixAStrong_at_11 : FixAStrong_at_n 11 :=
  fixAStrong_atN_of_strict (by norm_num) strict_11
theorem fixAStrong_at_12 : FixAStrong_at_n 12 :=
  fixAStrong_atN_of_strict (by norm_num) strict_12
theorem fixAStrong_at_13 : FixAStrong_at_n 13 :=
  fixAStrong_atN_of_strict (by norm_num) strict_13
theorem fixAStrong_at_14 : FixAStrong_at_n 14 :=
  fixAStrong_atN_of_strict (by norm_num) strict_14
theorem fixAStrong_at_15 : FixAStrong_at_n 15 :=
  fixAStrong_atN_of_strict (by norm_num) strict_15
theorem fixAStrong_at_16 : FixAStrong_at_n 16 :=
  fixAStrong_atN_of_strict (by norm_num) strict_16

/-! ## Section 4 — Aggregate over `n ∈ [4, 16]`.

Combine the per-`n` slices into a single piecewise statement on the
interval `[4, 16]`. -/

/-- **FixA' holds on `n ∈ [4, 16]` for every `C₁ ≥ 1`.**

This is the small-`n` finite-enumeration deliverable.  The asymptotic
companion (P21-T4) handles `n ≥ N_threshold` for some threshold;
combined with this file, the FixA' Prop closes on every `n ≥ 4`
provided `N_threshold ≤ 17` (so the two ranges overlap). -/
theorem fixAStrong_holds_for_small_n
    {n : ℕ} (hn4 : 4 ≤ n) (hn16 : n ≤ 16) :
    FixAStrong_at_n n := by
  interval_cases n
  · exact fixAStrong_at_4
  · exact fixAStrong_at_5
  · exact fixAStrong_at_6
  · exact fixAStrong_at_7
  · exact fixAStrong_at_8
  · exact fixAStrong_at_9
  · exact fixAStrong_at_10
  · exact fixAStrong_at_11
  · exact fixAStrong_at_12
  · exact fixAStrong_at_13
  · exact fixAStrong_at_14
  · exact fixAStrong_at_15
  · exact fixAStrong_at_16

/-! ## Section 5 — Composition with the asymptotic deliverable (T4).

Given the asymptotic FixA' bound `n ≥ N_threshold ⇒ FixAStrong_at_n n`
from P21-T4, together with the finite enumeration above, we obtain the
unconditional FixA' Prop `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`
at `C₁ = 1` for `N_threshold ≤ 17`.

The composition is exposed as a parametric headline so that P21-T4's
specific threshold and asymptotic argument can be plugged in directly. -/

/-- **Composition headline (parametric in T4).**

Given:

* `N_threshold : ℕ` with `N_threshold ≤ 17` (so the finite range
  `[4, 16]` covers the gap below the asymptotic regime), and
* `hAsymp` — the asymptotic FixA' bound at `C₁ = 1` for
  `n ≥ N_threshold`, i.e.

  ```
  ∀ n : ℕ, N_threshold ≤ n →
    (goldbachSiftedPair n √n : ℝ)
      ≤ 1 · n · pBF(√n) + reservoir' n √n ,
  ```

the existential FixA' Prop `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong`
is discharged.

The witness uses `C₁ = 1` and `N₀ = 4`. -/
theorem fixAStrong_full_of_asymptotic
    (N_threshold : ℕ) (hN : N_threshold ≤ 17)
    (hAsymp : ∀ n : ℕ, N_threshold ≤ n →
                (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                  ≤ 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                    + refinedReservoirCorrectedStrong n (Nat.sqrt n)) :
    BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong := by
  refine ⟨1, by norm_num, 4, ?_⟩
  intro n hn4
  by_cases h16 : n ≤ 16
  · -- Use finite enumeration: n ∈ [4, 16].
    have h_slice := fixAStrong_holds_for_small_n hn4 h16
    exact h_slice 1 (le_refl _)
  · -- n ≥ 17.  Hence n ≥ N_threshold since N_threshold ≤ 17.
    have hn17 : 17 ≤ n := Nat.lt_of_not_le h16
    have hn_threshold : N_threshold ≤ n := le_trans hN hn17
    exact hAsymp n hn_threshold

/-! ## Section 6 — Sanity headline: FixA' at `C₁ = 1` is consistent on
[4, 16].

Pure documentation theorem:  the finite enumeration above shows that
**no counterexample to FixA'** at `C₁ = 1` exists in `[4, 16]`.  -/

/-- **Sanity check (no false-Prop catch on `[4, 16]`).**

The finite enumeration `fixAStrong_holds_for_small_n` shows that the
FixA' inequality at `C₁ = 1` holds for **every** `n ∈ [4, 16]`.  This
rules out a small-`n` false-Prop catch on the FixA' chain. -/
theorem fixAStrong_C1_eq_one_on_small_n
    {n : ℕ} (hn4 : 4 ≤ n) (hn16 : n ≤ 16) :
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ 1 * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + refinedReservoirCorrectedStrong n (Nat.sqrt n) :=
  (fixAStrong_holds_for_small_n hn4 hn16) 1 (le_refl _)

/-! ## Section 7 — Summary marker.

P21-T5 deliverables (axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext`):

1. `FixAStrong_at_n` — the per-`n` FixA' Prop slice at `C₁ ≥ 1`.

2. `fixAStrong_atN_of_strict` — reduction:  the strict Brun-Goldbach
   bound `LHS ≤ n · pBF(√n)` together with `n ≥ 3` (for reservoir
   non-negativity) implies `FixAStrong_at_n n` at any `C₁ ≥ 1`.

3. Per-`n` closures `fixAStrong_at_4, ..., fixAStrong_at_16` —
   each obtained by composing `fixAStrong_atN_of_strict` with the
   corresponding `Gdbh.PathCDecidableSmallN.strict_n`.

4. `fixAStrong_holds_for_small_n` — aggregate piecewise statement
   covering `n ∈ [4, 16]`.

5. `fixAStrong_full_of_asymptotic` — parametric composition theorem:
   given P21-T4's asymptotic FixA' bound at `C₁ = 1` for some
   `N_threshold ≤ 17`, the FixA' existential Prop
   `BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong` is discharged
   unconditionally.

6. `fixAStrong_C1_eq_one_on_small_n` — documentation theorem:
   FixA' at `C₁ = 1` holds for every `n ∈ [4, 16]`, ruling out a
   small-`n` false-Prop catch. -/
theorem pathC_p21_t5_summary : True := trivial

end PathCFixAStrongSmallN
end Gdbh

/-! ## Section 8 — Axiom audit. -/

#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_atN_of_strict
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_4
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_5
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_6
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_7
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_8
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_9
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_10
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_11
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_12
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_13
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_14
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_15
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_at_16
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_holds_for_small_n
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_full_of_asymptotic
#print axioms Gdbh.PathCFixAStrongSmallN.fixAStrong_C1_eq_one_on_small_n
#print axioms Gdbh.PathCFixAStrongSmallN.pathC_p21_t5_summary
