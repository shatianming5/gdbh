/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T37 (Phase 19 / Path C — Decidable AssemblyPieceA at small n).
-/
import Gdbh.PathC_BrunBonferroniDecomposition
import Gdbh.PathC_AssemblyPieceAClosure
import Gdbh.PathC_PairedBrunSmallZ
import Gdbh.PathC_PairedBrunMertensLowerProof

/-!
# Path C — P19-T37: Decidable `AssemblyPieceA` at small `n`

This file is the **P19-T37 deliverable** in Phase 19 (Path C residual
exploration).

## Target

The Prop `AssemblyPieceA` (P19-T29) is the genuine Halberstam-Richert
residual of Path C.  It quantifies a real-valued inequality over all
`(k : ℕ → ℕ)` and all `n ≥ 4`:

```
goldbachSiftedPair n (Nat.sqrt n) ≤
  n · pairedBrunFactor(Nat.sqrt n)
    + n · (Nat.primeCounting (Nat.sqrt n))^(2 k n + 1)
        / (2 k n + 1)!
```

In this file we expose the **per-`n` slice**

```
AssemblyPieceA_atN (n : ℕ) : Prop
```

and check whether the limiting **strict** Brun-Goldbach

```
goldbachSiftedPair n (Nat.sqrt n) ≤ n · pairedBrunFactor(Nat.sqrt n)
```

holds for `n ∈ [4, 16]`.  This is the bound that *must* hold for
`AssemblyPieceA_atN n` to be valid at all `k`:  in the
`k n → ∞` limit, the tail term vanishes.

## Outcome (key findings — no false-Prop catch)

For `n ∈ [4, 16]` the **classical sharp paired Brun-Goldbach**

```
goldbachSiftedPair n (Nat.sqrt n) ≤ n · pairedBrunFactor (Nat.sqrt n)
```

is verified by direct finite computation.  In particular:

| `n` | `√n` | `goldbachSiftedPair n √n` | `n · pBF(√n)` |
|----:|-----:|--------------------------:|--------------:|
|   4 |    2 |                         2 |            4  |
|   5 |    2 |                         0 |            5  |
|   6 |    2 |                         3 |            6  |
|   7 |    2 |                         0 |            7  |
|   8 |    2 |                         4 |            8  |
|   9 |    3 |                         0 |            3  |
|  10 |    3 |                         1 | 10/3 ≈ 3.33  |
|  11 |    3 |                         0 | 11/3 ≈ 3.67  |
|  12 |    3 |                         4 |            4  |
|  13 |    3 |                         0 | 13/3 ≈ 4.33  |
|  14 |    3 |                         3 | 14/3 ≈ 4.67  |
|  15 |    3 |                         0 |            5  |
|  16 |    4 |                         2 | 16/3 ≈ 5.33  |

The tight case is `n = 12`, where `LHS = 4 = n · pBF(√n)`.  No
counterexample is found in `[4, 16]`;  this is **not** a false-Prop
catch.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.
-/

namespace Gdbh
namespace PathCDecidableSmallN

open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCPairedBrunSmallZ
  (pairedBrunFactor_eq_one_of_le_two)
open Gdbh.PathCPairedBrunMertensLowerProof
  (pairedBrunFactor_three_eq_one_third)
open Gdbh.PathCAssemblyPieceAClosure
  (tail_term_nonneg)

/-! ## Section 1 — `AssemblyPieceA_atN n`:  the per-`n` slice

This is the slice of `AssemblyPieceA` at a *fixed* `n`.  Closing
`AssemblyPieceA_atN n` for every `n ≥ 4` is equivalent to closing
`AssemblyPieceA`. -/

/-- The per-`n` slice of `AssemblyPieceA`. -/
def AssemblyPieceA_atN (n : ℕ) : Prop :=
  4 ≤ n →
    ∀ (k : ℕ → ℕ),
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ)

/-- **Reduction lemma.**  If the *strict* Brun-Goldbach bound

```
goldbachSiftedPair n √n ≤ n · pairedBrunFactor (√n)
```

holds, then `AssemblyPieceA_atN n` holds (for any tail). -/
theorem assemblyPieceA_atN_of_strict
    {n : ℕ}
    (h : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
            ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)) :
    AssemblyPieceA_atN n := by
  intro _ k
  have htail :
      (0 : ℝ)
        ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) :=
    tail_term_nonneg n (k n)
  linarith

/-! ## Section 2 — Helpers for the `pBF` values at small thresholds.

For `n ∈ [4, 8]` we have `Nat.sqrt n ≤ 2`, so `pBF(√n) = 1` (empty product).
For `n ∈ [9, 15]` we have `Nat.sqrt n = 3`, so `pBF(3) = 1/3`.
For `n = 16, ..., 24` we have `Nat.sqrt n = 4`, and since `4` is not
prime, `pBF(4) = pBF(3) = 1/3`. -/

/-- `pairedBrunFactor 4 = 1/3` (the prime `4` is excluded). -/
lemma pairedBrunFactor_four_eq_one_third :
    pairedBrunFactor 4 = (1 : ℝ) / 3 := by
  unfold pairedBrunFactor
  have h3prime : Nat.Prime 3 := by decide
  have h4nprime : ¬ Nat.Prime 4 := by decide
  have h_filter : (Finset.Icc 3 4).filter Nat.Prime = {3} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      interval_cases x
      · rfl
      · exact absurd hp h4nprime
    · intro hx; subst hx
      exact ⟨⟨by norm_num, by norm_num⟩, h3prime⟩
  rw [h_filter]
  simp
  norm_num

/-! ## Section 3 — `Nat.sqrt` values at small `n`.

Note:  `Nat.sqrt` is *not* kernel-reducible for non-trivial inputs
(it uses bit-pattern dependent iteration).  We therefore prove the
small-`n` values via `norm_num` (which is axiom-clean), not `decide`
(which gets stuck). -/

lemma sqrt_4 : Nat.sqrt 4 = 2 := by norm_num
lemma sqrt_5 : Nat.sqrt 5 = 2 := by norm_num
lemma sqrt_6 : Nat.sqrt 6 = 2 := by norm_num
lemma sqrt_7 : Nat.sqrt 7 = 2 := by norm_num
lemma sqrt_8 : Nat.sqrt 8 = 2 := by norm_num
lemma sqrt_9 : Nat.sqrt 9 = 3 := by norm_num
lemma sqrt_10 : Nat.sqrt 10 = 3 := by norm_num
lemma sqrt_11 : Nat.sqrt 11 = 3 := by norm_num
lemma sqrt_12 : Nat.sqrt 12 = 3 := by norm_num
lemma sqrt_13 : Nat.sqrt 13 = 3 := by norm_num
lemma sqrt_14 : Nat.sqrt 14 = 3 := by norm_num
lemma sqrt_15 : Nat.sqrt 15 = 3 := by norm_num
lemma sqrt_16 : Nat.sqrt 16 = 4 := by norm_num

/-! ## Section 4 — Exact computation of `goldbachSiftedPair n √n` at small `n`.

For each `n ∈ [4, 16]`, `goldbachSiftedPair n (Nat.sqrt n)` is a
`Finset.card` of an explicit filter and is computable by `decide`
once `Nat.sqrt n` is rewritten to its concrete value. -/

lemma goldbachSiftedPair_4 : goldbachSiftedPair 4 (Nat.sqrt 4) = 2 := by
  rw [sqrt_4]; decide
lemma goldbachSiftedPair_5 : goldbachSiftedPair 5 (Nat.sqrt 5) = 0 := by
  rw [sqrt_5]; decide
lemma goldbachSiftedPair_6 : goldbachSiftedPair 6 (Nat.sqrt 6) = 3 := by
  rw [sqrt_6]; decide
lemma goldbachSiftedPair_7 : goldbachSiftedPair 7 (Nat.sqrt 7) = 0 := by
  rw [sqrt_7]; decide
lemma goldbachSiftedPair_8 : goldbachSiftedPair 8 (Nat.sqrt 8) = 4 := by
  rw [sqrt_8]; decide
lemma goldbachSiftedPair_9 : goldbachSiftedPair 9 (Nat.sqrt 9) = 0 := by
  rw [sqrt_9]; decide
lemma goldbachSiftedPair_10 : goldbachSiftedPair 10 (Nat.sqrt 10) = 1 := by
  rw [sqrt_10]; decide
lemma goldbachSiftedPair_11 : goldbachSiftedPair 11 (Nat.sqrt 11) = 0 := by
  rw [sqrt_11]; decide
lemma goldbachSiftedPair_12 : goldbachSiftedPair 12 (Nat.sqrt 12) = 4 := by
  rw [sqrt_12]; decide
lemma goldbachSiftedPair_13 : goldbachSiftedPair 13 (Nat.sqrt 13) = 0 := by
  rw [sqrt_13]; decide
lemma goldbachSiftedPair_14 : goldbachSiftedPair 14 (Nat.sqrt 14) = 3 := by
  rw [sqrt_14]; decide
lemma goldbachSiftedPair_15 : goldbachSiftedPair 15 (Nat.sqrt 15) = 0 := by
  rw [sqrt_15]; decide
lemma goldbachSiftedPair_16 : goldbachSiftedPair 16 (Nat.sqrt 16) = 2 := by
  rw [sqrt_16]; decide

/-! ## Section 5 — Strict Brun-Goldbach (the limit bound) for each small `n`.

For each `n ∈ [4, 16]` we verify

```
(goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
```

i.e., the **classical sharp paired Brun-Goldbach**.  No counterexample
is found;  the tight case is `n = 12`. -/

/-- For `n ≤ 8` (so `√n ≤ 2`) we have `pBF(√n) = 1`, so the strict
bound reduces to `goldbachSiftedPair n √n ≤ n`, the trivial cardinal
bound. -/
private lemma strict_atN_of_le_two
    (n : ℕ) (hsqrt_le : Nat.sqrt n ≤ 2) :
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
  have hpf : pairedBrunFactor (Nat.sqrt n) = 1 :=
    pairedBrunFactor_eq_one_of_le_two hsqrt_le
  rw [hpf, mul_one]
  exact_mod_cast goldbachSiftedPair_le n (Nat.sqrt n)

lemma strict_4 :
    (goldbachSiftedPair 4 (Nat.sqrt 4) : ℝ)
      ≤ (4 : ℝ) * pairedBrunFactor (Nat.sqrt 4) :=
  strict_atN_of_le_two 4 (by rw [sqrt_4])

lemma strict_5 :
    (goldbachSiftedPair 5 (Nat.sqrt 5) : ℝ)
      ≤ (5 : ℝ) * pairedBrunFactor (Nat.sqrt 5) :=
  strict_atN_of_le_two 5 (by rw [sqrt_5])

lemma strict_6 :
    (goldbachSiftedPair 6 (Nat.sqrt 6) : ℝ)
      ≤ (6 : ℝ) * pairedBrunFactor (Nat.sqrt 6) :=
  strict_atN_of_le_two 6 (by rw [sqrt_6])

lemma strict_7 :
    (goldbachSiftedPair 7 (Nat.sqrt 7) : ℝ)
      ≤ (7 : ℝ) * pairedBrunFactor (Nat.sqrt 7) :=
  strict_atN_of_le_two 7 (by rw [sqrt_7])

lemma strict_8 :
    (goldbachSiftedPair 8 (Nat.sqrt 8) : ℝ)
      ≤ (8 : ℝ) * pairedBrunFactor (Nat.sqrt 8) :=
  strict_atN_of_le_two 8 (by rw [sqrt_8])

/-- For `√n = 3` (so `n ∈ [9, 15]`) we have `pBF(3) = 1/3`. -/
private lemma strict_atN_sqrt_three
    (n N : ℕ) (hN : goldbachSiftedPair n (Nat.sqrt n) = N)
    (hsqrt : Nat.sqrt n = 3)
    (hineq : (N : ℝ) * 3 ≤ (n : ℝ)) :
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
  rw [hN, hsqrt, pairedBrunFactor_three_eq_one_third]
  -- Goal: (N : ℝ) ≤ n * (1/3)
  -- From hineq: 3 N ≤ n.  Divide by 3.
  linarith

lemma strict_9 :
    (goldbachSiftedPair 9 (Nat.sqrt 9) : ℝ)
      ≤ (9 : ℝ) * pairedBrunFactor (Nat.sqrt 9) :=
  strict_atN_sqrt_three 9 0 goldbachSiftedPair_9 sqrt_9 (by norm_num)

lemma strict_10 :
    (goldbachSiftedPair 10 (Nat.sqrt 10) : ℝ)
      ≤ (10 : ℝ) * pairedBrunFactor (Nat.sqrt 10) :=
  strict_atN_sqrt_three 10 1 goldbachSiftedPair_10 sqrt_10 (by norm_num)

lemma strict_11 :
    (goldbachSiftedPair 11 (Nat.sqrt 11) : ℝ)
      ≤ (11 : ℝ) * pairedBrunFactor (Nat.sqrt 11) :=
  strict_atN_sqrt_three 11 0 goldbachSiftedPair_11 sqrt_11 (by norm_num)

lemma strict_12 :
    (goldbachSiftedPair 12 (Nat.sqrt 12) : ℝ)
      ≤ (12 : ℝ) * pairedBrunFactor (Nat.sqrt 12) :=
  strict_atN_sqrt_three 12 4 goldbachSiftedPair_12 sqrt_12 (by norm_num)

lemma strict_13 :
    (goldbachSiftedPair 13 (Nat.sqrt 13) : ℝ)
      ≤ (13 : ℝ) * pairedBrunFactor (Nat.sqrt 13) :=
  strict_atN_sqrt_three 13 0 goldbachSiftedPair_13 sqrt_13 (by norm_num)

lemma strict_14 :
    (goldbachSiftedPair 14 (Nat.sqrt 14) : ℝ)
      ≤ (14 : ℝ) * pairedBrunFactor (Nat.sqrt 14) :=
  strict_atN_sqrt_three 14 3 goldbachSiftedPair_14 sqrt_14 (by norm_num)

lemma strict_15 :
    (goldbachSiftedPair 15 (Nat.sqrt 15) : ℝ)
      ≤ (15 : ℝ) * pairedBrunFactor (Nat.sqrt 15) :=
  strict_atN_sqrt_three 15 0 goldbachSiftedPair_15 sqrt_15 (by norm_num)

/-- For `√n = 4` we use `pBF(4) = 1/3`. -/
lemma strict_16 :
    (goldbachSiftedPair 16 (Nat.sqrt 16) : ℝ)
      ≤ (16 : ℝ) * pairedBrunFactor (Nat.sqrt 16) := by
  rw [goldbachSiftedPair_16, sqrt_16, pairedBrunFactor_four_eq_one_third]
  -- Goal: (2 : ℝ) ≤ 16 * (1/3) = 16/3 ≈ 5.33
  norm_num

/-! ## Section 6 — Closure of `AssemblyPieceA_atN n` for `n ∈ [4, 16]`. -/

theorem assemblyPieceA_atN_4 : AssemblyPieceA_atN 4 :=
  assemblyPieceA_atN_of_strict strict_4

theorem assemblyPieceA_atN_5 : AssemblyPieceA_atN 5 :=
  assemblyPieceA_atN_of_strict strict_5

theorem assemblyPieceA_atN_6 : AssemblyPieceA_atN 6 :=
  assemblyPieceA_atN_of_strict strict_6

theorem assemblyPieceA_atN_7 : AssemblyPieceA_atN 7 :=
  assemblyPieceA_atN_of_strict strict_7

theorem assemblyPieceA_atN_8 : AssemblyPieceA_atN 8 :=
  assemblyPieceA_atN_of_strict strict_8

theorem assemblyPieceA_atN_9 : AssemblyPieceA_atN 9 :=
  assemblyPieceA_atN_of_strict strict_9

theorem assemblyPieceA_atN_10 : AssemblyPieceA_atN 10 :=
  assemblyPieceA_atN_of_strict strict_10

theorem assemblyPieceA_atN_11 : AssemblyPieceA_atN 11 :=
  assemblyPieceA_atN_of_strict strict_11

theorem assemblyPieceA_atN_12 : AssemblyPieceA_atN 12 :=
  assemblyPieceA_atN_of_strict strict_12

theorem assemblyPieceA_atN_13 : AssemblyPieceA_atN 13 :=
  assemblyPieceA_atN_of_strict strict_13

theorem assemblyPieceA_atN_14 : AssemblyPieceA_atN 14 :=
  assemblyPieceA_atN_of_strict strict_14

theorem assemblyPieceA_atN_15 : AssemblyPieceA_atN 15 :=
  assemblyPieceA_atN_of_strict strict_15

theorem assemblyPieceA_atN_16 : AssemblyPieceA_atN 16 :=
  assemblyPieceA_atN_of_strict strict_16

/-! ## Section 7 — Statement of the limit characterisation.

The reduction `assemblyPieceA_atN_of_strict` shows that the **strict
Brun-Goldbach** bound implies `AssemblyPieceA_atN n` for *any* tail
profile.  Conversely, since the tail term can be made arbitrarily small
by taking `k n` large, **the strict bound is also necessary**.

We expose this as a clean characterisation. -/

/-- **Necessity of the strict bound.**  If `AssemblyPieceA_atN n`
holds, then the *limit* (tail-free) inequality holds in the
`k n → ∞` sense:  for every `m : ℕ`, the bound with `(2 m + 1)!` in
the denominator still holds, and the tail term `π(√n)^(2m+1)/(2m+1)!`
tends to `0` as `m → ∞`.

We do not formalise the limit step here — for closing the assembly,
only the `→` direction of `assemblyPieceA_atN_of_strict` is needed.
This theorem statement remains for documentation. -/
theorem strict_is_necessary_at_n
    (n : ℕ) (_hn : 4 ≤ n)
    (_h : AssemblyPieceA_atN n) :
    ∀ m : ℕ,
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * m + 1)
                / ((2 * m + 1).factorial : ℝ) := by
  intro m
  exact _h _hn (fun _ => m)

/-! ## Section 8 — Summary export.

`assemblyPieceA_atN_holds_for_small_n` collates the per-`n` closures
into a single piecewise statement on `4 ≤ n ≤ 16`. -/

/-- **Closure of `AssemblyPieceA_atN n` on `n ∈ [4, 16]`.** -/
theorem assemblyPieceA_atN_holds_for_small_n
    {n : ℕ} (hn4 : 4 ≤ n) (hn16 : n ≤ 16) :
    AssemblyPieceA_atN n := by
  interval_cases n
  · exact assemblyPieceA_atN_4
  · exact assemblyPieceA_atN_5
  · exact assemblyPieceA_atN_6
  · exact assemblyPieceA_atN_7
  · exact assemblyPieceA_atN_8
  · exact assemblyPieceA_atN_9
  · exact assemblyPieceA_atN_10
  · exact assemblyPieceA_atN_11
  · exact assemblyPieceA_atN_12
  · exact assemblyPieceA_atN_13
  · exact assemblyPieceA_atN_14
  · exact assemblyPieceA_atN_15
  · exact assemblyPieceA_atN_16

end PathCDecidableSmallN
end Gdbh
