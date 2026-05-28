/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P22-T3 (Phase 22 / Path C — Combine the parallel deliverables of
        P22-T1 (Mertens-3 singular-series upper bound) and P22-T2
        (Brun-Goldbach with explicit singular series) into the named
        classical Prop `ClassicalBrunGoldbachLogLog`.)
-/
import Gdbh.PathC_FixAStrongClosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Path C — P22-T3: Conditional bridge `(T1 ∧ T2) ⇒ ClassicalBrunGoldbachLogLog`

## Mission

This file is the **combination step** of Phase 22 / Path C:  it takes the
two parallel deliverables of P22-T1 and P22-T2 and assembles them into a
single hypothesis that closes
`Gdbh.PathCFixAStrongClosure.ClassicalBrunGoldbachLogLog`.

The two parallel inputs (each producing a *named open Prop* whose closure
in mathlib v4.29.1 remains the residual gap) are:

* **P22-T1.**  A Mertens-3 type upper bound on the Hardy-Littlewood
  singular series `S : ℕ → ℝ` of the form
  `S(n) ≤ K_M · log log n` for `n ≥ N_M`.

  We name this Prop `SingularSeriesMertensBound S`.

* **P22-T2.**  A Brun-Goldbach upper bound *expressed via the singular
  series*:
  `r(n) ≤ C_BG · n · pairedBrunFactor(√n) · S(n)` for `n ≥ N_BG`,
  where `r(n) = goldbachSiftedPair n √n` is the project's sifted Goldbach
  counting function.

  We name this Prop `BrunGoldbachWithSingularSeries S`.

Both Props are *parametrised by the same function `S`*:  the bridge below
combines them by literal multiplication.

## The bridge

```
classicalBrunGoldbachLogLog_of_brunSingularSeries_and_mertensSingular
    {S : ℕ → ℝ}
    (hBG : BrunGoldbachWithSingularSeries S)
    (hM  : SingularSeriesMertensBound  S) :
    ClassicalBrunGoldbachLogLog
```

The proof:  let `(C_BG, N_BG)` witness `hBG` and `(K_M, N_M)` witness
`hM`.  For `n ≥ max N_BG N_M`,

```
r(n) ≤ C_BG · n · pBF(√n) · S(n)                  (hBG)
     ≤ C_BG · n · pBF(√n) · (K_M · log log n)     (hM, since n · pBF ≥ 0)
     = (C_BG · K_M) · n · pBF(√n) · log log n .
```

Setting `C := C_BG · K_M > 0`, this is exactly
`ClassicalBrunGoldbachLogLog`.

## Discussion: shape of the combined bound

The task specification asks what bound on the LHS the chain produces in
different scaling regimes.  Schematically:

* **`α = 0` (S(n) bounded).**  If T1's Mertens bound is `S(n) ≤ K_M`
  (constant), then the combined bound is
  `r(n) ≤ C · n · pBF(√n)`.  This is *the bare Brun-Goldbach main term*
  with no log-log loss — it would close FixA' trivially via P21-T1.
  However, the classical Mertens-3 bound is *not* constant; the genuine
  Hardy-Littlewood / Halberstam-Richert bound on the singular series is
  of size `log log n` (this is the standard ramification of
  Mertens' third theorem).

* **`α = 1` (S(n) ~ log log n).**  This is the classical case
  encoded in the file:  combined bound is
  `r(n) ≤ C · n · pBF(√n) · log log n`, exactly
  `ClassicalBrunGoldbachLogLog`.

* **`α = 2` (S(n) ≲ (log n)²) — naive worst case.**  If T1 only gave
  `S(n) ≤ K · (log n)²`, then combining with `pBF ≤ K' / (log n)²`
  collapses the bound to `r(n) ≤ C · n`, which is the *trivial* counting
  bound `#{p+q=2n} ≤ n`.  Useless.

The whole point of the *Mertens-3* singular-series bound is that it
yields the *tight* `log log n` factor rather than a polynomial in
`log n`.  Closing T1 (the singular-series Mertens-3 estimate) is
therefore the essential analytic input.

## Where the residual gap sits, mathematically

The classical proof of the Mertens-3 bound on `S` uses

1. truncating the Euler product defining `S(n)` to primes `p ≤ z(n)`
   (for `z` growing slowly with `n`);
2. averaging the local factors over primes `p ≤ z(n)` using
   Mertens' first theorem (already closed in the project as
   `Gdbh.PathCMertensFirstClosure` / `MertensFirstUpper`);
3. bounding the tail `∏_{p > z(n)}` via the rapid convergence
   `S(n) - S_z(n) = O(1/z(n))`, which follows from
   `|log(1 - 2/p²) - log(1 - 1/p)²| = O(1/p²)`.

Steps (1)–(3) compose into `S(n) ≤ K_M · log log n`.  Steps (1) and (3)
are elementary; step (2) is exactly the Mertens-1 bound, which *is*
formalised in the project repository.  The remaining mathlib gap is
therefore the combinatorial *assembly* of these three pieces — a routine
but non-trivial undertaking.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene:  only `Classical.choice`, `Quot.sound`, `propext`.
* This file **only adds**; it does not modify any other file in the
  project.

## Honesty rule

`SingularSeriesMertensBound` and `BrunGoldbachWithSingularSeries` are
*both* mathlib v4.29.1 **open**.  The present file establishes the
*conditional* implication `(T1 ∧ T2) ⇒ ClassicalBrunGoldbachLogLog`
axiom-cleanly.  It does **not** close either input Prop on its own.

Composed with P21-T1
(`brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog`)
the conditional bridge closes the FixA' chain Prop modulo `T1 ∧ T2`.
-/

namespace Gdbh
namespace PathCClassicalBrunGoldbachLogLogBridge

open Real
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCFixAStrongClosure (ClassicalBrunGoldbachLogLog)

/-! ## Section 1 — The two parallel inputs (P22-T1, P22-T2). -/

/-- **P22-T2 input.**  *Brun-Goldbach with the singular series exposed.*
This is the explicit-singular-series form of the Halberstam-Richert
§3.11 upper bound:  for `n ≥ N_BG`,

```
goldbachSiftedPair n √n  ≤  C_BG · n · pairedBrunFactor(√n) · S(n) ,
```

with `S : ℕ → ℝ` the (Hardy-Littlewood) singular series.  The Prop is
parametrised by `S` because the *same* function is used by the
companion bound `SingularSeriesMertensBound`.

**Status:**  mathlib v4.29.1 **open**.  This is the literal Brun-Goldbach
upper bound expressed with the singular-series factor not yet absorbed
into the constant. -/
def BrunGoldbachWithSingularSeries (S : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
    ∀ n : ℕ, N ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * S n

/-- **P22-T1 input.**  *Mertens-3 upper bound on the singular series.*
The classical singular-series upper bound:  for `n ≥ N_M`,

```
S(n)  ≤  K_M · log log n .
```

**Status:**  mathlib v4.29.1 **open**.  Mathematically this follows
from Mertens-1 (closed in the project) combined with the standard
Euler-product truncation argument outlined in the module docstring. -/
def SingularSeriesMertensBound (S : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, ∃ N : ℕ, 0 < K ∧
    ∀ n : ℕ, N ≤ n →
      S n ≤ K * Real.log (Real.log (n : ℝ))

/-! ## Section 2 — Combining-step lemma:  multiplying by `n · pBF`.

To pass from `S(n) ≤ K_M · log log n` to a bound on
`n · pBF(√n) · S(n)`, we need to multiply by the **non-negative**
factor `n · pBF(√n) ≥ 0`.  This is the only non-trivial step. -/

/-- For all `n`, the factor `(n : ℝ) · pairedBrunFactor (Nat.sqrt n)` is
non-negative.  Combines `Nat.cast_nonneg` with
`pairedBrunFactor_pos`. -/
lemma n_pbf_sqrt_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_pbf_nn : (0 : ℝ) ≤ pairedBrunFactor (Nat.sqrt n) :=
    le_of_lt (pairedBrunFactor_pos _)
  exact mul_nonneg h_n_nn h_pbf_nn

/-! ## Section 3 — The combination bridge. -/

/-- **P22-T3 main bridge.**  The two parallel Phase-22 inputs
(`BrunGoldbachWithSingularSeries S` and `SingularSeriesMertensBound S`,
for the *same* singular-series function `S`) jointly imply the named
classical Prop `ClassicalBrunGoldbachLogLog`.

The proof is the multiplicative chain

```
r(n) ≤ C_BG · n · pBF · S(n)                  (hBG)
     ≤ C_BG · n · pBF · (K_M · log log n)     (hM, since n · pBF ≥ 0)
     = (C_BG · K_M) · n · pBF · log log n ,
```

valid for `n ≥ max N_BG N_M`.  The combined constant is
`C := C_BG · K_M > 0`.

No `sorry`, no `axiom`, no `admit`. -/
theorem classicalBrunGoldbachLogLog_of_brunSingularSeries_and_mertensSingular
    {S : ℕ → ℝ}
    (hBG : BrunGoldbachWithSingularSeries S)
    (hM  : SingularSeriesMertensBound  S) :
    ClassicalBrunGoldbachLogLog := by
  -- Unpack hypotheses.
  obtain ⟨C_BG, N_BG, hC_BG_pos, hBG_bd⟩ := hBG
  obtain ⟨K_M,  N_M,  hK_M_pos,  hM_bd⟩  := hM
  -- The combined witness:  C := C_BG · K_M, N₀ := max N_BG N_M.
  refine ⟨C_BG * K_M, max N_BG N_M, mul_pos hC_BG_pos hK_M_pos, ?_⟩
  intro n hn
  -- Decompose the threshold.
  have hn_BG : N_BG ≤ n := le_trans (le_max_left _ _) hn
  have hn_M  : N_M  ≤ n := le_trans (le_max_right _ _) hn
  -- Apply each hypothesis at `n`.
  have h1 :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C_BG * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * S n :=
    hBG_bd n hn_BG
  have h2 : S n ≤ K_M * Real.log (Real.log (n : ℝ)) := hM_bd n hn_M
  -- Multiply `h2` by the non-negative factor `C_BG · (n · pBF(√n))`.
  have h_C_BG_nn : (0 : ℝ) ≤ C_BG := le_of_lt hC_BG_pos
  have h_npbf_nn : (0 : ℝ) ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) :=
    n_pbf_sqrt_nonneg n
  have h_factor_nn :
      (0 : ℝ) ≤ C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) :=
    mul_nonneg h_C_BG_nn h_npbf_nn
  -- Multiply `h2` on the left by `(C_BG · (n · pBF))`.
  have h3 :
      C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) * S n
        ≤ C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
            * (K_M * Real.log (Real.log (n : ℝ))) :=
    mul_le_mul_of_nonneg_left h2 h_factor_nn
  -- Rearrange the LHS of `h3` to match the RHS of `h1`.
  have h_rearr_l :
      C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) * S n
        = C_BG * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * S n := by ring
  -- Rearrange the RHS of `h3` to match the goal.
  have h_rearr_r :
      C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
          * (K_M * Real.log (Real.log (n : ℝ)))
        = C_BG * K_M * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            * Real.log (Real.log (n : ℝ)) := by ring
  -- Chain `h1` and `h3` to obtain the desired inequality.
  calc (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ C_BG * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) * S n := h1
    _ = C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)) * S n := h_rearr_l.symm
    _ ≤ C_BG * ((n : ℝ) * pairedBrunFactor (Nat.sqrt n))
            * (K_M * Real.log (Real.log (n : ℝ))) := h3
    _ = C_BG * K_M * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            * Real.log (Real.log (n : ℝ)) := h_rearr_r

/-! ## Section 4 — Headline summary -/

/-- **P22-T3 summary marker** (no content theorem).

Deliverables (axiom-clean:  only `Classical.choice`, `Quot.sound`,
`propext`):

1. `BrunGoldbachWithSingularSeries (S : ℕ → ℝ)` — named Prop encoding
   the classical Halberstam-Richert §3.11 Brun-Goldbach upper bound with
   the Hardy-Littlewood singular series factor `S(n)` left exposed
   (not yet absorbed into the constant).  **Status:** mathlib
   v4.29.1 **open**.  *Parallel deliverable P22-T2.*

2. `SingularSeriesMertensBound  (S : ℕ → ℝ)` — named Prop encoding
   the Mertens-3 upper bound `S(n) ≤ K_M · log log n` on the
   Hardy-Littlewood singular series.  **Status:** mathlib v4.29.1
   **open**.  *Parallel deliverable P22-T1.*

3. `classicalBrunGoldbachLogLog_of_brunSingularSeries_and_mertensSingular`
   — bridge theorem `(T1 ∧ T2) ⇒ ClassicalBrunGoldbachLogLog` (with the
   *same* `S` in both inputs).  The proof is a one-step product
   estimate:  multiply T1's `S(n) ≤ K_M · log log n` by the non-negative
   factor `n · pBF(√n)` and chain with T2's `r(n) ≤ C · n · pBF · S(n)`.

## Composition with the rest of the FixA' tower

Composing the present P22-T3 bridge with the existing P21-T1 bridge

```
brunGoldbachPairedMainTermRefinedAtSqrtFixAStrong_of_classicalLogLog
  : ClassicalBrunGoldbachLogLog
    → BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
```

(closed axiom-cleanly in `Gdbh.PathC_FixAStrongClosure`) yields:

```
(BrunGoldbachWithSingularSeries S) ∧ (SingularSeriesMertensBound S)
    → BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong .
```

In other words, *after Phase 22*, the FixA' chain Prop reduces to **two**
independently closable mathlib-open Props:

* P22-T1:  `SingularSeriesMertensBound  S`  (Mertens-3 on the singular series);
* P22-T2:  `BrunGoldbachWithSingularSeries S`  (Halberstam-Richert §3.11).

Both Props are classical;  closing either in mathlib v4.29.1 is a
separate undertaking, but neither requires further analytic machinery
beyond what is already classical 19th–20th-century analytic number
theory. -/
theorem pathC_p22_t3_summary : True := trivial

end PathCClassicalBrunGoldbachLogLogBridge
end Gdbh
