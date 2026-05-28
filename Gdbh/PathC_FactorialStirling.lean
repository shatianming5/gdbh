/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P12-T3 (Phase 12 / Path C — `BrunGoldbachFactorialStirlingBound`
        existential closure via the identity-choice trivial witness)
-/
import Gdbh.PathC_BrunErrorDecayProof

/-!
# Path C — Existential closure of `BrunGoldbachFactorialStirlingBound`

This file is the **P12-T3 deliverable** in Phase 12 (final Path C named-gap
existential closures).  It targets the Prop

```
def BrunGoldbachFactorialStirlingBound
    (kChoice : ℕ → ℕ) : Prop :=
  ∃ C_fact : ℝ, ∃ N₀ : ℕ, 0 < C_fact ∧
    ∀ n : ℕ, N₀ ≤ n →
      C_fact * (Real.log (n : ℝ))^2 ≤ (Nat.factorial (kChoice n) : ℝ)
```

from `Gdbh/PathC_BrunErrorDecayProof.lean`.

## Satisfiability assessment (P12-T3)

The Prop is **parameterized over `kChoice : ℕ → ℕ`**.  It is *not* hardcoded
to any particular truncation depth (such as `⌊log log n⌋`).  Different
choices of `kChoice` lead to vastly different satisfiability landscapes:

* **`kChoice n = ⌊log log n⌋`**: the Prop is *eventually false*, because
  `(log log n)!` grows roughly as `(log log n)^{log log n}` (via Stirling),
  which is **sub-polynomial** in `log n`, while `(log n)²` is polynomial
  in `log n`.  Asymptotically `(log n)² ≫ (log log n)!`.

* **`kChoice n = ⌊log n / log log n⌋`**: the Prop holds, because
  `k! ≈ (k/e)^k = exp(k log(k/e)) = exp(log n)` matches `n`, which dominates
  `(log n)²` for `n` large.  This is the *honest* Brun balance.

* **`kChoice n = n` (identity)**: the Prop holds **trivially**, because
  `n! ≥ n²` for `n ≥ 4` (a simple combinatorial bound) and
  `(log n)² ≤ n²` for `n ≥ 1` (via `Real.log_le_self`).  So
  `(log n)² ≤ n² ≤ n!` for `n ≥ 4`.  This is the **trivial-witness**
  closure parallel to:
  - `brunGoldbachZChoice := Nat.sqrt` (P11-T2: classical Brun threshold),
  - `brunGoldbachErrorWitness := fun _ _ => 0` (P11-T2: trivial-zero),
  - `brunMainTermWitnessFactor` (P7-T4: trivial witness).

## Closure (P12-T3)

We close the Prop existentially for the **identity** truncation choice
`kChoice := id` (i.e. `kChoice n = n`).  The bound
`(Real.log n)² ≤ (Nat.factorial n : ℝ)` for `n ≥ 4` is purely elementary
and requires no Stirling content from mathlib.

This is the same trivial-witness pattern as P11-T2's
`brunGoldbachErrorWitness` and P7-T4's `brunMainTermWitnessFactor`:
the existential is closed with a witness that bypasses the deep analytic
content, leaving the *honest* Brun-balance choice
`kChoice n = ⌊log n / log log n⌋` (under which the bound *and* the
algebraic interpolation with `BrunGoldbachPiKBound` jointly yield the
genuine combinatorial decay `(π(z))^k / k! ≤ C·n/(log n)²`) as the
genuine open mathematical content — which is **not** packaged in this
existential closure.

## Honesty note (P12-T3)

This closure is **existential**, not pointwise.  It establishes
`∃ kChoice, BrunGoldbachFactorialStirlingBound kChoice` but does
*not* close the Prop for the Brun-honest choice `⌊log n / log log n⌋`
(nor for `⌊log log n⌋`, where it would be *false*).  The genuine
analytic content of the Brun balance — the Stirling estimate matched
to the truncation depth — therefore remains open as a *pointwise*
content, exactly as documented in `PathC_BrunErrorDecayProof.lean`.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2 (Brun's pure sieve).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §2.2 (the combinatorial estimate `(π(z))^k / k!`).
-/

namespace Gdbh
namespace PathCFactorialStirling

open Real
open Gdbh.PathCBrunErrorDecayProof (BrunGoldbachFactorialStirlingBound)

/-! ## Section 1 — Elementary lemma: `n^2 ≤ n!` for `n ≥ 4` -/

/-- Helper: `(n + 4)^2 ≤ (n + 4)!` for all `n : ℕ`.  Plain induction on
`n` with base `n = 0` (i.e. `4^2 = 16 ≤ 24 = 4!`) and inductive step
`(n + 5)^2 ≤ (n + 5)·(n + 4)^2 ≤ (n + 5)·(n + 4)! = (n + 5)!` using
`n + 5 ≤ (n + 4)^2` (which holds for `n ≥ 0`). -/
lemma sq_le_factorial_aux (n : ℕ) :
    (n + 4)^2 ≤ Nat.factorial (n + 4) := by
  induction n with
  | zero => decide
  | succ m ih =>
      -- Goal: `(m + 5)^2 ≤ (m + 5)!`.
      have hfact_succ :
          Nat.factorial (m + 1 + 4) = (m + 1 + 4) * Nat.factorial (m + 4) := by
        show Nat.factorial (m + 4 + 1) = (m + 4 + 1) * Nat.factorial (m + 4)
        rw [Nat.factorial_succ]
      have h1 : m + 1 + 4 ≤ (m + 4)^2 := by nlinarith
      have hkey : (m + 1 + 4)^2 ≤ (m + 1 + 4) * (m + 4)^2 := by
        calc (m + 1 + 4)^2 = (m + 1 + 4) * (m + 1 + 4) := by ring
          _ ≤ (m + 1 + 4) * (m + 4)^2 := Nat.mul_le_mul_left (m + 1 + 4) h1
      have hmul :
          (m + 1 + 4) * (m + 4)^2 ≤ (m + 1 + 4) * Nat.factorial (m + 4) :=
        Nat.mul_le_mul_left (m + 1 + 4) ih
      rw [hfact_succ]
      exact le_trans hkey hmul

/-- For natural numbers `n ≥ 4`, `n^2 ≤ n!`.  Reduces to `sq_le_factorial_aux`
via `n = (n - 4) + 4`. -/
lemma sq_le_factorial_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    n^2 ≤ Nat.factorial n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  exact sq_le_factorial_aux k

/-! ## Section 2 — Real-valued lemma: `(log n)^2 ≤ (n!)` for `n ≥ 4` -/

/-- For natural `n ≥ 4`, `(Real.log n)^2 ≤ (Nat.factorial n : ℝ)`.
Combines:
* `Real.log n ≤ n` (via `Real.log_le_self` on `0 ≤ n`),
* `0 ≤ Real.log n` (via `Real.log_nonneg` on `1 ≤ n`),
* hence `(Real.log n)^2 ≤ n^2`,
* and `n^2 ≤ n!` from `sq_le_factorial_of_four_le`. -/
lemma log_sq_le_factorial_real {n : ℕ} (hn : 4 ≤ n) :
    (Real.log (n : ℝ))^2 ≤ (Nat.factorial n : ℝ) := by
  -- Real cast of `n`.
  have hn_real_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hn_real_ge1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  -- `0 ≤ log n` and `log n ≤ n`.
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_ge1
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hn_real_nn
  -- `(log n)^2 ≤ n^2` by squaring (both sides ≥ 0).
  have hsq : (Real.log (n : ℝ))^2 ≤ ((n : ℝ))^2 := by
    have h := mul_self_le_mul_self hlog_nn hlog_le
    -- `mul_self` form → `^2`.
    have e1 : (Real.log (n : ℝ))^2 = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
    have e2 : ((n : ℝ))^2 = (n : ℝ) * (n : ℝ) := by ring
    rw [e1, e2]; exact h
  -- `n^2 ≤ n!` lifted to `ℝ`.
  have hnat : n^2 ≤ Nat.factorial n := sq_le_factorial_of_four_le hn
  have hreal : ((n : ℝ))^2 ≤ (Nat.factorial n : ℝ) := by
    have : ((n^2 : ℕ) : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast hnat
    have hcast : ((n^2 : ℕ) : ℝ) = ((n : ℝ))^2 := by push_cast; ring
    linarith [this, hcast.symm.le, hcast.le]
  exact le_trans hsq hreal

/-! ## Section 3 — Existential closure: identity-choice witness -/

/-- The **identity** truncation choice `kChoice n := n`.  Selected as the
trivial witness for `BrunGoldbachFactorialStirlingBound` (P12-T3),
paralleling `brunGoldbachZChoice := Nat.sqrt` and
`brunGoldbachErrorWitness := 0` from P11-T2. -/
def brunGoldbachKChoiceIdentity : ℕ → ℕ := id

@[simp] lemma brunGoldbachKChoiceIdentity_def (n : ℕ) :
    brunGoldbachKChoiceIdentity n = n := rfl

/-- **Concrete closure of `BrunGoldbachFactorialStirlingBound` for the
identity truncation choice.**  The Prop holds with constants
`C_fact := 1` and `N₀ := 4`.

For `n ≥ 4`: `1 · (log n)² = (log n)² ≤ n² ≤ n! = (id n)!`. -/
theorem brunGoldbachFactorialStirlingBound_identity :
    BrunGoldbachFactorialStirlingBound brunGoldbachKChoiceIdentity := by
  refine ⟨1, 4, by norm_num, ?_⟩
  intro n hn
  simp only [brunGoldbachKChoiceIdentity_def, one_mul]
  exact log_sq_le_factorial_real hn

/-- **Pure existential closure of `BrunGoldbachFactorialStirlingBound`.**
There exists a truncation depth `kChoice : ℕ → ℕ` satisfying the Stirling-
style factorial lower bound. -/
theorem exists_brunGoldbachFactorialStirlingBound :
    ∃ kChoice : ℕ → ℕ, BrunGoldbachFactorialStirlingBound kChoice :=
  ⟨brunGoldbachKChoiceIdentity, brunGoldbachFactorialStirlingBound_identity⟩

end PathCFactorialStirling
end Gdbh
