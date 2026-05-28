/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P16-T2 (Phase 16 / Path C — `LogFactorialStirlingBound` closure)
-/
import Gdbh.PathC_VonMangoldtAsymptotic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Path C — Closure of `LogFactorialStirlingBound` (P16-T2)

This file is the **P16-T2 deliverable** in Phase 16.  Its target is the
named open `Prop` `Gdbh.PathCVonMangoldtAsymptotic.LogFactorialStirlingBound`:

```
∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  |log (N!) − N · log N + N|  ≤  C · (log N + 1) .
```

## Strategy — symmetric assembly via mathlib's `Stirling` API

Mathlib v4.29.1 provides:

* `Stirling.log_stirlingSeq_formula` :
  `log (stirlingSeq n) = log n! − (1/2) log (2n) − n · log (n / e)`.

Rearranging (using `log (n/e) = log n − 1` for `n ≥ 1`):

```
log n! − n · log n + n  =  log (stirlingSeq n) + (1/2) log (2n)
                        =  log (stirlingSeq n) + (1/2) log 2 + (1/2) log n .
```

For `n = m + 1 ≥ 1`, mathlib's effective bounds are:

* `Stirling.log_stirlingSeq_bounded_by_constant` :
  `1 − 12⁻¹ − log 2 / 2 ≤ log (stirlingSeq (m+1))` (lower).
* `Stirling.stirlingSeq'_antitone` ⟹ `stirlingSeq (m+1) ≤ stirlingSeq 1 = exp 1 / √2`,
  hence `log (stirlingSeq (m+1)) ≤ 1 − log 2 / 2` (upper).

Let `X(n) := log (stirlingSeq n) + (1/2) log 2`.  Then for `n ≥ 1`:

```
1 − 1/12 = 11/12  ≤  X(n)  ≤  1 .
```

So `|log n! − n · log n + n − (1/2) log n|  =  |X(n)|  ≤  1` for `n ≥ 1`.

Hence

```
|log n! − n · log n + n|  ≤  (1/2) · log n + 1
                          ≤  1 · (log n + 1)        (since log n ≥ 0)
```

Witnesses: `C := 1`, `N₀ := 1`.

## Axiom budget

The closure is axiom-clean: only `Classical.choice, Quot.sound, propext`.

## References

* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.
* H. Robbins, *A Remark on Stirling's Formula*, Amer. Math. Monthly 62 (1955).
* mathlib `Mathlib.Analysis.SpecialFunctions.Stirling`.
-/

namespace Gdbh
namespace PathCLogFactorialStirling

open Real
open Gdbh.PathCVonMangoldtAsymptotic (LogFactorialStirlingBound)

/-! ## Section 1 — Helper lemmas -/

/-- Auxiliary: `log (stirlingSeq 1) = 1 - log 2 / 2`. -/
lemma log_stirlingSeq_one_eq : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
  rw [Stirling.stirlingSeq_one]
  rw [Real.log_div (Real.exp_pos 1).ne' (by positivity)]
  rw [Real.log_exp, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Upper bound on `log (stirlingSeq (m + 1))`: it is at most `1 - log 2 / 2`.

Proof: `stirlingSeq ∘ succ` is antitone, so `stirlingSeq (m + 1) ≤ stirlingSeq 1`;
then take logs (note `stirlingSeq (m + 1) > 0` and `stirlingSeq 1 > 0`). -/
lemma log_stirlingSeq_succ_le (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) ≤ 1 - Real.log 2 / 2 := by
  -- `stirlingSeq ∘ succ` is antitone — `(stirlingSeq ∘ succ) m ≤ (stirlingSeq ∘ succ) 0`.
  have hanti : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 := by
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    -- `(stirlingSeq ∘ succ) 0 = stirlingSeq 1`, `(stirlingSeq ∘ succ) m = stirlingSeq (m + 1)`.
    simpa [Function.comp] using h
  have hpos : 0 < Stirling.stirlingSeq (m + 1) := Stirling.stirlingSeq'_pos m
  have hpos1 : 0 < Stirling.stirlingSeq 1 := by
    rw [Stirling.stirlingSeq_one]; positivity
  have hlog_mono := Real.log_le_log hpos hanti
  rw [log_stirlingSeq_one_eq] at hlog_mono
  exact hlog_mono

/-- Lower bound on `log (stirlingSeq (m + 1))` (mathlib's `log_stirlingSeq_bounded_by_constant`),
re-stated for convenience. -/
lemma log_stirlingSeq_succ_ge (m : ℕ) :
    1 - 12⁻¹ - Real.log 2 / 2 ≤ Real.log (Stirling.stirlingSeq (m + 1)) :=
  Stirling.log_stirlingSeq_bounded_by_constant m

/-- Two-sided bound on `log (stirlingSeq (m + 1))`. -/
lemma log_stirlingSeq_succ_abs_bound (m : ℕ) :
    |Real.log (Stirling.stirlingSeq (m + 1)) - (1 - Real.log 2 / 2)| ≤ 12⁻¹ := by
  have hlo := log_stirlingSeq_succ_ge m
  have hhi := log_stirlingSeq_succ_le m
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## Section 2 — Identity: `log n! − n log n + n = log(stirlingSeq n) + (1/2) log(2n)` -/

/-- For `n ≥ 1` (`m + 1`), the Stirling formula identity in the form

```
log n! − n · log n + n  =  log (stirlingSeq n) + (1/2) log (2n) .
```

This is a direct rearrangement of `Stirling.log_stirlingSeq_formula`. -/
lemma log_factorial_decomp (m : ℕ) :
    Real.log ((Nat.factorial (m + 1) : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)
        + ((m + 1 : ℕ) : ℝ)
      = Real.log (Stirling.stirlingSeq (m + 1))
          + (1 / 2) * Real.log (2 * ((m + 1 : ℕ) : ℝ)) := by
  -- Begin with mathlib's `log_stirlingSeq_formula`.
  have hform := Stirling.log_stirlingSeq_formula (m + 1)
  -- `log_stirlingSeq_formula` :
  --   log (stirlingSeq n) = log n ! − (1/2) log (2 n) − n · log (n / exp 1).
  -- For n = m + 1, n / exp 1 = (m + 1) / exp 1, and log ((m+1)/exp 1) = log (m+1) − 1.
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hdiv_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / Real.exp 1 := by positivity
  have hlogdiv : Real.log (((m + 1 : ℕ) : ℝ) / Real.exp 1)
      = Real.log ((m + 1 : ℕ) : ℝ) - 1 := by
    rw [Real.log_div hpos.ne' hexp_pos.ne', Real.log_exp]
  -- Cast (m + 1 : ℕ) → ℕ via factorial.
  have hcast : (((m + 1 : ℕ) : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by norm_cast
  -- The formula reads:
  --   log (stirlingSeq (m + 1)) = log ((m+1)!) − (1/2) log (2(m+1)) − (m+1) · log ((m+1)/exp 1)
  -- We rewrite `(↑(m + 1 : ℕ)) = (m + 1 : ℝ)` for clarity.  Then rearrange.
  -- Mathlib's formula uses `Real.log n !` which is the cast.
  -- We can manipulate hform directly.
  rw [hlogdiv] at hform
  -- Now: log (stirlingSeq (m+1)) = log ((m+1)!) - (1/2) log (2(m+1)) - (m+1) * (log (m+1) - 1).
  -- We want: log ((m+1)!) - (m+1) * log (m+1) + (m+1)
  --        = log (stirlingSeq (m+1)) + (1/2) log (2(m+1)).
  -- This is pure linear algebra from hform.
  linarith [hform]

/-! ## Section 3 — The main bound -/

/-- For `n = m + 1 ≥ 1`, the symmetric Stirling bound
`|log n! − n log n + n| ≤ 1 · (log n + 1)`.

Combines `log_factorial_decomp` with the two-sided bound on `log (stirlingSeq n)`. -/
lemma log_factorial_stirling_bound_aux (m : ℕ) :
    |Real.log ((Nat.factorial (m + 1) : ℕ) : ℝ)
        - ((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)
        + ((m + 1 : ℕ) : ℝ)|
      ≤ 1 * (Real.log ((m + 1 : ℕ) : ℝ) + 1) := by
  -- Let N := (m + 1 : ℝ), Y := log N.
  have hN_pos_pre : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hN_ge_one_pre : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    exact_mod_cast this
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hN_def
  have hN_pos : (0 : ℝ) < N := hN_pos_pre
  have hN_ge_one : (1 : ℝ) ≤ N := hN_ge_one_pre
  have hlogN_nn : 0 ≤ Real.log N := Real.log_nonneg hN_ge_one
  -- Decomposition: log N! - N log N + N = log(stirlingSeq N) + (1/2) log(2N).
  have hdecomp := log_factorial_decomp m
  -- (1/2) log (2N) = (1/2) (log 2 + log N) = (1/2) log 2 + (1/2) log N.
  have hlog2N : Real.log (2 * N) = Real.log 2 + Real.log N := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN_pos.ne']
  -- Bound: |log(stirlingSeq N) - (1 - log 2 / 2)| ≤ 1/12.
  have hbnd := log_stirlingSeq_succ_abs_bound m
  -- Therefore log(stirlingSeq N) + (1/2) log 2 lies in [11/12, 1].
  -- That is, |log(stirlingSeq N) + (1/2) log 2 - 1| ≤ 1/12 ≤ 1.
  -- Stronger: ≤ 1 (we will just bound this by 1).
  -- And we have log(stirlingSeq N) + (1/2) log(2N) = log(stirlingSeq N) + (1/2) log 2 + (1/2) log N.
  -- So the LHS = (log(stirlingSeq N) + (1/2) log 2) + (1/2) log N.
  -- |LHS| ≤ |log(stirlingSeq N) + (1/2) log 2| + (1/2) log N.
  -- And |log(stirlingSeq N) + (1/2) log 2| ≤ |1| + |log(stirlingSeq N) + (1/2) log 2 - 1| ... too loose.
  -- Direct: log(stirlingSeq N) + (1/2) log 2 ∈ [11/12, 1], so |·| ≤ 1.
  have hlo : 11/12 ≤ Real.log (Stirling.stirlingSeq (m + 1)) + Real.log 2 / 2 := by
    have := log_stirlingSeq_succ_ge m; linarith
  have hhi : Real.log (Stirling.stirlingSeq (m + 1)) + Real.log 2 / 2 ≤ 1 := by
    have := log_stirlingSeq_succ_le m; linarith
  have hmid_nn : 0 ≤ Real.log (Stirling.stirlingSeq (m + 1)) + Real.log 2 / 2 := by linarith
  have hmid_le_one : Real.log (Stirling.stirlingSeq (m + 1)) + Real.log 2 / 2 ≤ 1 := hhi
  -- Now substitute and finish.
  rw [hdecomp, hlog2N]
  -- Goal: |log(stirlingSeq (m+1)) + (1/2) (log 2 + log N)| ≤ 1 * (log N + 1)
  --     = |(log(stirlingSeq (m+1)) + log 2 / 2) + (1/2) log N| ≤ log N + 1.
  -- Rewrite (1/2) (log 2 + log N) = log 2 / 2 + log N / 2 algebraically.
  -- The sum: A + B where A := log(stirlingSeq) + log 2 / 2 ∈ [0, 1] and B := (1/2) log N ≥ 0.
  have habs_bound :
      |Real.log (Stirling.stirlingSeq (m + 1)) + 1 / 2 * (Real.log 2 + Real.log N)|
        ≤ Real.log N + 1 := by
    -- = |(log(stirlingSeq (m+1)) + log 2 / 2) + log N / 2|
    set A := Real.log (Stirling.stirlingSeq (m + 1)) + Real.log 2 / 2 with hA_def
    have hA_eq : Real.log (Stirling.stirlingSeq (m + 1)) + 1 / 2 * (Real.log 2 + Real.log N)
        = A + Real.log N / 2 := by rw [hA_def]; ring
    rw [hA_eq]
    have hA_nn : 0 ≤ A := hmid_nn
    have hA_le_one : A ≤ 1 := hmid_le_one
    have hLogN_half_nn : 0 ≤ Real.log N / 2 := by linarith
    -- A + log N / 2 ≥ 0.
    have hsum_nn : 0 ≤ A + Real.log N / 2 := by linarith
    rw [abs_of_nonneg hsum_nn]
    -- A + log N / 2 ≤ 1 + log N ≤ log N + 1.
    linarith
  -- Finish.
  linarith [habs_bound]

/-! ## Section 4 — Closure of `LogFactorialStirlingBound` -/

/-- **Closure of `LogFactorialStirlingBound`** (P16-T2).

Witnesses: `C := 1`, `N₀ := 1`.

For `N ≥ 1`, write `N = m + 1`; then `log_factorial_stirling_bound_aux m`
delivers the bound. -/
theorem logFactorialStirlingBound_holds : LogFactorialStirlingBound := by
  refine ⟨1, 1, ?_⟩
  intro N hN
  -- N ≥ 1, so N = m + 1 for some m.
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact log_factorial_stirling_bound_aux m

end PathCLogFactorialStirling
end Gdbh
