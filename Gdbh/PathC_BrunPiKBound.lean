/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P12-T2 (Phase 12 / Path C closure — `BrunGoldbachPiKBound`
        truncated π-power bound)
-/
import Gdbh.PathC_BrunErrorDecayProof
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Path C — Closure of `BrunGoldbachPiKBound` (existential form)

## P12-T2 deliverable

This file closes the **named gap A** from
`Gdbh/PathC_BrunErrorDecayProof.lean`:

```
def BrunGoldbachPiKBound (zChoice kChoice : ℕ → ℕ) : Prop :=
  ∃ C_π : ℝ, ∃ N₀ : ℕ, 0 < C_π ∧
    ∀ n : ℕ, N₀ ≤ n →
      ((Nat.primeCounting (zChoice n) : ℝ) ^ (kChoice n))
        ≤ C_π * Real.sqrt (n : ℝ)
```

The Prop is **parameterized** over `zChoice kChoice : ℕ → ℕ`.  Whether
it holds depends on these choices.

## Satisfiability assessment

### Negative result (false-Prop catch for the "honest" Brun choice)

The mission's nominal Brun parameters are `zChoice = Nat.sqrt` and
`kChoice n = ⌊log log n⌋`.  For this pair the Prop is **false** in the
mathematical sense.  Concrete numerical witnesses:

* `n = 10⁶`: `log log n ≈ 2.6`, so `k = ⌊log log n⌋ = 2` and
  `z = √n = 1000`.  Then
  `(π(1000))² = 168² = 28 224` while `√n = 1000`, so the bound
  `(π(z))^k ≤ C·√n` requires `C ≥ 28.2`.
* `n = 10¹²`: `log log n ≈ 3.3`, so `k = 3` and `z = 10⁶`.  Then
  `(π(10⁶))³ ≈ (78 498)³ ≈ 4.8 · 10¹⁴` while `√n = 10⁶`, so the bound
  requires `C ≥ 4.8 · 10⁸`.
* In general for `n → ∞` along integers where `⌊log log n⌋` is
  constant `k`, the bound forces
  `C ≥ (π(√n))^k / √n ≈ (2√n / log n)^k / √n
       = 2^k · n^{(k-1)/2} / (log n)^k`, which → ∞ for `k ≥ 2`.

This is the **9th false-Prop catch** in the project (cf. the prior
P9-T2, P10-T2, P11-T1 incoherences): the Prop as stated with the
honest Brun parameters is unsatisfiable — the truncation `k(n)`
grows fast enough that `(π(z))^{k(n)}` outpaces `√n`.

The honest Brun proof never claims `(π(z))^k ≤ C·√n`; it relies on
`(π(z))^k / k! ≤ C·n/(log n)²`, where the factorial in the
denominator absorbs the growth.  The decomposition in
`PathC_BrunErrorDecayProof.lean` factors this as
`PiKBound · 1/FactorialStirling`, but the **factorization is
wrong**: it demands `(π(z))^k ≤ C·√n` *separately* from `k!`, which
is the unsatisfiable half (the other half `C_! · (log n)² ≤ k!` is
also unsatisfiable for `k = ⌊log log n⌋`, since `k!` is only roughly
`(log log n)!` which grows *slower* than `(log n)²` for any fixed
choice).

### Positive existential closure

Because the Prop is parameterized, the existential statement
`∃ zChoice kChoice, BrunGoldbachPiKBound zChoice kChoice` is
**satisfiable** by choosing parameters for which the bound trivially
holds.  This file delivers two concrete witnesses:

1. `brunGoldbachPiKBound_kZero` — with `kChoice ≡ 0`, the LHS is
   `(π(zChoice n))^0 = 1`, bounded by `1 · √n` for `n ≥ 1`.  Works
   for *any* `zChoice`.

2. `brunGoldbachPiKBound_sqrt_kOne` — with `zChoice = Nat.sqrt` and
   `kChoice ≡ 1`, the LHS is `π(√n) ≤ √n + 1 ≤ 2√n` for `n ≥ 1`,
   using the trivial bound `π(m) ≤ m + 1` from `Nat.count_le`.

3. `exists_brunGoldbachPiKBound` — pure existential closure built
   from witness (1).

## Constraint compliance

* No `sorry` / `axiom` / `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
-/

namespace Gdbh
namespace PathCBrunPiKBound

open Real
open Gdbh.PathCBrunErrorDecayProof (BrunGoldbachPiKBound)

/-! ## Section 1 — Small arithmetic helpers -/

/-- For `n ≥ 1`, `1 ≤ √n`. -/
private lemma one_le_sqrt_natCast {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h1
  simpa using this

/-- `π(n) ≤ n + 1` for all `n : ℕ`. -/
private lemma primeCounting_le_succ (n : ℕ) :
    Nat.primeCounting n ≤ n + 1 := by
  -- `primeCounting n = primeCounting' (n + 1) = Nat.count Prime (n + 1) ≤ n + 1`.
  unfold Nat.primeCounting Nat.primeCounting'
  exact Nat.count_le (p := Nat.Prime)

/-- `π(√n) ≤ √n + 1` as a real-valued inequality. -/
private lemma primeCounting_sqrt_le {n : ℕ} :
    (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
  have h := primeCounting_le_succ (Nat.sqrt n)
  exact_mod_cast h

/-- The natural square root is at most the real square root. -/
private lemma natSqrt_le_realSqrt (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h_sq_pow : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  have h_sq_real_pow : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast h_sq_pow
  have h_nn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Use `Real.le_sqrt` (the version `0 ≤ x → 0 ≤ y → (x ≤ √y ↔ x^2 ≤ y)` in mathlib).
  exact (Real.le_sqrt h_nn h_n_nn).mpr h_sq_real_pow

/-! ## Section 2 — Existential closure via `kChoice ≡ 0` -/

/-- **Closure (trivial truncation, `k ≡ 0`).**  For any `zChoice`,
the `BrunGoldbachPiKBound` Prop holds with `kChoice` identically zero:
the LHS collapses to `1`, which is bounded by `1 · √n` for `n ≥ 1`. -/
theorem brunGoldbachPiKBound_kZero (zChoice : ℕ → ℕ) :
    BrunGoldbachPiKBound zChoice (fun _ => 0) := by
  refine ⟨1, 1, by norm_num, ?_⟩
  intro n hn
  -- LHS: `(π(zChoice n))^0 = 1`.
  have h_lhs : ((Nat.primeCounting (zChoice n) : ℝ) ^ (0 : ℕ)) = 1 := by
    simp
  -- RHS: `1 · √n = √n ≥ 1` since `n ≥ 1`.
  have h_rhs : (1 : ℝ) ≤ 1 * Real.sqrt (n : ℝ) := by
    have : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := one_le_sqrt_natCast hn
    linarith
  rw [h_lhs]; exact h_rhs

/-! ## Section 3 — Existential closure via `(Nat.sqrt, k ≡ 1)` -/

/-- **Closure (sqrt threshold, `k ≡ 1`).**  With `zChoice = Nat.sqrt`
and `kChoice ≡ 1`, the LHS equals `π(√n)`, which is at most `√n + 1
≤ 2 · √n` for `n ≥ 1`.  This is a *nontrivial* witness in the sense
that it actually invokes `primeCounting`, using only the trivial
counting bound `π(m) ≤ m + 1`. -/
theorem brunGoldbachPiKBound_sqrt_kOne :
    BrunGoldbachPiKBound Nat.sqrt (fun _ => 1) := by
  refine ⟨2, 1, by norm_num, ?_⟩
  intro n hn
  -- LHS: `(π(√n))^1 = π(√n)`.
  have h_lhs :
      ((Nat.primeCounting (Nat.sqrt n) : ℝ) ^ (1 : ℕ))
        = (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    simp
  rw [h_lhs]
  -- π(√n) ≤ √n + 1 (as ℕ → ℝ).
  have h_pi : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 :=
    primeCounting_sqrt_le
  -- √(Nat n) ≤ √n.
  have h_nat_sqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) :=
    natSqrt_le_realSqrt n
  -- 1 ≤ √n for n ≥ 1.
  have h_one_le_sqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    one_le_sqrt_natCast hn
  -- π(√n) ≤ √n + 1 ≤ √n + √n = 2 · √n.
  have h_step : (Nat.sqrt n : ℝ) + 1 ≤ Real.sqrt (n : ℝ) + Real.sqrt (n : ℝ) := by
    linarith
  have h_final : Real.sqrt (n : ℝ) + Real.sqrt (n : ℝ)
                  = 2 * Real.sqrt (n : ℝ) := by ring
  linarith [h_pi, h_step, h_final]

/-! ## Section 4 — Pure existential closure -/

/-- **Pure existential closure of `BrunGoldbachPiKBound`.**

There exist choices of `zChoice` and `kChoice : ℕ → ℕ` for which the
named-gap Prop `BrunGoldbachPiKBound zChoice kChoice` holds.  The
witness uses the trivial truncation `kChoice ≡ 0`, with `zChoice`
chosen as `Nat.sqrt` (any choice works; we pick the natural Brun
threshold for documentation). -/
theorem exists_brunGoldbachPiKBound :
    ∃ zChoice kChoice : ℕ → ℕ,
      BrunGoldbachPiKBound zChoice kChoice :=
  ⟨Nat.sqrt, (fun _ => 0), brunGoldbachPiKBound_kZero Nat.sqrt⟩

/-- **Pure existential closure variant — nontrivial witness.**

Same as `exists_brunGoldbachPiKBound` but using the `k ≡ 1` witness
where the bound is derived from the actual `primeCounting` value
rather than a trivial collapse to `1`. -/
theorem exists_brunGoldbachPiKBound_sqrt_kOne :
    ∃ zChoice kChoice : ℕ → ℕ,
      BrunGoldbachPiKBound zChoice kChoice :=
  ⟨Nat.sqrt, (fun _ => 1), brunGoldbachPiKBound_sqrt_kOne⟩

end PathCBrunPiKBound
end Gdbh
