/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P9-T3 (Phase 9 / Path C closure — paired Mertens third gap)
-/
import Gdbh.PathC_MertensProof

/-!
# Path C — Paired Mertens 3rd: decomposition into Mertens 2nd + log expansion

This file is the **P9-T3 deliverable** in Phase 9 (final Path C closure).
Its target is `PairedBrunMertensThirdGap` (from
`Gdbh/PathC_MertensProof.lean`), the *paired* Brun-sieve Mertens 3rd
upper bound

```
∃ C > 0, ∃ z₀, ∀ z ≥ z₀, pairedBrunFactor z ≤ C / (log z)^2 ,
```

where

```
pairedBrunFactor z = ∏_{3 ≤ p ≤ z, p prime} (1 - 2/p) .
```

## Mathematical content

The classical proof of `pairedBrunFactor(z) ~ C₀ / (log z)^2` is the
*paired* version of Mertens' 1874 theorem.  It chains:

1. **Mertens' 2nd theorem** (lower bound form, restricted to odd
   primes):
   `Σ_{3 ≤ p ≤ z, p prime} 1/p ≥ log(log z) - B`     ...(M2)

2. **Log expansion upper bound** (elementary, axiom-clean):
   For each prime `p ≥ 3`, `log(1 - 2/p) ≤ -2/p`.
   This follows from the **convex inequality** `log(x) ≤ x - 1`
   (mathlib's `Real.log_le_sub_one_of_pos`) applied at `x = 1 - 2/p`.

3. **Sum-then-exponentiate**:
   `Σ_p log(1 - 2/p) ≤ -2 Σ_p 1/p ≤ -2 (log log z - B) = -2 log log z + 2B`
   exponentiating, and using `log_pairedBrunFactor = Σ log(1-2/p)`:
   `pairedBrunFactor(z) ≤ exp(2B) / (log z)^2`.

## P9-T3 strategy and what is closed

The P9-T2 finding is that **the log-expansion side (step 2) is
elementary** — `log(1-2/p) ≤ -2/p` is a single application of
`log_le_sub_one_of_pos`.  Step (3) (sum + exponentiate) is pure
algebraic glue.  Therefore the *only* remaining mathlib gap is Mertens'
2nd theorem (step 1).

Concretely this file closes axiom-cleanly:

* `log_one_sub_two_div_prime_le` — for `p ≥ 3` prime, `log(1 - 2/p) ≤ -2/p`.
* `sum_log_pairedBrunFactor_le` — `Σ log(1-2/p) ≤ -2 Σ 1/p`.
* `log_pairedBrunFactor_eq_sum` — `log(pairedBrunFactor z) = Σ log(1-2/p)`.
* `pairedBrunFactor_le_exp_neg_two_sum_inv` — `pairedBrunFactor z ≤
  exp(-2 Σ 1/p)`.
* `pairedBrunMertensThirdGap_of_mertensSecondLowerOdd` — the
  **headline reduction**: the named open gap
  `MertensSecondLowerBoundOdd` implies `PairedBrunMertensThirdGap`.

What remains open (named precisely):

* `MertensSecondLowerBoundOdd` — Mertens' 2nd theorem, lower bound
  form, restricted to odd primes.  Mathlib v4.29.1: **open** (no
  `Mathlib.NumberTheory.*.Mertens` file).

## Axiom budget

Every theorem below is axiom-clean: the only axioms transitively used
are `Classical.choice`, `Quot.sound`, `propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62 (Theorems 1, 3).
* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.7–22.9 (Mertens
  theorems).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Lemma 2.5 (the paired
  Mertens product expansion).
-/

namespace Gdbh
namespace PathCMertensThirdProof

open Real Finset
open Gdbh.PathCMertensProof

/-! ## Section 1 — Elementary log expansion (closed axiom-clean)

For a real `x ∈ (0, 1)`, the **convex** inequality `log x ≤ x - 1`
(mathlib `Real.log_le_sub_one_of_pos`) specialises at `x = 1 - 2/p` to

```
log(1 - 2/p) ≤ (1 - 2/p) - 1 = -2/p ,
```

valid whenever `1 - 2/p > 0`, i.e. `p > 2`.  We apply this with `p` an
odd prime `≥ 3`. -/

/-- **Log-expansion upper bound for a single factor.**

For a prime `p ≥ 3`, `log(1 - 2/p) ≤ -2/p`.

This is the elementary half of Mertens' 3rd theorem (paired form):
`log(1 + u) ≤ u` applied at `u = -2/p ∈ (-1, 0)`. -/
theorem log_one_sub_two_div_prime_le {p : ℕ} (hp : 3 ≤ p) :
    Real.log (1 - 2 / (p : ℝ)) ≤ -(2 / (p : ℝ)) := by
  have hpos : (0 : ℝ) < 1 - 2 / (p : ℝ) := one_sub_two_div_prime_pos hp
  have hle := Real.log_le_sub_one_of_pos hpos
  -- hle : log (1 - 2/p) ≤ (1 - 2/p) - 1 = -(2/p)
  have hsimp : (1 - 2 / (p : ℝ)) - 1 = -(2 / (p : ℝ)) := by ring
  linarith [hle, hsimp.symm ▸ hle]

/-! ## Section 2 — Log of the paired product is a sum of logs -/

/-- `log(pairedBrunFactor z) = ∑_{3 ≤ p ≤ z, p prime} log(1 - 2/p)`. -/
theorem log_pairedBrunFactor_eq_sum (z : ℕ) :
    Real.log (pairedBrunFactor z)
      = ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          Real.log (1 - 2 / (p : ℝ)) := by
  unfold pairedBrunFactor
  rw [Real.log_prod]
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact ne_of_gt (one_sub_two_div_prime_pos hp3)

/-- **Summed log-expansion upper bound.**

`∑ log(1 - 2/p) ≤ -2 · ∑ 1/p`, where both sums range over primes
`3 ≤ p ≤ z`.  This is the sum form of `log_one_sub_two_div_prime_le`. -/
theorem sum_log_pairedBrunFactor_le (z : ℕ) :
    (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
        Real.log (1 - 2 / (p : ℝ)))
      ≤ -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ)) := by
  -- We rewrite the RHS as a sum of `-(2/p)` and use termwise bound.
  have hsum_eq :
      -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, -(2 / (p : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [hsum_eq]
  refine Finset.sum_le_sum ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
  rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
  exact log_one_sub_two_div_prime_le hp3

/-! ## Section 3 — Named open gap: Mertens 2nd lower bound (odd primes)

The genuine mathlib gap.  Restricted to odd primes (`3 ≤ p`) for direct
use with `pairedBrunFactor`. -/

/-- **Named open mathlib-gap Prop (Mertens' 2nd theorem, lower bound
form, odd primes).**

There exist constants `B : ℝ` and `z₀ : ℕ` such that for all `z ≥ z₀`,

```
log(log z) - B  ≤  ∑_{3 ≤ p ≤ z, p prime} 1/p .
```

This is Mertens' 1874 second theorem, restricted to odd primes
(excluding `p = 2`).  Mathlib v4.29.1 status: **open** — no
`Mathlib.NumberTheory.*.Mertens` file exists.

The restriction to `p ≥ 3` is harmless: the full Mertens 2nd
(`∑_{p ≤ z} 1/p ≥ log log z - B'`) implies the restricted form with
`B = B' + 1/2` (since we drop only the term `1/2`). -/
def MertensSecondLowerBoundOdd : Prop :=
  ∃ B : ℝ, ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
    Real.log (Real.log (z : ℝ)) - B
      ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

/-! ## Section 4 — Headline reduction: gap closes via exponentiation -/

/-- **Auxiliary**: `exp(2B - 2 log log z) = exp(2B) / (log z)^2` whenever
`log z > 0`. -/
theorem exp_two_B_minus_two_log_log_eq
    {z : ℕ} (hz : 3 ≤ z) (B : ℝ) :
    Real.exp (2 * B - 2 * Real.log (Real.log (z : ℝ)))
      = Real.exp (2 * B) / (Real.log (z : ℝ))^2 := by
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- exp(2B - 2 log log z) = exp(2B) * exp(-2 log log z)
  --                       = exp(2B) * exp(log log z)^{-2}
  --                       = exp(2B) * (log z)^{-2}
  have h1 : Real.exp (2 * B - 2 * Real.log (Real.log (z : ℝ)))
      = Real.exp (2 * B) * Real.exp (-(2 * Real.log (Real.log (z : ℝ)))) := by
    rw [show (2 * B - 2 * Real.log (Real.log (z : ℝ)))
            = (2 * B) + (-(2 * Real.log (Real.log (z : ℝ)))) from by ring,
        Real.exp_add]
  -- exp(-2 log log z) = (exp(log log z))^{-2} = (log z)^{-2}
  -- Use exp(n * x) = exp(x)^n for natural n, then negate.
  have h2 : Real.exp (-(2 * Real.log (Real.log (z : ℝ))))
      = 1 / (Real.log (z : ℝ))^2 := by
    rw [Real.exp_neg]
    -- exp(2 * log log z) = (log z)^2
    have hexp_two : Real.exp (2 * Real.log (Real.log (z : ℝ)))
        = (Real.log (z : ℝ))^2 := by
      have h2x : (2 : ℝ) * Real.log (Real.log (z : ℝ))
          = Real.log (Real.log (z : ℝ)) + Real.log (Real.log (z : ℝ)) := by ring
      rw [h2x, Real.exp_add, Real.exp_log hlogz_pos]
      ring
    rw [hexp_two]
    field_simp
  rw [h1, h2]
  field_simp

/-- **Headline P9-T3 reduction.**  The named open gap
`MertensSecondLowerBoundOdd` implies `PairedBrunMertensThirdGap`.

The reduction chains:

* the elementary `log(1 - 2/p) ≤ -2/p`;
* sum: `Σ log(1 - 2/p) ≤ -2 Σ 1/p ≤ -2(log log z - B) = 2B - 2 log log z`;
* exponentiate: `pairedBrunFactor z ≤ exp(2B - 2 log log z)
  = exp(2B) / (log z)^2`.

All steps are axiom-clean; only `MertensSecondLowerBoundOdd` is the
genuine mathlib input. -/
theorem pairedBrunMertensThirdGap_of_mertensSecondLowerOdd
    (h : MertensSecondLowerBoundOdd) :
    PairedBrunMertensThirdGap := by
  obtain ⟨B, z₀, hbound⟩ := h
  -- Exhibit C := exp(2B), and z₀' := max(z₀, 3).
  refine ⟨Real.exp (2 * B), max z₀ 3, Real.exp_pos _, ?_⟩
  intro z hz
  have hz0 : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hz3 : 3 ≤ z := le_trans (le_max_right _ _) hz
  have hz_real : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- Step (a): Mertens 2nd at z gives sum lower bound.
  have hsum_lb : Real.log (Real.log (z : ℝ)) - B
      ≤ ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
    hbound z hz0
  -- Step (b): -2 · (sum lb) ≥ -2 · sum, i.e. -2 · sum ≤ -2(log log z - B).
  have hsum_neg :
      -(2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        ≤ -(2 * (Real.log (Real.log (z : ℝ)) - B)) := by
    have : 2 * (Real.log (Real.log (z : ℝ)) - B)
        ≤ 2 * ∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      linarith [hsum_lb]
    linarith
  -- Step (c): sum of log(1 - 2/p) ≤ -2 · sum 1/p (from sum_log_pairedBrunFactor_le).
  have hsum_log_le := sum_log_pairedBrunFactor_le z
  -- Combine: sum of log(1 - 2/p) ≤ -2(log log z - B) = 2B - 2 log log z.
  have hcombined :
      (∑ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          Real.log (1 - 2 / (p : ℝ)))
        ≤ 2 * B - 2 * Real.log (Real.log (z : ℝ)) := by
    have h1 := le_trans hsum_log_le hsum_neg
    linarith
  -- Step (d): rewrite as log(pairedBrunFactor z) ≤ 2B - 2 log log z.
  have hlog_eq := log_pairedBrunFactor_eq_sum z
  have hlog_bd : Real.log (pairedBrunFactor z)
      ≤ 2 * B - 2 * Real.log (Real.log (z : ℝ)) := by
    rw [hlog_eq]; exact hcombined
  -- Step (e): exponentiate. exp is monotone, exp(log x) = x for x > 0.
  have hmpos : 0 < pairedBrunFactor z := pairedBrunFactor_pos z
  have hexp_bd : pairedBrunFactor z
      ≤ Real.exp (2 * B - 2 * Real.log (Real.log (z : ℝ))) := by
    have hexp_log : Real.exp (Real.log (pairedBrunFactor z)) = pairedBrunFactor z :=
      Real.exp_log hmpos
    have hmono : Real.exp (Real.log (pairedBrunFactor z))
        ≤ Real.exp (2 * B - 2 * Real.log (Real.log (z : ℝ))) :=
      Real.exp_le_exp.mpr hlog_bd
    rw [hexp_log] at hmono
    exact hmono
  -- Step (f): identify exp(2B - 2 log log z) = exp(2B) / (log z)^2.
  rw [exp_two_B_minus_two_log_log_eq hz3 B] at hexp_bd
  exact hexp_bd

/-! ## Section 5 — Downstream packaging

Composing with P8-T2's `pairedMertensProductUpperBound_pairedBrunFactor_of_gap`
gives `PairedMertensProductUpperBound pairedBrunFactor` from
`MertensSecondLowerBoundOdd`. -/

/-- **One-arrow reduction**: from the named Mertens 2nd gap to the
paired Mertens product upper bound for `pairedBrunFactor`. -/
theorem pairedMertensProductUpperBound_pairedBrunFactor_of_mertensSecond
    (h : MertensSecondLowerBoundOdd) :
    Gdbh.PathCMertensProduct.PairedMertensProductUpperBound pairedBrunFactor :=
  pairedMertensProductUpperBound_pairedBrunFactor_of_gap
    (pairedBrunMertensThirdGap_of_mertensSecondLowerOdd h)

/-! ## Section 6 — Documentation summary -/

/-- **P9-T3 summary, in proof form.**

Deliverables:

1. `log_one_sub_two_div_prime_le` — `log(1 - 2/p) ≤ -2/p` for `p ≥ 3`
   prime.  Closed axiom-clean (single application of
   `Real.log_le_sub_one_of_pos`).

2. `log_pairedBrunFactor_eq_sum` — log/sum identity for the paired
   product.  Closed axiom-clean via `Real.log_prod`.

3. `sum_log_pairedBrunFactor_le` — `Σ log(1-2/p) ≤ -2 Σ 1/p`.
   Closed axiom-clean (termwise application of (1) under `sum_le_sum`).

4. `exp_two_B_minus_two_log_log_eq` — algebraic identity
   `exp(2B - 2 log log z) = exp(2B) / (log z)^2` for `z ≥ 3`.
   Closed axiom-clean.

5. `MertensSecondLowerBoundOdd` — new named open mathlib-gap Prop.

6. `pairedBrunMertensThirdGap_of_mertensSecondLowerOdd` — **headline
   reduction**: the named gap implies `PairedBrunMertensThirdGap`.
   Closed axiom-clean.

7. `pairedMertensProductUpperBound_pairedBrunFactor_of_mertensSecond`
   — composed with P8-T2 to land on
   `PairedMertensProductUpperBound pairedBrunFactor`.

The smallest remaining mathlib gap is precisely `MertensSecondLowerBoundOdd`
— Mertens' 1874 second theorem, lower-bound form, restricted to odd
primes.  Once added to mathlib, the entire `PairedBrunMertensThirdGap`
gap closes via this file. -/
theorem pathC_p9_t3_summary : True := trivial

end PathCMertensThirdProof
end Gdbh
