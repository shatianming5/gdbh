/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P8-T5a (Phase 8 / Path C closure — concrete zChoice satisfying
the satisfiable Mertens route)
-/
import Gdbh.PathC_MertensProduct

/-!
# Path C — Concrete `zChoice` (square-root choice)

The P8-T5a refactor of `Gdbh/PathC_MertensProduct.lean` introduces the
**satisfiable** assembly

```
PairedMertensProductUpperBound M  +  SinglePowerLogZBound zChoice
  +  ZChoiceUnbounded zChoice
  ⇒  MertensProductBound M zChoice
```

(see `mertensProductBound_of_paired_and_singleLog`).  The earlier
P7-T3 assembly used `PairedSieveLogZBound zChoice` (i.e.
`log(zChoice N) ≥ K (log N)^2`), which together with the side condition
`zChoice N ≤ N` of `PathC_PrimePairBound` produced an **unsatisfiable**
constraint pair.  The fix is to push the squared `(log)^2` into the
*Mertens* side (`M(z) ≤ C/(log z)^2`, which is what the paired Brun
sieve produces directly) and only require `log(zChoice N) ≥ K · log N`
of `zChoice`.

This file provides a **concrete** witness for the three abstract
`zChoice` Props consumed by the new assembly:

* `zChoice₀ N := Nat.sqrt N` — the canonical Brun-style square-root
  sieve cutoff.
* `singlePowerLogZBound_zChoice₀ : SinglePowerLogZBound zChoice₀`
  with `K = 1/4` and threshold `N ≥ 16`.
* `zChoice₀_small : ∃ N₁, ∀ N ≥ N₁, (zChoice₀ N : ℝ) ≤ (N : ℝ)`
  — trivial from `Nat.sqrt_le_self` (with `N₁ = 0`).
* `zChoiceUnbounded_zChoice₀ : ZChoiceUnbounded zChoice₀`
  — `Nat.sqrt` is monotone and unbounded.

All proofs are axiom-clean (`[Classical.choice, Quot.sound, propext]`).
-/

namespace Gdbh
namespace PathCZChoiceConcrete

open Real
open Gdbh.PathCMertensProduct

/-- Concrete square-root sieve cutoff `zChoice₀ N := Nat.sqrt N`. -/
def zChoice₀ (N : ℕ) : ℕ := Nat.sqrt N

/-! ## Small-sieve side condition: `zChoice₀ N ≤ N`. -/

/-- `zChoice₀ N ≤ N` for every `N`.  This is `Nat.sqrt_le_self`. -/
theorem zChoice₀_le_self (N : ℕ) : zChoice₀ N ≤ N := Nat.sqrt_le_self N

/-- **Small-sieve side condition** for `zChoice₀`: `(zChoice₀ N : ℝ) ≤
(N : ℝ)` for all `N` (trivially, with `N₁ = 0`). -/
theorem zChoice₀_small :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice₀ N : ℝ) ≤ (N : ℝ) := by
  refine ⟨0, ?_⟩
  intro N _
  exact_mod_cast zChoice₀_le_self N

/-! ## Unboundedness of `zChoice₀`. -/

/-- For any threshold `z₀`, `zChoice₀ N = Nat.sqrt N ≥ z₀` for
`N ≥ z₀^2`. -/
theorem zChoice₀_ge_of_sq_le (z₀ N : ℕ) (h : z₀ * z₀ ≤ N) :
    z₀ ≤ zChoice₀ N := by
  unfold zChoice₀
  exact Nat.le_sqrt.mpr h

/-- **Unboundedness** of `zChoice₀`. -/
theorem zChoiceUnbounded_zChoice₀ : ZChoiceUnbounded zChoice₀ := by
  intro z₀
  refine ⟨z₀ * z₀, ?_⟩
  intro N hN
  exact zChoice₀_ge_of_sq_le z₀ N hN

/-! ## Single-power log-z bound for `zChoice₀`.

We show that for `N ≥ 16`, `log(Nat.sqrt N) ≥ (log N)/4`, hence
`SinglePowerLogZBound zChoice₀` holds with `K = 1/4`.

**Proof sketch.**  `(Nat.sqrt N + 1)^2 > N` (definitional).  For
`N ≥ 4`, `Nat.sqrt N ≥ 2`, so `Nat.sqrt N + 1 ≤ Nat.sqrt N + Nat.sqrt N
= 2 · Nat.sqrt N`.  Hence `(2 · Nat.sqrt N)^2 ≥ (Nat.sqrt N + 1)^2 > N`,
i.e. `4 · (Nat.sqrt N)^2 > N`.  Taking logs and using
`log(N) - log(4) ≥ (log N)/2` for `N ≥ 16` (i.e. `log N ≥ log 16 = 2
log 4`), we get `2 log(Nat.sqrt N) ≥ (log N)/2`, so
`log(Nat.sqrt N) ≥ (log N)/4`. -/

private lemma sqrt_ge_two_of_ge_four {N : ℕ} (h : 4 ≤ N) :
    2 ≤ Nat.sqrt N := by
  -- `Nat.le_sqrt`: `m ≤ Nat.sqrt n ↔ m * m ≤ n`.
  exact Nat.le_sqrt.mpr (by omega : 2 * 2 ≤ N)

private lemma four_sq_sqrt_gt {N : ℕ} (hN : 4 ≤ N) :
    N < 4 * (Nat.sqrt N) * (Nat.sqrt N) := by
  -- From `Nat.sqrt N ≥ 2` we get `Nat.sqrt N + 1 ≤ 2 · Nat.sqrt N`.
  have h2 : 2 ≤ Nat.sqrt N := sqrt_ge_two_of_ge_four hN
  have hSucc : Nat.sqrt N + 1 ≤ 2 * Nat.sqrt N := by omega
  -- `N < (Nat.sqrt N + 1)^2`.
  have hN_lt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  -- Hence `N < (2 · Nat.sqrt N)^2 = 4 · (Nat.sqrt N)^2`.
  have hSq : (Nat.sqrt N + 1) * (Nat.sqrt N + 1)
      ≤ (2 * Nat.sqrt N) * (2 * Nat.sqrt N) :=
    Nat.mul_le_mul hSucc hSucc
  have : N < (2 * Nat.sqrt N) * (2 * Nat.sqrt N) := lt_of_lt_of_le hN_lt hSq
  have heq : (2 * Nat.sqrt N) * (2 * Nat.sqrt N)
      = 4 * (Nat.sqrt N) * (Nat.sqrt N) := by ring
  rw [heq] at this
  exact this

/-- **Single-power log-z bound** for `zChoice₀` with `K = 1/4`. -/
theorem singlePowerLogZBound_zChoice₀ : SinglePowerLogZBound zChoice₀ := by
  refine ⟨(1 : ℝ) / 4, 16, by norm_num, ?_⟩
  intro N hN hN2
  -- Real-arithmetic facts about `N`.
  have hN16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN4 : 4 ≤ N := by omega
  have hN4r : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN_gt1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt1
  -- `log 4 ≤ (log N)/2`, since `N ≥ 16 = 4^2`, i.e. `log N ≥ 2 log 4`.
  have h_log16 : Real.log (16 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) hN16
  have h_log16_eq : Real.log (16 : ℝ) = 2 * Real.log (4 : ℝ) := by
    have : (16 : ℝ) = (4 : ℝ)^2 := by norm_num
    rw [this, Real.log_pow]
    ring
  have h_log4_half : Real.log (4 : ℝ) ≤ Real.log (N : ℝ) / 2 := by
    have := h_log16
    rw [h_log16_eq] at this
    linarith
  -- `Nat.sqrt N ≥ 2 ≥ 1`, so `(Nat.sqrt N : ℝ) ≥ 1 > 0`.
  have hsqrt_ge2 : 2 ≤ Nat.sqrt N := sqrt_ge_two_of_ge_four hN4
  have hsqrt_ge2_r : (2 : ℝ) ≤ ((Nat.sqrt N : ℕ) : ℝ) := by exact_mod_cast hsqrt_ge2
  have hsqrt_pos : (0 : ℝ) < ((Nat.sqrt N : ℕ) : ℝ) := by linarith
  have hsqrt_ge1 : (1 : ℝ) ≤ ((Nat.sqrt N : ℕ) : ℝ) := by linarith
  -- Core inequality: `N < 4 · (Nat.sqrt N)^2` as reals.
  have h_core_nat : N < 4 * (Nat.sqrt N) * (Nat.sqrt N) := four_sq_sqrt_gt hN4
  have h_core_r : (N : ℝ) < 4 * ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ) := by
    have := h_core_nat
    have hcast : ((4 * (Nat.sqrt N) * (Nat.sqrt N) : ℕ) : ℝ)
        = 4 * ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ) := by
      push_cast; ring
    exact_mod_cast this
  -- Take logs.
  have h4sqsq_pos : (0 : ℝ) < 4 * ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ) := by
    have : (0 : ℝ) < 4 * ((Nat.sqrt N : ℕ) : ℝ) := by linarith
    exact mul_pos this hsqrt_pos
  have h_logN_le : Real.log (N : ℝ)
      ≤ Real.log (4 * ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ)) :=
    (Real.log_le_log hN_pos (le_of_lt h_core_r))
  -- Simplify the RHS log.
  have h_log_rhs :
      Real.log (4 * ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ))
        = Real.log 4 + 2 * Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
    have h4_pos : (0 : ℝ) < 4 := by norm_num
    have h4s_pos : (0 : ℝ) < 4 * ((Nat.sqrt N : ℕ) : ℝ) := by linarith
    rw [Real.log_mul (ne_of_gt h4s_pos) (ne_of_gt hsqrt_pos),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hsqrt_pos)]
    ring
  rw [h_log_rhs] at h_logN_le
  -- So `log N ≤ log 4 + 2 log(Nat.sqrt N)`, i.e.
  -- `log N - log 4 ≤ 2 log(Nat.sqrt N)`.
  -- Using `log 4 ≤ (log N)/2`, we get `(log N)/2 ≤ 2 log(Nat.sqrt N)`,
  -- i.e. `(log N)/4 ≤ log(Nat.sqrt N)`.
  have h_logsqrt_ge : Real.log (N : ℝ) / 4
      ≤ Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
    have : Real.log (N : ℝ) - Real.log 4 ≤ 2 * Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
      linarith
    have h_half : Real.log (N : ℝ) / 2
        ≤ 2 * Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
      linarith
    linarith
  -- Conclude.
  show (1 : ℝ) / 4 * Real.log (N : ℝ) ≤ Real.log (zChoice₀ N : ℝ)
  unfold zChoice₀
  have : (1 : ℝ) / 4 * Real.log (N : ℝ) = Real.log (N : ℝ) / 4 := by ring
  rw [this]
  exact h_logsqrt_ge

/-! ## Convenience: a single conjunction recording the three closed
properties of `zChoice₀`. -/

/-- The three closed properties of `zChoice₀` consumed by the new
`mertensProductBound_of_paired_and_singleLog` assembly. -/
theorem zChoice₀_properties :
    SinglePowerLogZBound zChoice₀ ∧
    ZChoiceUnbounded zChoice₀ ∧
    (∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice₀ N : ℝ) ≤ (N : ℝ)) :=
  ⟨singlePowerLogZBound_zChoice₀, zChoiceUnbounded_zChoice₀, zChoice₀_small⟩

end PathCZChoiceConcrete
end Gdbh
