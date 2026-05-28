/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T4b (Phase 6 / Path C — Selberg's Λ² upper-bound sieve)
-/
import Gdbh.PathC_BrunSieve

/-!
# Path C — Selberg's `Λ²` upper-bound sieve and the twin-prime upper bound

Decomposition skeleton for Selberg's `Λ²` upper-bound sieve, mirroring
`Gdbh/PathC_BrunSieve.lean` (Brun pure sieve, P6-T4a).

Selberg's 1947 sieve replaces Brun's truncated Möbius-inversion with a
non-negative quadratic form `(∑_{d|n, d≤z} λ_d)²` in real parameters
`λ_d` with `λ_1 = 1`, then optimises over admissible `λ`.  The optimum
yields the bound `|{p ≤ N : p, p+2 both prime}| ≪ N / (log N)²`.

Selberg's argument decomposes into (i) the quadratic-form upper bound
`S(A, P, z) ≤ C₁ · N · M(z) + B(N, z)` with `M(z) = 1/∑_{d ≤ z} g(d)`,
(ii) the **quadratic-form optimisation** `M(z(N)) ≤ C₂/(log N)²`, and
(iii) the error estimate `B(N, z(N)) ≤ C₃ N/(log N)²`.  This file
exposes those three pieces as the `Prop`-valued sub-Props
`SelbergLambdaUpperBound`, `SelbergQuadraticFormOptimum`,
`SelbergErrorTermBound`, and provides the assembly theorem
`twinPrime_count_upperBound_of_selbergComponents` showing that they
combine to the Selberg-shape twin-prime upper bound.

The CONTENT of the sub-Props is deliberately Prop-level: this file does
*not* attempt to formalise the quadratic-form optimisation (which
requires substantial multiplicative-arithmetic infrastructure not yet
in mathlib; cf. `Mathlib.NumberTheory.SelbergSieve`).  The point is to
register the named open sub-Props in `audit_lean_axioms.py` so that
future analytic work can plug into a clean interface.

All theorems below are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.

## References

* A. Selberg, *On an elementary method in the theory of primes*,
  Norske Vid. Selsk. Forh. Trondheim 19 (1947), 64–67.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974.
-/

namespace Gdbh
namespace PathCSelbergSieve

open Finset Real
open Gdbh.PathCBrunSieve

/-! ## Section 1 — Selberg optimum weight (placeholder) and sub-Props -/

/-- Placeholder Selberg optimum weight.  In Selberg's argument the true
optimum has a concrete multiplicative-arithmetic formula; we use the
constant function `M 1` here, since the assembly theorem only uses
abstract sub-Props that *consume* `selbergOptLambda M`, not its
specific shape. -/
def selbergOptLambda (M : ℕ → ℝ) : ℕ → ℝ := fun _ => M 1

/-- `SelbergLambdaUpperBound lambdaFn M B` — the **Selberg quadratic
upper bound**: there is `C₁ > 0` with `siftedCount(N, z) ≤ C₁ · N · M(z) +
B(N, z)` for all `N, z`.  Same shape as Brun's `BrunMainTerm`; the
Selberg version produces a different main-term factor `M`
(the divisor-sum reciprocal `G(z) = 1/∑_{d ≤ z} g(d)`).  The
`lambdaFn` parameter records the Selberg side condition `λ_1 = M 1`
(abstract analogue of `λ_1 = 1`). -/
def SelbergLambdaUpperBound (lambdaFn : ℕ → ℝ) (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) :
    Prop :=
  lambdaFn 1 = M 1 ∧
    (∀ z, 0 ≤ M z) ∧
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ N z : ℕ, 0 < N →
        (siftedCount N z : ℝ) ≤ C₁ * (N : ℝ) * M z + B N z

/-- `SelbergQuadraticFormOptimum M zChoice` — the **quadratic-form
optimisation**: `M(zChoice N) ≤ C₂/(log N)²` for some `C₂ > 0` and all
sufficiently large `N`.  The `(log N)²` denominator (vs. Brun's
`log N`) is the characteristic Selberg gain from optimising the
quadratic form over the *pair* `(p, p+2)`. -/
def SelbergQuadraticFormOptimum (M : ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₂ N₀ : ℕ, 0 < C₂ ∧
    ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      M (zChoice N) ≤ (C₂ : ℝ) / (Real.log (N : ℝ))^2

/-- `SelbergErrorTermBound B zChoice` — the **error-term estimate**:
`B(N, zChoice N) ≤ C₃ · N/(log N)²` for some `C₃ > 0` and all
sufficiently large `N`.  In Selberg's argument `B(N, z) = R(z) =
∑_{d ≤ z²} 3^{ω(d)} |r_d|` where the `3^{ω(d)}` factor arises from
the lcm support of `λ_d λ_e`. -/
def SelbergErrorTermBound (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₃ N₀ : ℕ, 0 < C₃ ∧
    ∀ N : ℕ, N₀ ≤ N →
      B N (zChoice N) ≤ (C₃ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2

/-! ## Section 2 — Assembly theorem -/

/-- **Selberg's twin-prime upper bound, assembled from the three
sub-Props.**  Given `SelbergLambdaUpperBound (selbergOptLambda M) M B`,
`SelbergQuadraticFormOptimum M zChoice`, and `SelbergErrorTermBound B
zChoice`, there exist `C > 0` and `N₀` such that for all `N ≥ N₀`,
`#{p ≤ N : p, p+2 both prime} ≤ C · N/(log N)² + zChoice N`.  The
proof mirrors `twinPrime_count_upperBound_of_brunComponents`. -/
theorem twinPrime_count_upperBound_of_selbergComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hLam  : SelbergLambdaUpperBound (selbergOptLambda M) M B)
    (hOpt  : SelbergQuadraticFormOptimum M zChoice)
    (hErr  : SelbergErrorTermBound B zChoice) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → 0 < N →
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ C * (N : ℝ) / (Real.log (N : ℝ))^2 + (zChoice N : ℝ) := by
  obtain ⟨_, _hMnn, C₁, hC₁pos, hLam_bd⟩ := hLam
  obtain ⟨C₂, N₀opt, hC₂pos, hOpt_bd⟩ := hOpt
  obtain ⟨C₃, N₀err, hC₃pos, hErr_bd⟩ := hErr
  refine ⟨C₁ * (C₂ : ℝ) + (C₃ : ℝ), max N₀opt N₀err, ?_, ?_⟩
  · have hC₂real : (0 : ℝ) < (C₂ : ℝ) := by exact_mod_cast hC₂pos
    have hC₃real : (0 : ℝ) < (C₃ : ℝ) := by exact_mod_cast hC₃pos
    have : 0 < C₁ * (C₂ : ℝ) := mul_pos hC₁pos hC₂real
    linarith
  · intro N hN hN2 hNpos
    have hN_opt : N₀opt ≤ N := le_trans (le_max_left _ _) hN
    have hN_err : N₀err ≤ N := le_trans (le_max_right _ _) hN
    have h1 :
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ (siftedCount N (zChoice N) : ℝ) + (zChoice N : ℝ) := by
      exact_mod_cast twinPrime_count_le_siftedCount_add N (zChoice N)
    have h2 :
        (siftedCount N (zChoice N) : ℝ)
          ≤ C₁ * (N : ℝ) * M (zChoice N) + B N (zChoice N) :=
      hLam_bd N (zChoice N) hNpos
    have hlogN_pos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN2)
    have hlogN2_pos : 0 < (Real.log (N : ℝ))^2 := by positivity
    have hM_bd : M (zChoice N) ≤ (C₂ : ℝ) / (Real.log (N : ℝ))^2 :=
      hOpt_bd N hN_opt hN2
    have hB_bd :
        B N (zChoice N) ≤ (C₃ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2 :=
      hErr_bd N hN_err
    have hNreal_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
    have hC₁N_nn : 0 ≤ C₁ * (N : ℝ) := mul_nonneg (le_of_lt hC₁pos) hNreal_nn
    have h_main_bd :
        C₁ * (N : ℝ) * M (zChoice N)
          ≤ C₁ * (N : ℝ) * ((C₂ : ℝ) / (Real.log (N : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hM_bd hC₁N_nn
    have h_sift_bd :
        (siftedCount N (zChoice N) : ℝ)
          ≤ C₁ * (N : ℝ) * ((C₂ : ℝ) / (Real.log (N : ℝ))^2)
            + (C₃ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2 :=
      h2.trans (add_le_add h_main_bd hB_bd)
    have hlog2_ne : (Real.log (N : ℝ))^2 ≠ 0 := ne_of_gt hlogN2_pos
    have h_alg :
        C₁ * (N : ℝ) * ((C₂ : ℝ) / (Real.log (N : ℝ))^2)
          + (C₃ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2
        = (C₁ * (C₂ : ℝ) + (C₃ : ℝ)) * (N : ℝ) / (Real.log (N : ℝ))^2 := by
      field_simp
    rw [h_alg] at h_sift_bd
    linarith

/-! ## Section 3 — Existential repackaging and trivial skeleton closer -/

/-- **Existential form of Selberg's twin-prime upper bound.** -/
theorem exists_twinPrime_upperBound_of_selbergComponents
    (h : ∃ M B zChoice,
            SelbergLambdaUpperBound (selbergOptLambda M) M B ∧
            SelbergQuadraticFormOptimum M zChoice ∧
            SelbergErrorTermBound B zChoice) :
    ∃ (zChoice : ℕ → ℕ) (C : ℝ) (N₀ : ℕ), 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → 0 < N →
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ C * (N : ℝ) / (Real.log (N : ℝ))^2 + (zChoice N : ℝ) := by
  obtain ⟨M, B, zChoice, hLam, hOpt, hErr⟩ := h
  obtain ⟨C, N₀, hCpos, hbd⟩ :=
    twinPrime_count_upperBound_of_selbergComponents M B zChoice hLam hOpt hErr
  exact ⟨zChoice, C, N₀, hCpos, hbd⟩

/-- **Trivial skeleton closer for the qualitative Selberg-optimum
lambda witness.**  For any nonneg `M : ℕ → ℝ`, there exists an error
reservoir `B` with `SelbergLambdaUpperBound (selbergOptLambda M) M B`.
We use the worst-case `B(N, z) = N` and `C₁ = 1`, relying on
`siftedCount ≤ N`.  The genuine *quantitative* Selberg-optimum content
remains in the open sub-Prop `SelbergQuadraticFormOptimum`. -/
theorem exists_selberg_optimum_lambda_witness (M : ℕ → ℝ)
    (hMnn : ∀ z, 0 ≤ M z) :
    ∃ B : ℕ → ℕ → ℝ,
      SelbergLambdaUpperBound (selbergOptLambda M) M B := by
  refine ⟨fun N _ => (N : ℝ), rfl, hMnn, 1, by norm_num, ?_⟩
  intro N z hN
  have hSift : (siftedCount N z : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast siftedCount_le N z
  have h_extra : 0 ≤ 1 * (N : ℝ) * M z := by
    have : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
    have := hMnn z; positivity
  linarith

end PathCSelbergSieve
end Gdbh
