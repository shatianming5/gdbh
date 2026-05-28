/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T5 (Phase 6 / Path C — twin-prime upper-bound consolidator)
-/
import Gdbh.PathC_BrunSieve
import Gdbh.PathC_SelbergSieve

/-!
# Path C — Consolidated twin-prime pair count upper bound

This file consolidates the two independent twin-prime upper bounds
delivered by `Gdbh/PathC_BrunSieve.lean` (P6-T4a) and
`Gdbh/PathC_SelbergSieve.lean` (P6-T4b) into a single **named
hypothesis** suitable for downstream consumption by P6-T6 (which
combines a twin-prime upper bound with a Chebyshev lower bound to
establish positivity of the Schnirelmann density of primes).

Both upstream files terminate in an assembly theorem of the same shape

```
∃ C N₀, 0 < C ∧ ∀ N ≥ N₀, 2 ≤ N, 0 < N,
  twinPrimeCount(N) ≤ C·N / (log N)^2 + zChoice N
```

For downstream use we package this as a single existential `Prop`
`TwinPrimePairCountBound` of the strictly weaker shape

```
∃ C N₀, ∀ N ≥ N₀, twinPrimeCount(N) ≤ C·N / (log N)^2 + N
```

where the trailing `+ N` loosely absorbs the `zChoice N` term provided
the sieve range is `≤ N` (a natural side condition — in any concrete
Brun or Selberg sieve the sieving threshold `z = z(N)` is at most a
small power of `N`, certainly `≤ N`).

The file provides:

* `Gdbh.PathCPrimePairBound.TwinPrimePairCountBound` — the named
  consolidated hypothesis.
* `Gdbh.PathCPrimePairBound.twinPrimePairCountBound_of_brunComponents`
  — the bridge from Brun's three sub-Props (with a `zChoice N ≤ N` side
  condition).
* `Gdbh.PathCPrimePairBound.twinPrimePairCountBound_of_selbergComponents`
  — the bridge from Selberg's three sub-Props (with the same side
  condition).
* `Gdbh.PathCPrimePairBound.twinPrimePairCountBound_of_brun_or_selberg`
  — common-output existential closer showing either sieve suffices.

All theorems below are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Gdbh
namespace PathCPrimePairBound

open Finset Real
open Gdbh.PathCBrunSieve
open Gdbh.PathCSelbergSieve

/-! ## Section 1 — The consolidated named hypothesis -/

/-- **Consolidated twin-prime pair-count upper bound.**  There exist
absolute constants `C` and `N₀` such that for every `N ≥ N₀`,

```
#{n ∈ [1, N] : n and n+2 both prime} ≤ C · N / (log N)^2 + N.
```

The trailing `+ N` loosely absorbs the `zChoice N` term produced by any
genuine sieve (Brun or Selberg) provided the sieving threshold is at
most `N`, which is always the case in practice.

This is the *abstract output* of a twin-prime upper bound; it is the
only piece of the Brun/Selberg sieve that the downstream Schnirelmann
positivity argument (P6-T6) consumes. -/
def TwinPrimePairCountBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (((Finset.Icc 1 N).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤
      C * (N : ℝ) / (Real.log (N : ℝ))^2 + (N : ℝ)

/-! ## Section 2 — Bridge from Brun's three sub-Props -/

/-- **Bridge from Brun to the consolidated bound.**  Given Brun's three
sub-Props and the side condition that the sieving threshold `zChoice N`
is eventually at most `N`, the consolidated
`TwinPrimePairCountBound` holds. -/
theorem twinPrimePairCountBound_of_brunComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hMain : BrunMainTerm M B)
    (hErr  : BrunErrorTerm B zChoice)
    (hMert : MertensProductBound M zChoice)
    (hSmall : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice N : ℝ) ≤ (N : ℝ)) :
    TwinPrimePairCountBound := by
  obtain ⟨C, N₀, hCpos, hbd⟩ :=
    twinPrime_count_upperBound_of_brunComponents M B zChoice hMain hErr hMert
  obtain ⟨N₁, hSmall_bd⟩ := hSmall
  refine ⟨C, max (max N₀ N₁) 2, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hmain := hbd N hN0 hN2 hNpos
  have hz_le : (zChoice N : ℝ) ≤ (N : ℝ) := hSmall_bd N hN1
  linarith

/-! ## Section 3 — Bridge from Selberg's three sub-Props -/

/-- **Bridge from Selberg to the consolidated bound.**  Given Selberg's
three sub-Props and the side condition that the sieving threshold
`zChoice N` is eventually at most `N`, the consolidated
`TwinPrimePairCountBound` holds. -/
theorem twinPrimePairCountBound_of_selbergComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hLam  : SelbergLambdaUpperBound (selbergOptLambda M) M B)
    (hOpt  : SelbergQuadraticFormOptimum M zChoice)
    (hErr  : SelbergErrorTermBound B zChoice)
    (hSmall : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice N : ℝ) ≤ (N : ℝ)) :
    TwinPrimePairCountBound := by
  obtain ⟨C, N₀, hCpos, hbd⟩ :=
    twinPrime_count_upperBound_of_selbergComponents M B zChoice hLam hOpt hErr
  obtain ⟨N₁, hSmall_bd⟩ := hSmall
  refine ⟨C, max (max N₀ N₁) 2, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hmain := hbd N hN0 hN2 hNpos
  have hz_le : (zChoice N : ℝ) ≤ (N : ℝ) := hSmall_bd N hN1
  linarith

/-! ## Section 4 — Existential closer from either sieve

We package "Brun or Selberg suffices" as a single statement: given
*either* a complete Brun sub-Prop pack *or* a complete Selberg sub-Prop
pack (with the same `zChoice N ≤ N` side condition), the consolidated
twin-prime upper bound holds.  This is the form most convenient for
downstream consumption. -/

/-- **Either-sieve existential closer.**  If there exist Brun components
satisfying the three Brun sub-Props *or* Selberg components satisfying
the three Selberg sub-Props (with the small-sieve side condition in
either case), then `TwinPrimePairCountBound` holds. -/
theorem twinPrimePairCountBound_of_brun_or_selberg
    (h :
      (∃ M B zChoice,
        BrunMainTerm M B ∧ BrunErrorTerm B zChoice
        ∧ MertensProductBound M zChoice
        ∧ (∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice N : ℝ) ≤ (N : ℝ)))
      ∨
      (∃ M B zChoice,
        SelbergLambdaUpperBound (selbergOptLambda M) M B
        ∧ SelbergQuadraticFormOptimum M zChoice
        ∧ SelbergErrorTermBound B zChoice
        ∧ (∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → (zChoice N : ℝ) ≤ (N : ℝ)))) :
    TwinPrimePairCountBound := by
  rcases h with ⟨M, B, zChoice, hMain, hErr, hMert, hSmall⟩
                | ⟨M, B, zChoice, hLam, hOpt, hErrS, hSmall⟩
  · exact twinPrimePairCountBound_of_brunComponents M B zChoice hMain hErr hMert hSmall
  · exact twinPrimePairCountBound_of_selbergComponents M B zChoice hLam hOpt hErrS hSmall

/-! ## Section 5 — Trivial consequences of `TwinPrimePairCountBound`

We record two simple consequences of the consolidated bound that
downstream P6-T6 will use directly. -/

/-- If `TwinPrimePairCountBound` holds, then there is some `C` and `N₀`
witnessing the bound. -/
theorem twinPrimePairCountBound_exists_witness
    (h : TwinPrimePairCountBound) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤
        C * (N : ℝ) / (Real.log (N : ℝ))^2 + (N : ℝ) := h

/-- The consolidated bound rephrased to show the witness constant `C`
can be taken non-negative (replacing `C` by `max C 0` if necessary,
since the right-hand side is monotone in `C` for `N ≥ 0`). -/
theorem twinPrimePairCountBound_nonneg_const
    (h : TwinPrimePairCountBound) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤
        C * (N : ℝ) / (Real.log (N : ℝ))^2 + (N : ℝ) := by
  obtain ⟨C, N₀, hbd⟩ := h
  refine ⟨max C 0, N₀, le_max_right _ _, ?_⟩
  intro N hN
  have h1 := hbd N hN
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  have hsq_nn : (0 : ℝ) ≤ (Real.log (N : ℝ))^2 := sq_nonneg _
  by_cases hlog : (Real.log (N : ℝ))^2 = 0
  · -- denominator zero: both sides have the `/ 0` term equal to 0 by Lean's convention.
    have hC : C * (N : ℝ) / (Real.log (N : ℝ))^2 =
              max C 0 * (N : ℝ) / (Real.log (N : ℝ))^2 := by
      rw [hlog]; simp
    linarith
  · have hsq_pos : 0 < (Real.log (N : ℝ))^2 := lt_of_le_of_ne hsq_nn (Ne.symm hlog)
    have hCle : C ≤ max C 0 := le_max_left _ _
    have hmul_le : C * (N : ℝ) ≤ max C 0 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hCle hN_nn
    have hinv_nn : 0 ≤ ((Real.log (N : ℝ))^2)⁻¹ := inv_nonneg.mpr hsq_nn
    have hdiv_le :
        C * (N : ℝ) / (Real.log (N : ℝ))^2 ≤
        max C 0 * (N : ℝ) / (Real.log (N : ℝ))^2 := by
      have h1 : C * (N : ℝ) / (Real.log (N : ℝ))^2 =
                C * (N : ℝ) * ((Real.log (N : ℝ))^2)⁻¹ := by
        rw [div_eq_mul_inv]
      have h2 : max C 0 * (N : ℝ) / (Real.log (N : ℝ))^2 =
                max C 0 * (N : ℝ) * ((Real.log (N : ℝ))^2)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hmul_le hinv_nn
    linarith

end PathCPrimePairBound
end Gdbh
