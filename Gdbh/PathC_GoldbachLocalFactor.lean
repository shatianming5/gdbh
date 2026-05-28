import Gdbh.PathC_BrunRefinedComposition

/-!
# Path C -- Goldbach local factor interface

This file records the honest local-density shape for the Goldbach paired
sieve.  For an odd prime `p`, the forbidden residue classes for
`m (n - m)` modulo `p` are:

* one class when `p ∣ n`, since `m ≡ 0` and `m ≡ n` coincide;
* two classes otherwise.

The old `pairedBrunFactor z = ∏ (1 - 2 / p)` is therefore the uniform
worst local density only for primes not dividing `n`.  The honest
main factor is `n`-dependent and equals the old paired factor times a
truncated Goldbach singular multiplier.
-/

namespace Gdbh
namespace PathCGoldbachLocalFactor

open scoped BigOperators
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos
  one_sub_two_div_prime_pos)
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCBrunRefinedComposition (BrunGoldbachPairedMainTermRefined
  refinedReservoir)
open Gdbh.PathCTwinAsymptotic (goldbachRepresentationCount)

/-- Number of bad residue classes modulo an odd prime for the Goldbach
paired sieve at target sum `n`: one if `p ∣ n`, two otherwise. -/
def goldbachBadResidueCard (n p : ℕ) : ℕ :=
  if p ∣ n then 1 else 2

@[simp] theorem goldbachBadResidueCard_of_dvd {n p : ℕ} (h : p ∣ n) :
    goldbachBadResidueCard n p = 1 := by
  simp [goldbachBadResidueCard, h]

@[simp] theorem goldbachBadResidueCard_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) :
    goldbachBadResidueCard n p = 2 := by
  simp [goldbachBadResidueCard, h]

/-- The honest `n`-dependent Goldbach paired-sieve local factor, truncated at
the sieve level `z`. -/
noncomputable def goldbachLocalFactor (n z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
    (1 - (goldbachBadResidueCard n p : ℝ) / (p : ℝ))

/-- The truncated Goldbach singular multiplier.  This is the correction factor
between the uniform paired factor and the honest local factor. -/
noncomputable def truncatedGoldbachSingularMultiplier (n z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
    if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1

/-- The full finite singular multiplier over odd prime divisors of `n`, using
the same finite product style as the truncated multiplier. -/
noncomputable def goldbachSingularMultiplier (n : ℕ) : ℝ :=
  truncatedGoldbachSingularMultiplier n n

private lemma one_sub_one_div_nat_pos {p : ℕ} (hp : 2 ≤ p) :
    (0 : ℝ) < 1 - 1 / (p : ℝ) := by
  have hp_real : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp
  have h_one_div_le : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp_real
  linarith

/-- The honest local factor is positive for every target and truncation. -/
theorem goldbachLocalFactor_pos (n z : ℕ) :
    0 < goldbachLocalFactor n z := by
  classical
  unfold goldbachLocalFactor
  refine Finset.prod_pos ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  by_cases hpn : p ∣ n
  · have hlt : (1 : ℝ) / (p : ℝ) < 1 := by
      have h := one_sub_one_div_nat_pos (by omega : 2 ≤ p)
      linarith
    simpa [goldbachBadResidueCard, hpn] using hlt
  · have hlt : (2 : ℝ) / (p : ℝ) < 1 := by
      have h := one_sub_two_div_prime_pos hp3
      linarith
    simpa [goldbachBadResidueCard, hpn] using hlt

/-- The honest local factor is the old paired factor multiplied by the
truncated Goldbach singular multiplier. -/
theorem goldbachLocalFactor_eq_paired_mul_singularMultiplier (n z : ℕ) :
    goldbachLocalFactor n z =
      pairedBrunFactor z * truncatedGoldbachSingularMultiplier n z := by
  classical
  unfold goldbachLocalFactor pairedBrunFactor truncatedGoldbachSingularMultiplier
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  have hp_ne0 : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (by omega : 0 < p)
    exact this.ne'
  have hp_sub_ne0 : (p : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (p : ℝ) := by
      exact_mod_cast (by omega : 2 < p)
    linarith
  by_cases hpn : p ∣ n
  · simp [goldbachBadResidueCard, hpn]
    field_simp [hp_ne0, hp_sub_ne0]
    ring
  · simp [goldbachBadResidueCard, hpn]

/-- The truncated singular multiplier is at least one. -/
theorem truncatedGoldbachSingularMultiplier_ge_one (n z : ℕ) :
    1 ≤ truncatedGoldbachSingularMultiplier n z := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.one_le_prod ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  by_cases hpn : p ∣ n
  · have hpos : (0 : ℝ) < (p : ℝ) - 2 := by
      have : (2 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by omega : 2 < p)
      linarith
    have hnonneg : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := by
      positivity
    simp [hpn]
    linarith
  · simp [hpn]

/-- The `n`-dependent Goldbach local factor always dominates the uniform
paired Brun factor.  Equality holds away from odd prime divisors of `n`; at
dividing primes the local density is larger because the two forbidden
residue classes coincide. -/
theorem pairedBrunFactor_le_goldbachLocalFactor (n z : ℕ) :
    pairedBrunFactor z ≤ goldbachLocalFactor n z := by
  have hsing : 1 ≤ truncatedGoldbachSingularMultiplier n z :=
    truncatedGoldbachSingularMultiplier_ge_one n z
  have hpaired_nonneg : 0 ≤ pairedBrunFactor z :=
    le_of_lt (pairedBrunFactor_pos z)
  rw [goldbachLocalFactor_eq_paired_mul_singularMultiplier]
  calc
    pairedBrunFactor z = pairedBrunFactor z * 1 := by ring
    _ ≤ pairedBrunFactor z * truncatedGoldbachSingularMultiplier n z := by
      exact mul_le_mul_of_nonneg_left hsing hpaired_nonneg

/-- Corrected refined main-term target with the `n`-dependent local factor.
This is the intended replacement for the current uniform-factor
`BrunGoldbachPairedMainTermRefined` when formalising the actual
Halberstam-Richert/Brun Goldbach upper-bound sieve. -/
def BrunGoldbachLocalMainTermRefined : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachLocalFactor n z + refinedReservoir n z

/-- Final-assembly local main-term target.  The downstream singular-factor
representation bound only uses the sieve at `z = Nat.sqrt n` and only
eventually in `n`, so this is the narrowest local-factor target. -/
def BrunGoldbachLocalMainTermRefinedAtSqrt : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n)

/-- Final-assembly local main-term target allowing a fixed constant multiple
of the refined reservoir.  This is the most practical paired-sieve output
shape when the analytic finite-sieve error is closed only up to an absolute
constant. -/
def BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant : Prop :=
  ∃ C₁ C_E : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧ 0 < C_E ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + C_E * refinedReservoir n (Nat.sqrt n)

/-- The all-threshold refined local main-term target implies the final
assembly `z = Nat.sqrt n` target. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_of_refined
    (hMain : BrunGoldbachLocalMainTermRefined) :
    BrunGoldbachLocalMainTermRefinedAtSqrt := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, 2, hC₁_pos, ?_⟩
  intro n _hn hn2
  exact hMainBd n (Nat.sqrt n) (by omega)

/-- The coefficient-one final-assembly target is a special case of the
constant-error final-assembly target. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_atSqrt
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant := by
  rcases hMain with ⟨C₁, N₀, hC₁_pos, hMainBd⟩
  refine ⟨C₁, 1, N₀, hC₁_pos, by norm_num, ?_⟩
  intro n hn hn2
  simpa using hMainBd n hn hn2

/-- Corrected local main-term target allowing a fixed constant multiple of
the refined reservoir.  This is the more natural output shape for a
finite-sieve error estimate; the constant is harmless in the downstream
representation bound, where all fixed constants are absorbed. -/
def BrunGoldbachLocalMainTermRefinedWithErrorConstant : Prop :=
  ∃ C₁ C_E : ℝ, 0 < C₁ ∧ 0 < C_E ∧
    ∀ n z : ℕ, 0 < n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachLocalFactor n z
          + C_E * refinedReservoir n z

/-- The coefficient-one refined local main-term target is a special case of
the constant-error version. -/
theorem brunGoldbachLocalMainTermRefinedWithErrorConstant_of_refined
    (hMain : BrunGoldbachLocalMainTermRefined) :
    BrunGoldbachLocalMainTermRefinedWithErrorConstant := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, 1, hC₁_pos, by norm_num, ?_⟩
  intro n z hn
  simpa using hMainBd n z hn

/-- The all-threshold constant-error target implies the final-assembly
constant-error target at `z = Nat.sqrt n`. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_withErrorConstant
    (hMain : BrunGoldbachLocalMainTermRefinedWithErrorConstant) :
    BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant := by
  rcases hMain with ⟨C₁, C_E, hC₁_pos, hCE_pos, hMainBd⟩
  refine ⟨C₁, C_E, 2, hC₁_pos, hCE_pos, ?_⟩
  intro n _hn hn2
  exact hMainBd n (Nat.sqrt n) (by omega)

/-- Singular-factor version of the Goldbach representation bound.  This is
the theorem shape delivered by the local-density sieve; by itself it should
not be confused with the stronger uniform `GoldbachRepresentationBound`
consumed by the current Schnirelmann-counting endpoint. -/
def GoldbachRepresentationBoundWithSingularFactor : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
    (goldbachRepresentationCount n : ℝ) ≤
      C * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n

/-- The older uniform paired-factor refined main term is stronger than the
corrected local-factor main term.  This connector lets any future proof of
`BrunGoldbachPairedMainTermRefined` feed the singular-factor route, while the
recommended direct target remains `BrunGoldbachLocalMainTermRefined`. -/
theorem brunGoldbachLocalMainTermRefined_of_paired
    (hMain : BrunGoldbachPairedMainTermRefined) :
    BrunGoldbachLocalMainTermRefined := by
  rcases hMain with ⟨_hFactor, C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn
  have hbd := hMainBd n z hn
  have hfactor :
      C₁ * (n : ℝ) * pairedBrunFactor z ≤
        C₁ * (n : ℝ) * goldbachLocalFactor n z := by
    exact mul_le_mul_of_nonneg_left
      (pairedBrunFactor_le_goldbachLocalFactor n z)
      (mul_nonneg (le_of_lt hC₁_pos) (by positivity))
  linarith

end PathCGoldbachLocalFactor
end Gdbh
