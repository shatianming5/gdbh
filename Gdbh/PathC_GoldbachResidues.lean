import Gdbh.PathC_GoldbachLocalFactor
import Mathlib.Data.ZMod.Basic

/-!
# Path C -- Goldbach bad residue classes

This file links the local-factor interface to the elementary residue model:
for a fixed target `n` and modulus `p`, the bad classes for the paired
Goldbach sieve are `{0, n}` in `ZMod p`.  Their cardinal is exactly
`goldbachBadResidueCard n p`.
-/

namespace Gdbh
namespace PathCGoldbachResidues

open Gdbh.PathCGoldbachLocalFactor
  (BrunGoldbachLocalMainTermRefined BrunGoldbachLocalMainTermRefinedWithErrorConstant
   BrunGoldbachLocalMainTermRefinedAtSqrt
   BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant
   goldbachBadResidueCard goldbachLocalFactor goldbachLocalFactor_pos)
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet mem_goldbachSiftedPairSet)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir)

/-- Bad residue classes modulo `p` for the paired Goldbach sieve at target
sum `n`: a residue `a` is bad when `a = 0` or `a = n`. -/
def goldbachBadResidueSet (n p : ℕ) : Finset (ZMod p) :=
  {0, (n : ZMod p)}

@[simp] theorem mem_goldbachBadResidueSet {n p : ℕ} {a : ZMod p} :
    a ∈ goldbachBadResidueSet n p ↔ a = 0 ∨ a = (n : ZMod p) := by
  simp [goldbachBadResidueSet]

/-- The bad residue set has one class when `p ∣ n` and two classes otherwise,
matching `goldbachBadResidueCard`. -/
theorem goldbachBadResidueSet_card (n p : ℕ) :
    (goldbachBadResidueSet n p).card = goldbachBadResidueCard n p := by
  classical
  unfold goldbachBadResidueSet goldbachBadResidueCard
  by_cases h : p ∣ n
  · have hzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr h
    simp [h, hzero]
  · have hne : (n : ZMod p) ≠ 0 := by
      intro hzero
      exact h ((ZMod.natCast_eq_zero_iff n p).mp hzero)
    have hne' : (0 : ZMod p) ≠ (n : ZMod p) := by
      intro hz
      exact hne hz.symm
    simpa [h] using (Finset.card_pair hne')

/-- The bad residue set is always nonempty. -/
theorem one_le_goldbachBadResidueSet_card (n p : ℕ) :
    1 ≤ (goldbachBadResidueSet n p).card := by
  rw [goldbachBadResidueSet_card]
  unfold goldbachBadResidueCard
  by_cases h : p ∣ n <;> simp [h]

/-- The paired Goldbach bad residue set has at most two classes. -/
theorem goldbachBadResidueSet_card_le_two (n p : ℕ) :
    (goldbachBadResidueSet n p).card ≤ 2 := by
  rw [goldbachBadResidueSet_card]
  unfold goldbachBadResidueCard
  by_cases h : p ∣ n <;> simp [h]

/-- The corrected local factor can be written directly as the product over
the cardinalities of the bad residue sets.  This is the residue-model form
needed by a finite upper-bound sieve. -/
theorem goldbachLocalFactor_eq_badResidueSet_card_product (n z : ℕ) :
    goldbachLocalFactor n z =
      ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
        (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
  classical
  unfold goldbachLocalFactor
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [goldbachBadResidueSet_card]

/-- Each residue-cardinality Euler factor is positive for odd primes in the
Goldbach sieve range. -/
theorem goldbachResidueFactorTerm_pos {n p : ℕ} (hp3 : 3 ≤ p) :
    0 < 1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) := by
  have hcard_le : (goldbachBadResidueSet n p).card ≤ 2 :=
    goldbachBadResidueSet_card_le_two n p
  have hcard_lt_p : ((goldbachBadResidueSet n p).card : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt hcard_le (by omega : 2 < p))
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (by omega : 0 < p)
  have hdiv_lt : ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) < 1 := by
    exact (div_lt_one hp_pos).mpr hcard_lt_p
  linarith

/-- Each residue-cardinality Euler factor is at most one. -/
theorem goldbachResidueFactorTerm_le_one {n p : ℕ} (hp0 : 0 < p) :
    1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) ≤ 1 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp0
  have hdiv_nonneg :
      0 ≤ ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) := by
    positivity
  linarith

/-- Each odd-prime residue-cardinality Euler factor is nonnegative. -/
theorem goldbachResidueFactorTerm_nonneg {n p : ℕ} (hp3 : 3 ≤ p) :
    0 ≤ 1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ) :=
  le_of_lt (goldbachResidueFactorTerm_pos (n := n) hp3)

/-- The residue-cardinality form of the corrected Goldbach local density. -/
noncomputable def goldbachResidueMainFactor (n z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
    (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ))

/-- The residue-cardinality main factor is the same as the corrected
`goldbachLocalFactor`. -/
theorem goldbachResidueMainFactor_eq_goldbachLocalFactor (n z : ℕ) :
    goldbachResidueMainFactor n z = goldbachLocalFactor n z := by
  rw [goldbachResidueMainFactor, goldbachLocalFactor_eq_badResidueSet_card_product]

/-- The residue-cardinality main factor is positive. -/
theorem goldbachResidueMainFactor_pos (n z : ℕ) :
    0 < goldbachResidueMainFactor n z := by
  simpa [goldbachResidueMainFactor_eq_goldbachLocalFactor n z] using
    goldbachLocalFactor_pos n z

/-- The residue-cardinality main factor is nonnegative. -/
theorem goldbachResidueMainFactor_nonneg (n z : ℕ) :
    0 ≤ goldbachResidueMainFactor n z :=
  le_of_lt (goldbachResidueMainFactor_pos n z)

/-- If there are no odd primes in the sieve range, the residue main factor is
the empty product. -/
theorem goldbachResidueMainFactor_eq_one_of_lt_three
    (n : ℕ) {z : ℕ} (hz : z < 3) :
    goldbachResidueMainFactor n z = 1 := by
  simp [goldbachResidueMainFactor, hz]

/-- Paired-sift main-term target with an abstract error reservoir.  This is
the finite-sieve component a Brun/Halberstam-Richert worker should prove
before optimising the error into the fixed `refinedReservoir`. -/
def BrunGoldbachResidueMainTermWithError (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n z + B n z

/-- The abstract error reservoir is pointwise dominated by the refined
reservoir used by the current Path C route. -/
def GoldbachResidueErrorDominatedByRefined (B : ℕ → ℕ → ℝ) : Prop :=
  ∀ n z : ℕ, B n z ≤ refinedReservoir n z

/-- The abstract finite-sieve error reservoir is bounded by a fixed constant
multiple of the refined reservoir.  This is the practical target for
combinatorial error estimates. -/
def GoldbachResidueErrorBoundedByRefined (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ C_E : ℝ, 0 < C_E ∧ ∀ n z : ℕ, B n z ≤ C_E * refinedReservoir n z

/-- Refined Goldbach main-term target in the direct residue-set language.
This is the preferred finite-sieve interface: prove the paired sift upper
bound using the actual bad residue set modulo each odd prime. -/
def BrunGoldbachResidueMainTermRefined : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n z + refinedReservoir n z

/-- A residue main-term bound with any error reservoir dominated by
`refinedReservoir` closes the refined residue main-term target. -/
theorem brunGoldbachResidueMainTermRefined_of_error_dominated
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorDominatedByRefined B) :
    BrunGoldbachResidueMainTermRefined := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn
  have hbd := hMainBd n z hn
  have herr := hErr n z
  linarith

/-- The refined residue main-term target is equivalent to the existence of an
abstract finite-sieve error reservoir dominated by `refinedReservoir`. -/
theorem brunGoldbachResidueMainTermRefined_iff_exists_error_dominated :
    BrunGoldbachResidueMainTermRefined ↔
      ∃ B : ℕ → ℕ → ℝ,
        BrunGoldbachResidueMainTermWithError B ∧
          GoldbachResidueErrorDominatedByRefined B := by
  constructor
  · intro hMain
    refine ⟨refinedReservoir, ?_, ?_⟩
    · exact hMain
    · intro n z
      rfl
  · rintro ⟨B, hMain, hErr⟩
    exact brunGoldbachResidueMainTermRefined_of_error_dominated hMain hErr

/-- A residue main-term bound with an error reservoir bounded by a constant
multiple of `refinedReservoir` gives the corrected local main-term target
with a constant-error reservoir. -/
theorem brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residue_error_bound
    {B : ℕ → ℕ → ℝ}
    (hMain : BrunGoldbachResidueMainTermWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefined B) :
    BrunGoldbachLocalMainTermRefinedWithErrorConstant := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  rcases hErr with ⟨C_E, hCE_pos, hErrBd⟩
  refine ⟨C₁, C_E, hC₁_pos, hCE_pos, ?_⟩
  intro n z hn
  have hbd := hMainBd n z hn
  have herr := hErrBd n z
  have hfactor_eq :
      goldbachResidueMainFactor n z = goldbachLocalFactor n z :=
    goldbachResidueMainFactor_eq_goldbachLocalFactor n z
  rw [hfactor_eq] at hbd
  linarith

/-- Pointwise domination by `refinedReservoir` is a special case of bounded
domination by a constant multiple. -/
theorem goldbachResidueErrorBoundedByRefined_of_dominated
    {B : ℕ → ℕ → ℝ}
    (hErr : GoldbachResidueErrorDominatedByRefined B) :
    GoldbachResidueErrorBoundedByRefined B := by
  refine ⟨1, by norm_num, ?_⟩
  intro n z
  simpa using hErr n z

/-- The direct residue-set main-term target is exactly strong enough to feed
the corrected local-factor route. -/
theorem brunGoldbachLocalMainTermRefined_of_residueMainTerm
    (hMain : BrunGoldbachResidueMainTermRefined) :
    BrunGoldbachLocalMainTermRefined := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn
  have hbd := hMainBd n z hn
  simpa [goldbachResidueMainFactor_eq_goldbachLocalFactor n z] using hbd

/-- Conversely, any corrected local-factor main term can be rewritten in the
residue-set product language. -/
theorem brunGoldbachResidueMainTermRefined_of_localMainTerm
    (hMain : BrunGoldbachLocalMainTermRefined) :
    BrunGoldbachResidueMainTermRefined := by
  rcases hMain with ⟨C₁, hC₁_pos, hMainBd⟩
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn
  have hbd := hMainBd n z hn
  simpa [goldbachResidueMainFactor_eq_goldbachLocalFactor n z] using hbd

/-- The residue-set and corrected local-factor formulations of the refined
Goldbach main term are equivalent. -/
theorem brunGoldbachResidueMainTermRefined_iff_localMainTerm :
    BrunGoldbachResidueMainTermRefined ↔ BrunGoldbachLocalMainTermRefined :=
  ⟨brunGoldbachLocalMainTermRefined_of_residueMainTerm,
   brunGoldbachResidueMainTermRefined_of_localMainTerm⟩

/-- If `m ≤ n`, equality of the residue classes of `m` and `n` modulo `p`
is the same as `p ∣ n - m`. -/
theorem zmod_natCast_eq_natCast_iff_dvd_sub {m n p : ℕ} (hmn : m ≤ n) :
    (m : ZMod p) = (n : ZMod p) ↔ p ∣ n - m := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.modEq_iff_dvd' hmn

/-- Membership in the bad Goldbach residue set is exactly the natural
divisibility condition `p ∣ m ∨ p ∣ n - m`, provided `m ≤ n` so that the
second endpoint uses natural subtraction. -/
theorem mem_goldbachBadResidueSet_iff_dvd_or_dvd_sub
    {n p m : ℕ} (hmn : m ≤ n) :
    (m : ZMod p) ∈ goldbachBadResidueSet n p ↔ p ∣ m ∨ p ∣ (n - m) := by
  rw [mem_goldbachBadResidueSet]
  constructor
  · intro h
    rcases h with h0 | hn
    · exact Or.inl ((ZMod.natCast_eq_zero_iff m p).mp h0)
    · exact Or.inr ((zmod_natCast_eq_natCast_iff_dvd_sub hmn).mp hn)
  · intro h
    rcases h with hm | hnm
    · exact Or.inl ((ZMod.natCast_eq_zero_iff m p).mpr hm)
    · exact Or.inr ((zmod_natCast_eq_natCast_iff_dvd_sub hmn).mpr hnm)

/-- Avoiding the bad residue classes is exactly simultaneous avoidance of
the two divisibility obstructions in the paired Goldbach sieve. -/
theorem not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub
    {n p m : ℕ} (hmn : m ≤ n) :
    (m : ZMod p) ∉ goldbachBadResidueSet n p ↔ ¬ p ∣ m ∧ ¬ p ∣ (n - m) := by
  rw [mem_goldbachBadResidueSet_iff_dvd_or_dvd_sub hmn]
  exact not_or

/-! ## Residue-sifted count

The finite upper-bound sieve naturally counts values `m` avoiding the bad
residue set modulo each odd prime.  The existing project-level
`goldbachSiftedPair` also sifts by `p = 2`; hence it is contained in this
odd-prime residue-sifted set.  Bounding the residue-sifted count is therefore
enough for the corrected Goldbach main term.
-/

/-- Values `m ∈ [1, n - 1]` avoiding the Goldbach bad residue set modulo
every odd prime `p ≤ z`. -/
noncomputable def goldbachResidueSiftedSet (n z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (n - 1)).filter
    (fun m => ∀ p, p ∈ (Finset.Icc 3 z).filter Nat.Prime →
      (m : ZMod p) ∉ goldbachBadResidueSet n p)

/-- The odd-prime residue-sifted count. -/
noncomputable def goldbachResidueSiftedCount (n z : ℕ) : ℕ :=
  (goldbachResidueSiftedSet n z).card

@[simp] theorem mem_goldbachResidueSiftedSet {n z m : ℕ} :
    m ∈ goldbachResidueSiftedSet n z ↔
      (1 ≤ m ∧ m ≤ n - 1) ∧
        ∀ p, p ∈ (Finset.Icc 3 z).filter Nat.Prime →
          (m : ZMod p) ∉ goldbachBadResidueSet n p := by
  classical
  simp [goldbachResidueSiftedSet, Finset.mem_Icc, and_assoc]

/-- The residue-sifted set is contained in `[1, n - 1]`. -/
theorem goldbachResidueSiftedSet_subset_Icc (n z : ℕ) :
    goldbachResidueSiftedSet n z ⊆ Finset.Icc 1 (n - 1) := by
  intro m hm
  rw [mem_goldbachResidueSiftedSet] at hm
  exact Finset.mem_Icc.mpr hm.1

/-- Trivial cardinal bound for the residue-sifted count. -/
theorem goldbachResidueSiftedCount_le (n z : ℕ) :
    goldbachResidueSiftedCount n z ≤ n := by
  unfold goldbachResidueSiftedCount
  have hcard : (goldbachResidueSiftedSet n z).card ≤
      (Finset.Icc 1 (n - 1)).card :=
    Finset.card_le_card (goldbachResidueSiftedSet_subset_Icc n z)
  have hIcc : (Finset.Icc 1 (n - 1)).card ≤ n := by
    rw [Nat.card_Icc]
    omega
  exact hcard.trans hIcc

/-- Increasing the sieve threshold can only decrease the residue-sifted
count. -/
theorem goldbachResidueSiftedCount_anti (n : ℕ) {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    goldbachResidueSiftedCount n z₂ ≤ goldbachResidueSiftedCount n z₁ := by
  unfold goldbachResidueSiftedCount
  apply Finset.card_le_card
  intro m hm
  rw [mem_goldbachResidueSiftedSet] at hm ⊢
  refine ⟨hm.1, ?_⟩
  intro p hp
  exact hm.2 p (by
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hp_prime⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, hpz₁⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp3, hpz₁.trans hz⟩, hp_prime⟩)

/-- The project-level paired sift is contained in the odd-prime
residue-sifted set. -/
theorem goldbachSiftedPairSet_subset_residueSiftedSet (n z : ℕ) :
    goldbachSiftedPairSet n z ⊆ goldbachResidueSiftedSet n z := by
  intro m hm
  rw [mem_goldbachSiftedPairSet] at hm
  rcases hm with ⟨hmIcc, hm_not, hnm_not⟩
  rw [mem_goldbachResidueSiftedSet]
  refine ⟨hmIcc, ?_⟩
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hp_prime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨_hp3, hp_le_z⟩
  have hmn : m ≤ n := by omega
  rw [not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub hmn]
  exact ⟨hm_not p hp_le_z hp_prime, hnm_not p hp_le_z hp_prime⟩

/-- The paired sifted count is bounded by the residue-sifted count. -/
theorem goldbachSiftedPair_le_residueSiftedCount (n z : ℕ) :
    goldbachSiftedPair n z ≤ goldbachResidueSiftedCount n z := by
  unfold goldbachSiftedPair goldbachResidueSiftedCount
  exact Finset.card_le_card (goldbachSiftedPairSet_subset_residueSiftedSet n z)

/-- Finite-sieve upper bound for the odd-prime residue-sifted count with an
abstract error reservoir.  This is the most natural local target for a
Halberstam-Richert/Brun worker. -/
def BrunGoldbachResidueSiftedUpperBoundWithError (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n →
      (goldbachResidueSiftedCount n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n z + B n z

/-- The canonical refined error reservoir for the residue-sifted finite-sieve
target. -/
noncomputable def goldbachResidueRefinedError : ℕ → ℕ → ℝ :=
  refinedReservoir

/-- The canonical refined error reservoir is bounded by itself. -/
theorem goldbachResidueRefinedError_bounded :
    GoldbachResidueErrorBoundedByRefined goldbachResidueRefinedError := by
  refine ⟨1, by norm_num, ?_⟩
  intro n z
  simp [goldbachResidueRefinedError]

/-- The canonical refined error reservoir is pointwise dominated by the
refined reservoir. -/
theorem goldbachResidueRefinedError_dominated :
    GoldbachResidueErrorDominatedByRefined goldbachResidueRefinedError := by
  intro n z
  simp [goldbachResidueRefinedError]

/-- The canonical refined error reservoir is nonnegative. -/
theorem goldbachResidueRefinedError_nonneg (n z : ℕ) :
    0 ≤ goldbachResidueRefinedError n z := by
  simp [goldbachResidueRefinedError, refinedReservoir]
  positivity

/-- The remaining hard finite-sieve upper-bound field after choosing the
canonical refined error reservoir. -/
def GoldbachResidueSiftedRefinedUpperBound : Prop :=
  BrunGoldbachResidueSiftedUpperBoundWithError goldbachResidueRefinedError

/-- Large-sieve-range version of the refined-error residue-sifted target.
This is the cleaner finite-sieve worker target: the cases `z < 3` contain no
odd prime moduli and are discharged mechanically. -/
def GoldbachResidueSiftedRefinedUpperBoundForLargeZ : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n → 3 ≤ z →
      (goldbachResidueSiftedCount n z : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n z
          + goldbachResidueRefinedError n z

/-- Final-assembly version of the refined-error residue-sifted target.
Downstream Path C only evaluates the finite sieve at `z = Nat.sqrt n` and
only for all sufficiently large `n`; this is therefore the narrowest current
finite-sieve worker target. -/
def GoldbachResidueSiftedRefinedUpperBoundAtSqrt : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + goldbachResidueRefinedError n (Nat.sqrt n)

/-- Final-assembly residue-sifted target allowing a fixed constant multiple
of the refined error reservoir.  This is the narrowest practical finite-sieve
worker target: only `z = Nat.sqrt n`, only eventually in `n`, and with a
harmless absolute error constant. -/
def GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant : Prop :=
  ∃ C₁ C_E : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧ 0 < C_E ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + C_E * goldbachResidueRefinedError n (Nat.sqrt n)

/-- Final-assembly residue-sifted upper bound with an abstract error
reservoir.  Worker A can prove this finite-sieve estimate without choosing
the final Path C error reservoir. -/
def BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
    (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + B n (Nat.sqrt n)

/-- At-sqrt error domination by a fixed constant multiple of the refined
reservoir.  Worker B can prove this independently from the sieve upper-bound
worker. -/
def GoldbachResidueErrorBoundedByRefinedAtSqrt
    (B : ℕ → ℕ → ℝ) : Prop :=
  ∃ C_E : ℝ, ∃ N₀ : ℕ, 0 < C_E ∧
    ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
      B n (Nat.sqrt n) ≤ C_E * refinedReservoir n (Nat.sqrt n)

/-- The all-threshold refined-error target implies the final-assembly
`z = Nat.sqrt n` target. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_refinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrt := by
  rcases hUpper with ⟨C₁, hC₁_pos, hbd⟩
  refine ⟨C₁, 2, hC₁_pos, ?_⟩
  intro n _hn hn2
  exact hbd n (Nat.sqrt n) (by omega)

/-- The coefficient-one final-assembly residue target is a special case of
the constant-error final-assembly target. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant := by
  rcases hSift with ⟨C₁, N₀, hC₁_pos, hSiftBd⟩
  refine ⟨C₁, 1, N₀, hC₁_pos, by norm_num, ?_⟩
  intro n hn hn2
  simpa using hSiftBd n hn hn2

/-- An all-threshold abstract-error residue-sifted bound implies its
final-assembly at-sqrt version. -/
theorem brunGoldbachResidueSiftedUpperBoundAtSqrtWithError_of_all
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundWithError B) :
    BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B := by
  rcases hSift with ⟨C₁, hC₁_pos, hSiftBd⟩
  refine ⟨C₁, 2, hC₁_pos, ?_⟩
  intro n _hn hn2
  exact hSiftBd n (Nat.sqrt n) (by omega)

/-- An all-threshold fixed-constant error bound implies the corresponding
final-assembly at-sqrt error bound. -/
theorem goldbachResidueErrorBoundedByRefinedAtSqrt_of_all
    {B : ℕ → ℕ → ℝ}
    (hErr : GoldbachResidueErrorBoundedByRefined B) :
    GoldbachResidueErrorBoundedByRefinedAtSqrt B := by
  rcases hErr with ⟨C_E, hCE_pos, hErrBd⟩
  refine ⟨C_E, 2, hCE_pos, ?_⟩
  intro n _hn _hn2
  exact hErrBd n (Nat.sqrt n)

/-- At-sqrt abstract-error sieve output plus at-sqrt error domination gives
the final-assembly refined target with a fixed error constant. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B)
    (hErr : GoldbachResidueErrorBoundedByRefinedAtSqrt B) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant := by
  rcases hSift with ⟨C₁, Nsift, hC₁_pos, hSiftBd⟩
  rcases hErr with ⟨C_E, Nerr, hCE_pos, hErrBd⟩
  refine ⟨C₁, C_E, max Nsift Nerr, hC₁_pos, hCE_pos, ?_⟩
  intro n hn hn2
  have hnSift : Nsift ≤ n := (le_max_left Nsift Nerr).trans hn
  have hnErr : Nerr ≤ n := (le_max_right Nsift Nerr).trans hn
  have hbd := hSiftBd n hnSift hn2
  have herr :
      B n (Nat.sqrt n) ≤ C_E * goldbachResidueRefinedError n (Nat.sqrt n) := by
    simpa [goldbachResidueRefinedError] using hErrBd n hnErr hn2
  linarith

/-- The large-sieve-range finite-sieve target implies the all-threshold
target; small `z` is handled by the empty residue product and
`goldbachResidueSiftedCount_le`. -/
theorem goldbachResidueSiftedRefinedUpperBound_of_forLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    GoldbachResidueSiftedRefinedUpperBound := by
  rcases hLarge with ⟨C₁, hC₁_pos, hLargeBd⟩
  refine ⟨max C₁ 1, lt_of_lt_of_le zero_lt_one (le_max_right C₁ 1), ?_⟩
  intro n z hn
  by_cases hz : 3 ≤ z
  · have hbd := hLargeBd n z hn hz
    have hC_le : C₁ ≤ max C₁ 1 := le_max_left C₁ 1
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hfactor_nonneg : 0 ≤ goldbachResidueMainFactor n z :=
      goldbachResidueMainFactor_nonneg n z
    have hmul_n :
        C₁ * (n : ℝ) ≤ max C₁ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hC_le hn_nonneg
    have hmain_le :
        C₁ * (n : ℝ) * goldbachResidueMainFactor n z ≤
          max C₁ 1 * (n : ℝ) * goldbachResidueMainFactor n z :=
      mul_le_mul_of_nonneg_right hmul_n hfactor_nonneg
    linarith
  · have hzlt : z < 3 := Nat.lt_of_not_ge hz
    have hcount : (goldbachResidueSiftedCount n z : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast goldbachResidueSiftedCount_le n z
    have hfactor : goldbachResidueMainFactor n z = 1 :=
      goldbachResidueMainFactor_eq_one_of_lt_three n hzlt
    have hC_ge_one : (1 : ℝ) ≤ max C₁ 1 := le_max_right C₁ 1
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hn_le_main :
        (n : ℝ) ≤ max C₁ 1 * (n : ℝ) * goldbachResidueMainFactor n z := by
      rw [hfactor]
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right hC_ge_one hn_nonneg)
    have herr_nonneg : 0 ≤ goldbachResidueRefinedError n z :=
      goldbachResidueRefinedError_nonneg n z
    linarith

/-- The large-sieve-range target also implies the final-assembly target once
the finite tail before `Nat.sqrt n ≥ 3` is absorbed into the all-threshold
closure. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_forLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrt :=
  goldbachResidueSiftedRefinedUpperBoundAtSqrt_of_refinedUpperBound
    (goldbachResidueSiftedRefinedUpperBound_of_forLargeZ hLarge)

/-- Data bundle for a finite-sieve upper bound on the odd-prime
residue-sifted count.  Worker A owns the `upperBound` field. -/
structure GoldbachResidueSiftedUpperData where
  B : ℕ → ℕ → ℝ
  upperBound : BrunGoldbachResidueSiftedUpperBoundWithError B

/-- Data bundle for the finite-sieve upper bound plus a usable error estimate.
Worker A owns `upperBound`; Worker B owns `errorBound`. -/
structure GoldbachResidueSiftedBoundedErrorData where
  B : ℕ → ℕ → ℝ
  upperBound : BrunGoldbachResidueSiftedUpperBoundWithError B
  errorBound : GoldbachResidueErrorBoundedByRefined B

/-- Data bundle for the final-assembly at-sqrt finite-sieve upper bound plus
the corresponding at-sqrt error domination.  This is the most parallel
worker-friendly finite-sieve interface. -/
structure GoldbachResidueSiftedAtSqrtBoundedErrorData where
  B : ℕ → ℕ → ℝ
  upperBound : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B
  errorBound : GoldbachResidueErrorBoundedByRefinedAtSqrt B

/-- A proof of the refined-error residue-sifted upper bound packages into the
bounded-error data bundle with the error-bound field already closed. -/
noncomputable def goldbachResidueSiftedBoundedErrorData_of_refinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    GoldbachResidueSiftedBoundedErrorData where
  B := goldbachResidueRefinedError
  upperBound := hUpper
  errorBound := goldbachResidueRefinedError_bounded

/-- A proof of the large-sieve-range refined-error target packages into the
bounded-error data bundle after the small-threshold cases are closed
mechanically. -/
noncomputable def goldbachResidueSiftedBoundedErrorData_of_forLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    GoldbachResidueSiftedBoundedErrorData :=
  goldbachResidueSiftedBoundedErrorData_of_refinedUpperBound
    (goldbachResidueSiftedRefinedUpperBound_of_forLargeZ hLarge)

/-- An all-threshold bounded-error data bundle gives the final-assembly
at-sqrt bounded-error data bundle. -/
noncomputable def goldbachResidueSiftedAtSqrtBoundedErrorData_of_boundedErrorData
    (data : GoldbachResidueSiftedBoundedErrorData) :
    GoldbachResidueSiftedAtSqrtBoundedErrorData where
  B := data.B
  upperBound :=
    brunGoldbachResidueSiftedUpperBoundAtSqrtWithError_of_all data.upperBound
  errorBound :=
    goldbachResidueErrorBoundedByRefinedAtSqrt_of_all data.errorBound

/-- Forget the error estimate from a bounded-error finite-sieve data bundle. -/
def GoldbachResidueSiftedBoundedErrorData.toUpperData
    (data : GoldbachResidueSiftedBoundedErrorData) :
    GoldbachResidueSiftedUpperData where
  B := data.B
  upperBound := data.upperBound

/-- A finite-sieve upper-data bundle gives the corresponding upper-bound
Prop. -/
theorem brunGoldbachResidueSiftedUpperBoundWithError_of_data
    (data : GoldbachResidueSiftedUpperData) :
    BrunGoldbachResidueSiftedUpperBoundWithError data.B :=
  data.upperBound

/-- An at-sqrt bounded-error data bundle closes the final-assembly refined
target with a fixed error constant. -/
theorem goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrtBoundedErrorData
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData) :
    GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant :=
  goldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant_of_atSqrt_error_bound
    data.upperBound data.errorBound

/-- Crude sanity witness for the residue-sifted upper-bound interface:
with the worst-case error reservoir `B(n,z) = n`, the bound is immediate
from the trivial cardinal estimate.  The hard analytic work is replacing
this crude error by one bounded by a constant multiple of `refinedReservoir`. -/
theorem brunGoldbachResidueSiftedUpperBoundWithError_trivial :
    BrunGoldbachResidueSiftedUpperBoundWithError (fun n _ => (n : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro n z _hn
  have hcount : (goldbachResidueSiftedCount n z : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n z
  have hfactor_nonneg : 0 ≤ goldbachResidueMainFactor n z :=
    goldbachResidueMainFactor_nonneg n z
  have hmain_nonneg : 0 ≤ 1 * (n : ℝ) * goldbachResidueMainFactor n z := by
    positivity
  linarith

/-- A residue-sifted upper bound immediately gives the paired-sift main-term
bound with the same error reservoir. -/
theorem brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound
    {B : ℕ → ℕ → ℝ}
    (hSift : BrunGoldbachResidueSiftedUpperBoundWithError B) :
    BrunGoldbachResidueMainTermWithError B := by
  rcases hSift with ⟨C₁, hC₁_pos, hSiftBd⟩
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn
  have hle : (goldbachSiftedPair n z : ℝ) ≤
      (goldbachResidueSiftedCount n z : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le_residueSiftedCount n z
  have hbd := hSiftBd n z hn
  linarith

/-- The canonical refined-error residue-sifted target directly gives the
refined residue main-term target. -/
theorem brunGoldbachResidueMainTermRefined_of_residueSiftedRefinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    BrunGoldbachResidueMainTermRefined :=
  brunGoldbachResidueMainTermRefined_of_error_dominated
    (brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound hUpper)
    goldbachResidueRefinedError_dominated

/-- The large-sieve-range refined-error residue-sifted target directly gives
the refined residue main-term target. -/
theorem brunGoldbachResidueMainTermRefined_of_residueSiftedRefinedUpperBoundForLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    BrunGoldbachResidueMainTermRefined :=
  brunGoldbachResidueMainTermRefined_of_residueSiftedRefinedUpperBound
    (goldbachResidueSiftedRefinedUpperBound_of_forLargeZ hLarge)

/-- The canonical refined-error residue-sifted target directly gives the
corrected local-factor refined main-term target. -/
theorem brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    BrunGoldbachLocalMainTermRefined :=
  brunGoldbachLocalMainTermRefined_of_residueMainTerm
    (brunGoldbachResidueMainTermRefined_of_residueSiftedRefinedUpperBound hUpper)

/-- The large-sieve-range refined-error residue-sifted target directly gives
the corrected local-factor refined main-term target. -/
theorem brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBoundForLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    BrunGoldbachLocalMainTermRefined :=
  brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBound
    (goldbachResidueSiftedRefinedUpperBound_of_forLargeZ hLarge)

/-- The final-assembly residue-sifted target directly gives the final-assembly
paired local-factor target. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrt_of_residueSiftedRefinedUpperBoundAtSqrt
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt) :
    BrunGoldbachLocalMainTermRefinedAtSqrt := by
  rcases hSift with ⟨C₁, N₀, hC₁_pos, hSiftBd⟩
  refine ⟨C₁, N₀, hC₁_pos, ?_⟩
  intro n hn hn2
  have hpair_le :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤
        (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le_residueSiftedCount n (Nat.sqrt n)
  have hres := hSiftBd n hn hn2
  have hfactor_eq :
      goldbachResidueMainFactor n (Nat.sqrt n) =
        goldbachLocalFactor n (Nat.sqrt n) :=
    goldbachResidueMainFactor_eq_goldbachLocalFactor n (Nat.sqrt n)
  have herr_eq :
      goldbachResidueRefinedError n (Nat.sqrt n) =
        refinedReservoir n (Nat.sqrt n) := by
    simp [goldbachResidueRefinedError]
  have hres_local :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤
        C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) +
          refinedReservoir n (Nat.sqrt n) := by
    simpa [hfactor_eq, herr_eq] using hres
  exact hpair_le.trans hres_local

/-- The final-assembly residue-sifted constant-error target directly gives
the final-assembly paired local-factor constant-error target. -/
theorem brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant) :
    BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant := by
  rcases hSift with ⟨C₁, C_E, N₀, hC₁_pos, hCE_pos, hSiftBd⟩
  refine ⟨C₁, C_E, N₀, hC₁_pos, hCE_pos, ?_⟩
  intro n hn hn2
  have hpair_le :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤
        (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le_residueSiftedCount n (Nat.sqrt n)
  have hres := hSiftBd n hn hn2
  have hfactor_eq :
      goldbachResidueMainFactor n (Nat.sqrt n) =
        goldbachLocalFactor n (Nat.sqrt n) :=
    goldbachResidueMainFactor_eq_goldbachLocalFactor n (Nat.sqrt n)
  have hres_local :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤
        C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) +
          C_E * refinedReservoir n (Nat.sqrt n) := by
    simpa [hfactor_eq, goldbachResidueRefinedError] using hres
  exact hpair_le.trans hres_local

/-- A bounded-error finite-sieve data bundle gives the paired-sift main-term
bound with the same error reservoir. -/
theorem brunGoldbachResidueMainTermWithError_of_boundedErrorData
    (data : GoldbachResidueSiftedBoundedErrorData) :
    BrunGoldbachResidueMainTermWithError data.B :=
  brunGoldbachResidueMainTermWithError_of_residueSiftedUpperBound
    data.upperBound

/-- A bounded-error finite-sieve data bundle gives the constant-error local
main-term target consumed by the local-to-singular connector. -/
theorem brunGoldbachLocalMainTermRefinedWithErrorConstant_of_boundedErrorData
    (data : GoldbachResidueSiftedBoundedErrorData) :
    BrunGoldbachLocalMainTermRefinedWithErrorConstant :=
  brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residue_error_bound
    (brunGoldbachResidueMainTermWithError_of_boundedErrorData data)
    data.errorBound

/-- The canonical refined-error residue-sifted target also feeds the
constant-error local main-term interface used by the local-to-singular
connector. -/
theorem brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    BrunGoldbachLocalMainTermRefinedWithErrorConstant :=
  brunGoldbachLocalMainTermRefinedWithErrorConstant_of_boundedErrorData
    (goldbachResidueSiftedBoundedErrorData_of_refinedUpperBound hUpper)

/-- The large-sieve-range refined-error residue-sifted target also feeds the
constant-error local main-term interface. -/
theorem brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBoundForLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    BrunGoldbachLocalMainTermRefinedWithErrorConstant :=
  brunGoldbachLocalMainTermRefinedWithErrorConstant_of_boundedErrorData
    (goldbachResidueSiftedBoundedErrorData_of_forLargeZ hLarge)

end PathCGoldbachResidues
end Gdbh
