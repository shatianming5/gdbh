/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtSeventeenToThirtySixSplit

/-!
# Path C -- corrected residue canonical sqrt-thirty-seven-to-hundred split

Round 31 removed the block `17 ≤ Nat.sqrt n ≤ 36` from the corrected residue
canonical target.  This file removes the next block
`37 ≤ Nat.sqrt n ≤ 100`.  The proof avoids a case split at every prime by
showing that the crude factor product `∏ (1 - 2 / p)` only decreases when more
odd primes are included; the fixed product through `100` is still at least
`1 / 37`.
-/

namespace Gdbh
namespace PathCResidueCanonicalSqrtThirtySevenToHundredSplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
  (ResidueCanonicalFromSqrtThirtySevenAtSqrt
   ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtThirtySeven
   pathC_kGoldbach_of_residueCanonicalFromSqrtThirtySeven_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtThirtySeven
   residueFactorProduct_lower_two_of_three_le)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual: `37 ≤ Nat.sqrt n ≤ 100`. -/
def ResidueCanonicalSqrtThirtySevenToHundredAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 37 ≤ Nat.sqrt n → Nat.sqrt n ≤ 100 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`37 ≤ sqrt n ≤ 100`. -/
def ResidueCanonicalFromSqrtHundredOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 101 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 101` residual. -/
def ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtHundredOneAtSqrt C₁

/-! ## Crude product lower bounds -/

/-- Crude lower factor obtained from the bad-residue-cardinality bound. -/
noncomputable def crudeResidueFactor (p : ℕ) : ℝ :=
  1 - (2 : ℝ) / (p : ℝ)

/-- The crude factor is nonnegative for odd-prime-range values. -/
theorem crudeResidueFactor_nonneg_of_three_le {p : ℕ} (hp3 : 3 ≤ p) :
    0 ≤ crudeResidueFactor p := by
  unfold crudeResidueFactor
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hp3)
  have htwo_le : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hp3)
  have hdiv_le_one : (2 : ℝ) / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp_pos]
    exact htwo_le
  linarith

/-- The crude factor is at most one. -/
theorem crudeResidueFactor_le_one (p : ℕ) :
    crudeResidueFactor p ≤ 1 := by
  unfold crudeResidueFactor
  have hdiv_nonneg : 0 ≤ (2 : ℝ) / (p : ℝ) := by positivity
  linarith

/-- Adding more factors in `[0, 1]` can only decrease the crude product. -/
theorem crudeResidueFactorProduct_antitone_of_subset
    {s t : Finset ℕ} (hst : s ⊆ t) (h3t : ∀ p ∈ t, 3 ≤ p) :
    (∏ p ∈ t, crudeResidueFactor p) ≤
      ∏ p ∈ s, crudeResidueFactor p := by
  classical
  have hsdiff_le_one :
      (∏ p ∈ t \ s, crudeResidueFactor p) ≤ (1 : ℝ) := by
    have hprod := Finset.prod_le_prod
      (s := t \ s) (f := crudeResidueFactor) (g := fun _ => (1 : ℝ))
      (fun p hp => by
        exact crudeResidueFactor_nonneg_of_three_le
          (h3t p ((Finset.mem_sdiff.mp hp).1)))
      (fun p _hp => crudeResidueFactor_le_one p)
    simpa using hprod
  have hs_nonneg : 0 ≤ ∏ p ∈ s, crudeResidueFactor p := by
    exact Finset.prod_nonneg (fun p hp =>
      crudeResidueFactor_nonneg_of_three_le (h3t p (hst hp)))
  have hdecomp := Finset.prod_sdiff hst (f := crudeResidueFactor)
  calc
    (∏ p ∈ t, crudeResidueFactor p)
        = (∏ p ∈ t \ s, crudeResidueFactor p) *
            ∏ p ∈ s, crudeResidueFactor p := by
          exact hdecomp.symm
    _ ≤ 1 * ∏ p ∈ s, crudeResidueFactor p := by
          exact mul_le_mul_of_nonneg_right hsdiff_le_one hs_nonneg
    _ = ∏ p ∈ s, crudeResidueFactor p := by ring

/-- Explicit odd-prime set through `100`. -/
theorem prime_filter_three_to_hundred :
    (Finset.Icc 3 100).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97} : Finset ℕ) := by
  decide

/-- The fixed crude product through `100` is still at least `1 / 37`. -/
theorem one_thirty_seventh_le_crudeResidueFactorProduct_to_hundred :
    (1 / 37 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 100).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_hundred]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 100`, the odd-prime residue main factor is at least
`1 / 37`. -/
theorem one_thirty_seventh_le_goldbachResidueMainFactor_of_le_hundred
    (n z : ℕ) (hz100 : z ≤ 100) :
    (1 / 37 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let Phundred : Finset ℕ := (Finset.Icc 3 100).filter Nat.Prime
  have hsubset : Pz ⊆ Phundred := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz100⟩, hp'.2⟩
  have h3_hundred : ∀ p ∈ Phundred, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ Phundred, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_hundred
  have hcrude_z :
      (1 / 37 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_thirty_seventh_le_crudeResidueFactorProduct_to_hundred.trans hanti
  have hactual :
      (∏ p ∈ Pz, crudeResidueFactor p) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
    simpa [crudeResidueFactor] using
      residueFactorProduct_lower_two_of_three_le n Pz h3_z
  have hmain :
      (1 / 37 : ℝ) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
    hcrude_z.trans hactual
  simpa [goldbachResidueMainFactor, Pz] using hmain

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `37 ≤ Nat.sqrt n ≤ 100` of the corrected residual is
closed with coefficient `37`, by the trivial count bound and the `1 / 37`
local-factor lower bound. -/
theorem residueCanonicalSqrtThirtySevenToHundredAtSqrt_thirty_seven :
    ResidueCanonicalSqrtThirtySevenToHundredAtSqrt 37 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_thirty_seven hsqrt_le_hundred
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_thirty_seventh :
      (1 / 37 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_thirty_seventh_le_goldbachResidueMainFactor_of_le_hundred
      n (Nat.sqrt n) hsqrt_le_hundred
  have hfactor_scaled :
      (1 : ℝ) ≤ 37 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (37 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (37 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (37 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `37 ≤ sqrt n ≤ 100` block and a `sqrt n ≥ 101` residual combine
into the Round 31 residual `sqrt n ≥ 37`. -/
theorem residueCanonicalFromSqrtThirtySevenAtSqrt_of_sqrtThirtySevenToHundred_and_fromSqrtHundredOne
    {Cblock C101 : ℝ}
    (hBlock : ResidueCanonicalSqrtThirtySevenToHundredAtSqrt Cblock)
    (hHundredOne : ResidueCanonicalFromSqrtHundredOneAtSqrt C101) :
    ResidueCanonicalFromSqrtThirtySevenAtSqrt (max Cblock C101) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hHundredOne with ⟨_hC101_pos, hHundredOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C101), ?_⟩
  intro n hn hsqrt_ge_thirty_seven
  by_cases hsqrt_le_hundred : Nat.sqrt n ≤ 100
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C101)
      (hBlockBd n hn hsqrt_ge_thirty_seven hsqrt_le_hundred)
  · have hsqrt_ge_hundred_one : 101 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C101)
      (hHundredOneBd n hn hsqrt_ge_hundred_one)

/-- The only remaining finite-sieve worker target after the closed
`37 ≤ sqrt n ≤ 100` block is the `sqrt n ≥ 101` residual. -/
theorem residueCanonicalFromSqrtThirtySevenWithConstant_of_fromSqrtHundredOne
    (hHundredOne : ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtThirtySevenAtSqrtWithConstant := by
  rcases hHundredOne with ⟨C101, hHundredOne⟩
  exact ⟨max 37 C101,
    residueCanonicalFromSqrtThirtySevenAtSqrt_of_sqrtThirtySevenToHundred_and_fromSqrtHundredOne
      residueCanonicalSqrtThirtySevenToHundredAtSqrt_thirty_seven hHundredOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtHundredOne
    (hHundredOne : ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtThirtySeven
    (residueCanonicalFromSqrtThirtySevenWithConstant_of_fromSqrtHundredOne
      hHundredOne)

/-- `sqrt n ≥ 101` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtHundredOne
    (hHundredOne : ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtThirtySeven
    (residueCanonicalFromSqrtThirtySevenWithConstant_of_fromSqrtHundredOne
      hHundredOne)

/-- Final Path C adapter after the closed `37 ≤ sqrt n ≤ 100` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 101` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtHundredOne_and_countingInput
    (hHundredOne : ResidueCanonicalFromSqrtHundredOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtThirtySeven_and_countingInput
    (residueCanonicalFromSqrtThirtySevenWithConstant_of_fromSqrtHundredOne
      hHundredOne)
    hCounting

end PathCResidueCanonicalSqrtThirtySevenToHundredSplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.crudeResidueFactorProduct_antitone_of_subset
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.one_thirty_seventh_le_goldbachResidueMainFactor_of_le_hundred
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.residueCanonicalSqrtThirtySevenToHundredAtSqrt_thirty_seven
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.residueCanonicalFromSqrtThirtySevenAtSqrt_of_sqrtThirtySevenToHundred_and_fromSqrtHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.residueCanonicalFromSqrtThirtySevenWithConstant_of_fromSqrtHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.residueCanonicalWithConstant_of_fromSqrtHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.finiteSieveInput_of_residueCanonicalFromSqrtHundredOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit.pathC_kGoldbach_of_residueCanonicalFromSqrtHundredOne_and_countingInput
