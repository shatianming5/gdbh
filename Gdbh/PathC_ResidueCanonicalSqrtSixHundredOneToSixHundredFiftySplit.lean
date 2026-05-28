/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalSqrtFiveHundredOneToSixHundredSplit

/-!
# Path C -- corrected residue canonical sqrt-six-hundred-one-to-six-hundred-fifty split

Round 35 removed the block `501 ≤ Nat.sqrt n ≤ 600` from the corrected residue
canonical target.  This file removes the next stable block
`601 ≤ Nat.sqrt n ≤ 650`, keeping the coefficient `101` and advancing the
large-range worker residual to `651 ≤ Nat.sqrt n`.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueMainFactor goldbachResidueSiftedCount
   goldbachResidueSiftedCount_le)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueCanonicalSqrtSplit
  (ResidueCanonicalAtSqrtInequality
   residueCanonicalAtSqrtInequality_mono)
open Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
  (residueFactorProduct_lower_two_of_three_le)
open Gdbh.PathCResidueCanonicalSqrtThirtySevenToHundredSplit
  (crudeResidueFactor crudeResidueFactorProduct_antitone_of_subset)
open Gdbh.PathCResidueCanonicalSqrtFiveHundredOneToSixHundredSplit
  (ResidueCanonicalFromSqrtSixHundredOneAtSqrt
   ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant
   finiteSieveInput_of_residueCanonicalFromSqrtSixHundredOne
   pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredOne_and_countingInput
   residueCanonicalWithConstant_of_fromSqrtSixHundredOne)
open Gdbh.PathCResidueCanonicalCorrectedRoute
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Named split targets -/

/-- Closed finite block of the corrected residual:
`601 ≤ Nat.sqrt n ≤ 650`. -/
def ResidueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 601 ≤ Nat.sqrt n → Nat.sqrt n ≤ 650 →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Remaining large-range corrected residual after removing the block
`601 ≤ sqrt n ≤ 650`. -/
def ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrt (C₁ : ℝ) : Prop :=
  0 < C₁ ∧
    ∀ n : ℕ, 16 ≤ n → 651 ≤ Nat.sqrt n →
      ResidueCanonicalAtSqrtInequality C₁ n

/-- Existential wrapper for the `sqrt n ≥ 651` residual. -/
def ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant : Prop :=
  ∃ C₁ : ℝ, ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrt C₁

/-! ## Crude product lower bound through 650 -/

/-- Explicit odd-prime set through `650`. -/
theorem prime_filter_three_to_six_hundred_fifty :
    (Finset.Icc 3 650).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
        227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
        307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569,
        571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647} :
        Finset ℕ) := by
  decide

/-- The fixed crude product through `650` is still at least `1 / 101`. -/
theorem one_over_one_hundred_one_le_crudeResidueFactorProduct_to_six_hundred_fifty :
    (1 / 101 : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 650).filter Nat.Prime,
        crudeResidueFactor p := by
  rw [prime_filter_three_to_six_hundred_fifty]
  norm_num [crudeResidueFactor]

/-- For every `z ≤ 650`, the odd-prime residue main factor is at least
`1 / 101`. -/
theorem one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred_fifty
    (n z : ℕ) (hz650 : z ≤ 650) :
    (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  let P650 : Finset ℕ := (Finset.Icc 3 650).filter Nat.Prime
  have hsubset : Pz ⊆ P650 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp'.1).1,
        le_trans (Finset.mem_Icc.mp hp'.1).2 hz650⟩, hp'.2⟩
  have h3_650 : ∀ p ∈ P650, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have h3_z : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hanti :
      (∏ p ∈ P650, crudeResidueFactor p) ≤
        ∏ p ∈ Pz, crudeResidueFactor p :=
    crudeResidueFactorProduct_antitone_of_subset hsubset h3_650
  have hcrude_z :
      (1 / 101 : ℝ) ≤ ∏ p ∈ Pz, crudeResidueFactor p :=
    one_over_one_hundred_one_le_crudeResidueFactorProduct_to_six_hundred_fifty.trans
      hanti
  have hactual :
      (∏ p ∈ Pz, crudeResidueFactor p) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) := by
    simpa [crudeResidueFactor] using
      residueFactorProduct_lower_two_of_three_le n Pz h3_z
  have hmain :
      (1 / 101 : ℝ) ≤
        ∏ p ∈ Pz,
          (1 - ((goldbachBadResidueSet n p).card : ℝ) / (p : ℝ)) :=
    hcrude_z.trans hactual
  simpa [goldbachResidueMainFactor, Pz] using hmain

/-! ## Closed block and bridge to the large residual -/

/-- The whole block `601 ≤ Nat.sqrt n ≤ 650` of the corrected residual is
closed with coefficient `101`, by the trivial count bound and the `1 / 101`
local-factor lower bound. -/
theorem residueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt_one_hundred_one :
    ResidueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt 101 := by
  refine ⟨by norm_num, ?_⟩
  intro n _hn _hsqrt_ge_six_hundred_one hsqrt_le_six_hundred_fifty
  dsimp [ResidueCanonicalAtSqrtInequality]
  have hcount :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachResidueSiftedCount_le n (Nat.sqrt n)
  have hfactor_one_hundred_first :
      (1 / 101 : ℝ) ≤ goldbachResidueMainFactor n (Nat.sqrt n) :=
    one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred_fifty
      n (Nat.sqrt n) hsqrt_le_six_hundred_fifty
  have hfactor_scaled :
      (1 : ℝ) ≤ 101 * goldbachResidueMainFactor n (Nat.sqrt n) := by
    nlinarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn_le_main :
      (n : ℝ) ≤
        (101 : ℝ) * (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor_scaled hn_nonneg
    calc
      (n : ℝ) ≤
          (101 * goldbachResidueMainFactor n (Nat.sqrt n)) * (n : ℝ) := by
            simpa using hmul
      _ = (101 : ℝ) * (n : ℝ) *
          goldbachResidueMainFactor n (Nat.sqrt n) := by
            ring
  have htail_nonneg :
      0 ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n) := by
    unfold residueBonferroniTailAtSqrt
    positivity
  exact hcount.trans (hn_le_main.trans (le_add_of_nonneg_right htail_nonneg))

/-- A closed `601 ≤ sqrt n ≤ 650` block and a `sqrt n ≥ 651` residual combine
into the Round 35 residual `sqrt n ≥ 601`. -/
theorem residueCanonicalFromSqrtSixHundredOneAtSqrt_of_sqrtSixHundredOneToSixHundredFifty_and_fromSqrtSixHundredFiftyOne
    {Cblock C651 : ℝ}
    (hBlock : ResidueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt Cblock)
    (hSixHundredFiftyOne : ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrt C651) :
    ResidueCanonicalFromSqrtSixHundredOneAtSqrt (max Cblock C651) := by
  rcases hBlock with ⟨hCblock_pos, hBlockBd⟩
  rcases hSixHundredFiftyOne with ⟨_hC651_pos, hSixHundredFiftyOneBd⟩
  refine ⟨lt_of_lt_of_le hCblock_pos (le_max_left Cblock C651), ?_⟩
  intro n hn hsqrt_ge_six_hundred_one
  by_cases hsqrt_le_six_hundred_fifty : Nat.sqrt n ≤ 650
  · exact residueCanonicalAtSqrtInequality_mono
      (le_max_left Cblock C651)
      (hBlockBd n hn hsqrt_ge_six_hundred_one hsqrt_le_six_hundred_fifty)
  · have hsqrt_ge_six_hundred_fifty_one : 651 ≤ Nat.sqrt n := by omega
    exact residueCanonicalAtSqrtInequality_mono
      (le_max_right Cblock C651)
      (hSixHundredFiftyOneBd n hn hsqrt_ge_six_hundred_fifty_one)

/-- The only remaining finite-sieve worker target after the closed
`601 ≤ sqrt n ≤ 650` block is the `sqrt n ≥ 651` residual. -/
theorem residueCanonicalFromSqrtSixHundredOneWithConstant_of_fromSqrtSixHundredFiftyOne
    (hSixHundredFiftyOne : ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant) :
    ResidueCanonicalFromSqrtSixHundredOneAtSqrtWithConstant := by
  rcases hSixHundredFiftyOne with ⟨C651, hSixHundredFiftyOne⟩
  exact ⟨max 101 C651,
    residueCanonicalFromSqrtSixHundredOneAtSqrt_of_sqrtSixHundredOneToSixHundredFifty_and_fromSqrtSixHundredFiftyOne
      residueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt_one_hundred_one
      hSixHundredFiftyOne⟩

/-- Large-range residual bridge all the way back to the corrected canonical
target with a constant. -/
theorem residueCanonicalWithConstant_of_fromSqrtSixHundredFiftyOne
    (hSixHundredFiftyOne : ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernelWithConstant :=
  residueCanonicalWithConstant_of_fromSqrtSixHundredOne
    (residueCanonicalFromSqrtSixHundredOneWithConstant_of_fromSqrtSixHundredFiftyOne
      hSixHundredFiftyOne)

/-- `sqrt n ≥ 651` residual bridge to the supported finite-sieve input. -/
theorem finiteSieveInput_of_residueCanonicalFromSqrtSixHundredFiftyOne
    (hSixHundredFiftyOne : ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant) :
    PathCFiniteSieveInput :=
  finiteSieveInput_of_residueCanonicalFromSqrtSixHundredOne
    (residueCanonicalFromSqrtSixHundredOneWithConstant_of_fromSqrtSixHundredFiftyOne
      hSixHundredFiftyOne)

/-- Final Path C adapter after the closed `601 ≤ sqrt n ≤ 650` block: the
finite-sieve worker only has to prove the `sqrt n ≥ 651` residual. -/
theorem pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredFiftyOne_and_countingInput
    (hSixHundredFiftyOne : ResidueCanonicalFromSqrtSixHundredFiftyOneAtSqrtWithConstant)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredOne_and_countingInput
    (residueCanonicalFromSqrtSixHundredOneWithConstant_of_fromSqrtSixHundredFiftyOne
      hSixHundredFiftyOne)
    hCounting

end PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit
end Gdbh

#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.one_over_one_hundred_one_le_goldbachResidueMainFactor_of_le_six_hundred_fifty
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.residueCanonicalSqrtSixHundredOneToSixHundredFiftyAtSqrt_one_hundred_one
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.residueCanonicalFromSqrtSixHundredOneAtSqrt_of_sqrtSixHundredOneToSixHundredFifty_and_fromSqrtSixHundredFiftyOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.residueCanonicalFromSqrtSixHundredOneWithConstant_of_fromSqrtSixHundredFiftyOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.residueCanonicalWithConstant_of_fromSqrtSixHundredFiftyOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.finiteSieveInput_of_residueCanonicalFromSqrtSixHundredFiftyOne
#print axioms
  Gdbh.PathCResidueCanonicalSqrtSixHundredOneToSixHundredFiftySplit.pathC_kGoldbach_of_residueCanonicalFromSqrtSixHundredFiftyOne_and_countingInput
