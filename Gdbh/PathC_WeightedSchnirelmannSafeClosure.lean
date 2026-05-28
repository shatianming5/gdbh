/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex Round 1 controller
-/
import Gdbh.PathC_UnconditionalFixAStrong
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_FixAStrongReservoir

/-!
# Path C — weighted Schnirelmann bridge, compile-clean residual split

This file is an additive, compile-clean decomposition of
`WeightedSchnirelmannResidualBridge`.

It does not close the bridge unconditionally.  It exposes the two smaller
pieces needed to turn a FixA' universal witness into the original refined
main-term witness:

* absorb `refinedReservoirCorrectedStrong` into the paired main term plus
  the original `refinedReservoir`;
* handle the finite range below the FixA'/absorption thresholds.
-/

namespace Gdbh
namespace PathCWeightedSchnirelmannSafeClosure

open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCBrunRefinedComposition
  (BrunGoldbachPairedMainTermRefined refinedReservoir)
open Gdbh.PathCPairedMainTermAssembly
  (PairedMainTermAbsorption brunGoldbachPairedMainTermRefined_of_absorption)
open Gdbh.PathCFixAStrongReservoir
  (BrunGoldbachPairedMainTermRefinedFixAStrong refinedReservoirCorrectedStrong)
open Gdbh.PathCUnconditionalFixAStrong (WeightedSchnirelmannResidualBridge)

/-! ## Smaller residual Props -/

/-- The large-`n` analytic residual: the FixA' reservoir is absorbed into
the paired Brun main term plus the original refined reservoir. -/
def FixAStrongReservoirAbsorption : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N₁ : ℕ,
    ∀ n z : ℕ, N₁ ≤ n →
      refinedReservoirCorrectedStrong n z
        ≤ K * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z

/-- The finite-range residual at a prescribed threshold.  This isolates the
bounded `n < N_F` work from the asymptotic reservoir absorption. -/
def FixAStrongFiniteRangeAbsorptionAligned (N_F : ℕ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
    ∀ n z : ℕ, 0 < n → n < N_F →
      (goldbachSiftedPair n z : ℝ)
        ≤ C' * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z

private lemma main_term_le_of_const_le
    {C C' : ℝ} (hCC' : C ≤ C') (n z : ℕ) :
    C * (n : ℝ) * pairedBrunFactor z
      ≤ C' * (n : ℝ) * pairedBrunFactor z := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  have hnp : 0 ≤ (n : ℝ) * pairedBrunFactor z := mul_nonneg hn hp
  have h := mul_le_mul_of_nonneg_right hCC' hnp
  calc
    C * (n : ℝ) * pairedBrunFactor z
        = C * ((n : ℝ) * pairedBrunFactor z) := by ring
    _ ≤ C' * ((n : ℝ) * pairedBrunFactor z) := h
    _ = C' * (n : ℝ) * pairedBrunFactor z := by ring

/-! ## Bridges -/

/-- A direct refined witness trivially gives the weighted bridge. -/
theorem weightedSchnirelmannResidualBridge_of_refined
    (h : BrunGoldbachPairedMainTermRefined) :
    WeightedSchnirelmannResidualBridge := by
  intro _hFixAStrong
  exact h

/-- The absorption half of the refined witness trivially gives the bridge. -/
theorem weightedSchnirelmannResidualBridge_of_absorption
    (h : PairedMainTermAbsorption) :
    WeightedSchnirelmannResidualBridge := by
  intro _hFixAStrong
  exact brunGoldbachPairedMainTermRefined_of_absorption h

/-- FixA' plus the two smaller residuals yields `PairedMainTermAbsorption`. -/
theorem pairedMainTermAbsorption_of_fixAStrong_and_residuals
    (hFixAStrong : BrunGoldbachPairedMainTermRefinedFixAStrong)
    (hReservoir : FixAStrongReservoirAbsorption)
    (hFinite : ∀ N_F : ℕ, FixAStrongFiniteRangeAbsorptionAligned N_F) :
    PairedMainTermAbsorption := by
  obtain ⟨C, hC_pos, N₀, hFixBd⟩ := hFixAStrong
  obtain ⟨K, hK_pos, N₁, hReservoirBd⟩ := hReservoir
  let N_F : ℕ := max N₀ N₁
  obtain ⟨Cfin, hCfin_pos, hFiniteBd⟩ := hFinite N_F
  let CTot : ℝ := max (C + K) Cfin
  have hCK_pos : 0 < C + K := add_pos hC_pos hK_pos
  have hCTot_pos : 0 < CTot :=
    lt_of_lt_of_le hCK_pos (le_max_left _ _)
  refine ⟨CTot, hCTot_pos, ?_⟩
  intro n z hn_pos
  by_cases hn_small : n < N_F
  · have hFin := hFiniteBd n z hn_pos hn_small
    have hCfin_le : Cfin ≤ CTot := le_max_right _ _
    have hmain :
        Cfin * (n : ℝ) * pairedBrunFactor z
          ≤ CTot * (n : ℝ) * pairedBrunFactor z :=
      main_term_le_of_const_le hCfin_le n z
    linarith
  · have hn_large : N_F ≤ n := Nat.le_of_not_lt hn_small
    have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn_large
    have hnN₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn_large
    have hFix := hFixBd n z hnN₀
    have hAbs := hReservoirBd n z hnN₁
    have hCK_le : C + K ≤ CTot := le_max_left _ _
    have hmain :
        (C + K) * (n : ℝ) * pairedBrunFactor z
          ≤ CTot * (n : ℝ) * pairedBrunFactor z :=
      main_term_le_of_const_le hCK_le n z
    nlinarith

/-- The weighted bridge follows from the two smaller residuals. -/
theorem weightedSchnirelmannResidualBridge_of_residuals
    (hReservoir : FixAStrongReservoirAbsorption)
    (hFinite : ∀ N_F : ℕ, FixAStrongFiniteRangeAbsorptionAligned N_F) :
    WeightedSchnirelmannResidualBridge := by
  intro hFixAStrong
  exact brunGoldbachPairedMainTermRefined_of_absorption
    (pairedMainTermAbsorption_of_fixAStrong_and_residuals
      hFixAStrong hReservoir hFinite)

end PathCWeightedSchnirelmannSafeClosure
end Gdbh

#print axioms
  Gdbh.PathCWeightedSchnirelmannSafeClosure.weightedSchnirelmannResidualBridge_of_refined
#print axioms
  Gdbh.PathCWeightedSchnirelmannSafeClosure.weightedSchnirelmannResidualBridge_of_absorption
#print axioms
  Gdbh.PathCWeightedSchnirelmannSafeClosure.pairedMainTermAbsorption_of_fixAStrong_and_residuals
#print axioms
  Gdbh.PathCWeightedSchnirelmannSafeClosure.weightedSchnirelmannResidualBridge_of_residuals
