/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueCanonicalAnalyticTailReduction
import Gdbh.PathC_MertensSecondUpper

/-!
# Path C -- residue main factor Mertens lower bound

Round 41 split the analytic tail into two worker estimates.  This file closes
the residue-main-factor half from the already verified paired-Brun Mertens
lower gap.

The remaining analytic tail worker after this file is the residue-sifted count
upper bound of size `n / (log n)^2`.
-/

set_option maxHeartbeats 800000

namespace Gdbh
namespace PathCResidueMainFactorMertensLower

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueMainFactor)
open Gdbh.PathCResidueCanonicalSqrtSeventeenToThirtySixSplit
  (residueFactorProduct_lower_two_of_three_le)
open Gdbh.PathCResidueCanonicalAnalyticTailReduction
  (ResidueSiftedCountLogSquaredUpperAfter
   ResidueMainFactorLogSquaredLowerAfter
   ResidueCanonicalLogSquaredTailInputs
   finiteSieveInput_of_residueCanonicalLogSquared_tail_inputs
   pathC_kGoldbach_of_residueCanonicalLogSquared_tail_inputs_and_countingInput)
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCPairedBrunMertensLowerReal (PairedBrunMertensThirdLowerGap)
open Gdbh.PathCMertensSecondUpper (pairedBrunMertensThirdLowerGap_holds)
open Gdbh.PathCSingularCountingInterface
  (PathCCountingInput PathCFiniteSieveInput)

/-! ## Eventual worker targets -/

/-- Eventual form of the residue-sifted count upper bound. -/
noncomputable def ResidueSiftedCountLogSquaredUpperEventually : Prop :=
  ∃ N : ℕ, ∃ A : ℝ, ResidueSiftedCountLogSquaredUpperAfter N A

/-- Eventual form of the residue main-factor lower bound. -/
noncomputable def ResidueMainFactorLogSquaredLowerEventually : Prop :=
  ∃ N : ℕ, ∃ B : ℝ, ResidueMainFactorLogSquaredLowerAfter N B

/-- Eventual form of the bundled Round 41 analytic tail input. -/
noncomputable def ResidueCanonicalLogSquaredTailEventually : Prop :=
  ∃ N : ℕ, ResidueCanonicalLogSquaredTailInputs N

/-! ## Local factor comparison -/

/-- The residue main factor dominates the paired-Brun product, because each
bad-residue set has cardinal at most two. -/
theorem pairedBrunFactor_le_goldbachResidueMainFactor (n z : ℕ) :
    pairedBrunFactor z ≤ goldbachResidueMainFactor n z := by
  classical
  let Pz : Finset ℕ := (Finset.Icc 3 z).filter Nat.Prime
  have h3 : ∀ p ∈ Pz, 3 ≤ p := by
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  simpa [pairedBrunFactor, goldbachResidueMainFactor, Pz] using
    residueFactorProduct_lower_two_of_three_le n Pz h3

/-! ## Mertens lower bridge -/

/-- The paired-Brun Mertens lower gap gives an eventual lower bound for the
residue main factor at `z = Nat.sqrt n`. -/
theorem residueMainFactorLogSquaredLowerAfter_of_pairedBrunMertensThirdLowerGap
    (hGap : PairedBrunMertensThirdLowerGap) :
    ResidueMainFactorLogSquaredLowerEventually := by
  rcases hGap with ⟨C, z0, hCpos, hGapBd⟩
  refine ⟨max z0 2, C, ?_⟩
  refine ⟨hCpos, ?_⟩
  intro n _hn hsqrt_after
  set z := Nat.sqrt n
  have hz_ge_z0 : z0 ≤ z := by
    have hmax : max z0 2 + 1 ≤ z := by simpa [z] using hsqrt_after
    omega
  have hz_ge_three : 3 ≤ z := by
    have hmax : max z0 2 + 1 ≤ z := by simpa [z] using hsqrt_after
    omega
  have hz_pos_nat : 0 < z := by omega
  have hz_le_n : z ≤ n := by
    simpa [z] using Nat.sqrt_le_self n
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hz_pos_nat hz_le_n
  have hlogz_pos : 0 < Real.log (z : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogn_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog_le : Real.log (z : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log
      (by exact_mod_cast hz_pos_nat)
      (by exact_mod_cast hz_le_n)
  have hsq_le :
      (Real.log (z : ℝ))^2 ≤ (Real.log (n : ℝ))^2 := by
    nlinarith [hlogz_pos, hlogn_pos, hlog_le]
  have hC_nonneg : 0 ≤ C := le_of_lt hCpos
  have hden :
      C / (Real.log (n : ℝ))^2 ≤ C / (Real.log (z : ℝ))^2 := by
    exact div_le_div_of_nonneg_left hC_nonneg (by positivity) hsq_le
  have hgap_z :
      C / (Real.log (z : ℝ))^2 ≤ pairedBrunFactor z :=
    hGapBd z hz_ge_z0
  have hpair_res :
      pairedBrunFactor z ≤ goldbachResidueMainFactor n z :=
    pairedBrunFactor_le_goldbachResidueMainFactor n z
  simpa [z] using hden.trans (hgap_z.trans hpair_res)

/-- The residue main-factor lower half of the Round 41 analytic tail is
closed by the existing paired-Brun Mertens lower theorem. -/
theorem residueMainFactorLogSquaredLowerEventually_holds :
    ResidueMainFactorLogSquaredLowerEventually :=
  residueMainFactorLogSquaredLowerAfter_of_pairedBrunMertensThirdLowerGap
    pairedBrunMertensThirdLowerGap_holds

/-! ## Threshold monotonicity and recombination -/

/-- Raising the threshold preserves the residue-sifted count upper bound. -/
theorem residueSiftedCountLogSquaredUpperAfter_mono
    {N M : ℕ} {A : ℝ} (hNM : N ≤ M)
    (h : ResidueSiftedCountLogSquaredUpperAfter N A) :
    ResidueSiftedCountLogSquaredUpperAfter M A := by
  rcases h with ⟨hA, hbd⟩
  refine ⟨hA, ?_⟩
  intro n hn hsqrt
  exact hbd n hn (by omega)

/-- Raising the threshold preserves the residue main-factor lower bound. -/
theorem residueMainFactorLogSquaredLowerAfter_mono
    {N M : ℕ} {B : ℝ} (hNM : N ≤ M)
    (h : ResidueMainFactorLogSquaredLowerAfter N B) :
    ResidueMainFactorLogSquaredLowerAfter M B := by
  rcases h with ⟨hB, hbd⟩
  refine ⟨hB, ?_⟩
  intro n hn hsqrt
  exact hbd n hn (by omega)

/-- Once the residue-sifted count upper bound is eventually available, the
closed Mertens lower bound supplies the full bundled analytic tail input. -/
theorem residueCanonicalLogSquaredTailEventually_of_siftedUpperEventually
    (hUpper : ResidueSiftedCountLogSquaredUpperEventually) :
    ResidueCanonicalLogSquaredTailEventually := by
  rcases hUpper with ⟨NU, A, hU⟩
  rcases residueMainFactorLogSquaredLowerEventually_holds with ⟨NL, B, hL⟩
  refine ⟨max NU NL, A, B, ?_, ?_⟩
  · exact residueSiftedCountLogSquaredUpperAfter_mono
      (le_max_left NU NL) hU
  · exact residueMainFactorLogSquaredLowerAfter_mono
      (le_max_right NU NL) hL

/-- Eventual residue-sifted count upper bound supplies the finite-sieve input,
because the residue main-factor lower half is already closed. -/
theorem finiteSieveInput_of_residueSiftedCountLogSquaredUpperEventually
    (hUpper : ResidueSiftedCountLogSquaredUpperEventually) :
    PathCFiniteSieveInput := by
  rcases residueCanonicalLogSquaredTailEventually_of_siftedUpperEventually
      hUpper with ⟨N, hInputs⟩
  exact finiteSieveInput_of_residueCanonicalLogSquared_tail_inputs
    N hInputs

/-- Final Path C adapter after closing the residue main-factor lower half of
the analytic tail. -/
theorem pathC_kGoldbach_of_residueSiftedCountLogSquaredUpperEventually_and_countingInput
    (hUpper : ResidueSiftedCountLogSquaredUpperEventually)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n := by
  rcases residueCanonicalLogSquaredTailEventually_of_siftedUpperEventually
      hUpper with ⟨N, hInputs⟩
  exact
    pathC_kGoldbach_of_residueCanonicalLogSquared_tail_inputs_and_countingInput
      N hInputs hCounting

end PathCResidueMainFactorMertensLower
end Gdbh

#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.pairedBrunFactor_le_goldbachResidueMainFactor
#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.residueMainFactorLogSquaredLowerAfter_of_pairedBrunMertensThirdLowerGap
#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.residueMainFactorLogSquaredLowerEventually_holds
#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.residueCanonicalLogSquaredTailEventually_of_siftedUpperEventually
#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.finiteSieveInput_of_residueSiftedCountLogSquaredUpperEventually
#print axioms
  Gdbh.PathCResidueMainFactorMertensLower.pathC_kGoldbach_of_residueSiftedCountLogSquaredUpperEventually_and_countingInput
