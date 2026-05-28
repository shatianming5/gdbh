import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_GoldbachResidues
import Gdbh.PathC_GoldbachRBound
import Gdbh.PathC_SmallSieveSideCondition
import Gdbh.PathC_BrunGoldbachComposition
import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_MertensFirstClosure

/-!
# Path C -- Local Goldbach sieve to singular-factor representation bound

This file provides the next connector in the corrected Goldbach route.  It
does not prove the local Brun main term or the local Mertens product bound;
it states the exact local-product bound needed and shows that, together with
the already-closed small-sieve side condition, those inputs imply the
singular-factor representation bound.
-/

namespace Gdbh
namespace PathCLocalToSingular

open scoped BigOperators
open Gdbh.PathCGoldbachLocalFactor
open Gdbh.PathCGoldbachResidues
  (GoldbachResidueSiftedRefinedUpperBound
   GoldbachResidueSiftedRefinedUpperBoundForLargeZ
   GoldbachResidueSiftedRefinedUpperBoundAtSqrt
   GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   goldbachResidueSiftedCount goldbachSiftedPair_le_residueSiftedCount
   goldbachResidueMainFactor goldbachResidueMainFactor_eq_goldbachLocalFactor
   goldbachResidueRefinedError
   brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
   brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBound
   brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBound
   brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBoundForLargeZ
   brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBoundForLargeZ)
open Gdbh.PathCGoldbachRBound (goldbachRepresentationCount_le_siftedPair_add
  goldbachSiftedPair)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir)
open Gdbh.PathCSmallSieveSideCondition (smallSieveSideCondition_holds)
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCBrunGoldbachComposition
  (mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap)
open Gdbh.PathCMertensSecondProof (pairedBrunMertensThirdGap_of_first_and_abel)
open Gdbh.PathCMertensFirstClosure (mertensFirstTheoremBound_holds)
open Gdbh.PathCClosedReductions (abelInversionMertensSecondFromFirst_holds)

private lemma one_le_singularFactorTerm {n p : ℕ} (hp3 : 3 ≤ p) :
    1 ≤ (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1) := by
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

private lemma singularFactorTerm_nonneg {n p : ℕ} (hp3 : 3 ≤ p) :
    0 ≤ (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1) := by
  have h := one_le_singularFactorTerm (n := n) hp3
  linarith

/-- The truncated singular multiplier is at least one. -/
theorem one_le_truncatedGoldbachSingularMultiplier (n z : ℕ) :
    1 ≤ truncatedGoldbachSingularMultiplier n z := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.one_le_prod ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  exact one_le_singularFactorTerm (n := n) hp3

/-- The full finite Goldbach singular multiplier is at least one. -/
theorem one_le_goldbachSingularMultiplier (n : ℕ) :
    1 ≤ goldbachSingularMultiplier n := by
  simpa [goldbachSingularMultiplier] using
    one_le_truncatedGoldbachSingularMultiplier n n

/-- The truncated singular multiplier is monotone in its truncation level. -/
theorem truncatedGoldbachSingularMultiplier_mono {n z w : ℕ} (hzw : z ≤ w) :
    truncatedGoldbachSingularMultiplier n z ≤
      truncatedGoldbachSingularMultiplier n w := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hzw⟩, hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    exact singularFactorTerm_nonneg (n := n) hp.1.1
  · intro p hp _hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    exact one_le_singularFactorTerm (n := n) hp.1.1

/-- A truncation below `n` is bounded by the full finite singular multiplier. -/
theorem truncatedGoldbachSingularMultiplier_le_full (n z : ℕ) (hz : z ≤ n) :
    truncatedGoldbachSingularMultiplier n z ≤ goldbachSingularMultiplier n := by
  simpa [goldbachSingularMultiplier] using
    (truncatedGoldbachSingularMultiplier_mono (n := n) hz)

/-- Local-factor Mertens bound in the exact shape needed when the sieve
choice is `Nat.sqrt n`.  The singular multiplier is retained on the right. -/
def GoldbachLocalFactorMertensBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
    goldbachLocalFactor n (Nat.sqrt n) ≤
      C / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n

/-- The local-factor Mertens bound follows from the already-closed Mertens
first theorem and Abel-inversion chain, keeping the Goldbach singular
multiplier on the right. -/
theorem goldbachLocalFactorMertensBound_holds :
    GoldbachLocalFactorMertensBound := by
  have hGap := pairedBrunMertensThirdGap_of_first_and_abel
    mertensFirstTheoremBound_holds abelInversionMertensSecondFromFirst_holds
  have hPairMert :=
    mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap hGap
  obtain ⟨C3, N0, hC3pos, hBd⟩ := hPairMert
  refine ⟨(C3 : ℝ), N0, by exact_mod_cast hC3pos, ?_⟩
  intro n hn hn2
  have hpaired := hBd n hn hn2
  have htrunc_le :
      truncatedGoldbachSingularMultiplier n (Nat.sqrt n) ≤
        goldbachSingularMultiplier n :=
    truncatedGoldbachSingularMultiplier_le_full n (Nat.sqrt n)
      (Nat.sqrt_le_self n)
  have htrunc_nonneg :
      0 ≤ truncatedGoldbachSingularMultiplier n (Nat.sqrt n) := by
    have h := one_le_truncatedGoldbachSingularMultiplier n (Nat.sqrt n)
    linarith
  have hbase_nonneg : 0 ≤ (C3 : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  rw [goldbachLocalFactor_eq_paired_mul_singularMultiplier n (Nat.sqrt n)]
  calc
    pairedBrunFactor (Nat.sqrt n) *
          truncatedGoldbachSingularMultiplier n (Nat.sqrt n)
        ≤ ((C3 : ℝ) / (Real.log (n : ℝ)) ^ 2) *
            truncatedGoldbachSingularMultiplier n (Nat.sqrt n) := by
          exact mul_le_mul_of_nonneg_right hpaired htrunc_nonneg
    _ ≤ ((C3 : ℝ) / (Real.log (n : ℝ)) ^ 2) *
            goldbachSingularMultiplier n := by
          exact mul_le_mul_of_nonneg_left htrunc_le hbase_nonneg
    _ = (C3 : ℝ) / (Real.log (n : ℝ)) ^ 2 *
            goldbachSingularMultiplier n := by ring

/-- Local main term plus local-factor Mertens control imply the
singular-factor representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_components
    (hMain : BrunGoldbachLocalMainTermRefined)
    (hMert : GoldbachLocalFactorMertensBound) :
    GoldbachRepresentationBoundWithSingularFactor := by
  obtain ⟨C1, hC1pos, hMainBd⟩ := hMain
  obtain ⟨C2, N₂, hC2pos, hMertBd⟩ := hMert
  obtain ⟨Nsmall, hSmall⟩ := smallSieveSideCondition_holds
  refine ⟨C1 * C2 + 2, max (max N₂ Nsmall) 2, by positivity, ?_⟩
  intro n hn
  have hnM : N₂ ≤ n := by
    exact (le_max_left N₂ Nsmall |>.trans (le_max_left _ _) |>.trans hn)
  have hnSmall : Nsmall ≤ n := by
    exact (le_max_right N₂ Nsmall |>.trans (le_max_left _ _) |>.trans hn)
  have hn2 : 2 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hbase_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hsing_one : 1 ≤ goldbachSingularMultiplier n :=
    one_le_goldbachSingularMultiplier n
  have hsing_nonneg : 0 ≤ goldbachSingularMultiplier n := by
    linarith
  have h_rep_nat := goldbachRepresentationCount_le_siftedPair_add n (Nat.sqrt n)
  have h_rep : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + 2 * ((Nat.sqrt n : ℝ) + 1) := by
    have hcast : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + (2 * (Nat.sqrt n + 1) : ℕ) := by
      exact_mod_cast h_rep_nat
    have h_cast2 :
        ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
      push_cast
      ring
    rwa [h_cast2] at hcast
  have h_sift := hMainBd n (Nat.sqrt n) hnpos
  have h_local := hMertBd n hnM hn2
  have hmain_le : C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) ≤
      C1 * (n : ℝ) *
        (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left h_local
      (mul_nonneg (le_of_lt hC1pos) (by positivity))
  have href : refinedReservoir n (Nat.sqrt n) =
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    simp [refinedReservoir]
  have hsmall := hSmall n hnSmall hn2
  have hbase_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n := by
    exact le_mul_of_one_le_right hbase_nonneg hsing_one
  calc
    (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ)
        ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          + 2 * ((Nat.sqrt n : ℝ) + 1) := h_rep
    _ ≤ (C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n))
          + 2 * ((Nat.sqrt n : ℝ) + 1) := by
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
            rw [href]
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
            linarith
    _ = (C1 * C2 + 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n := by
            field_simp [ne_of_gt hlog_sq_pos]
            ring

/-- Local main term with a fixed constant multiple of the refined reservoir,
plus local-factor Mertens control, still implies the singular-factor
representation bound.  The extra fixed reservoir constant is absorbed into
the final representation-bound constant. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_components_with_error_constant
    (hMain : BrunGoldbachLocalMainTermRefinedWithErrorConstant)
    (hMert : GoldbachLocalFactorMertensBound) :
    GoldbachRepresentationBoundWithSingularFactor := by
  obtain ⟨C1, C_E, hC1pos, hCEpos, hMainBd⟩ := hMain
  obtain ⟨C2, N₂, hC2pos, hMertBd⟩ := hMert
  obtain ⟨Nsmall, hSmall⟩ := smallSieveSideCondition_holds
  refine ⟨C1 * C2 + C_E + 1, max (max N₂ Nsmall) 2, by positivity, ?_⟩
  intro n hn
  have hnM : N₂ ≤ n := by
    exact (le_max_left N₂ Nsmall |>.trans (le_max_left _ _) |>.trans hn)
  have hnSmall : Nsmall ≤ n := by
    exact (le_max_right N₂ Nsmall |>.trans (le_max_left _ _) |>.trans hn)
  have hn2 : 2 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hbase_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hsing_one : 1 ≤ goldbachSingularMultiplier n :=
    one_le_goldbachSingularMultiplier n
  have hsing_nonneg : 0 ≤ goldbachSingularMultiplier n := by
    linarith
  have h_rep_nat := goldbachRepresentationCount_le_siftedPair_add n (Nat.sqrt n)
  have h_rep : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + 2 * ((Nat.sqrt n : ℝ) + 1) := by
    have hcast : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + (2 * (Nat.sqrt n + 1) : ℕ) := by
      exact_mod_cast h_rep_nat
    have h_cast2 :
        ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
      push_cast
      ring
    rwa [h_cast2] at hcast
  have h_sift := hMainBd n (Nat.sqrt n) hnpos
  have h_local := hMertBd n hnM hn2
  have hmain_le : C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) ≤
      C1 * (n : ℝ) *
        (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left h_local
      (mul_nonneg (le_of_lt hC1pos) (by positivity))
  have href : refinedReservoir n (Nat.sqrt n) =
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    simp [refinedReservoir]
  have hsmall := hSmall n hnSmall hn2
  have hbase_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n := by
    exact le_mul_of_one_le_right hbase_nonneg hsing_one
  have hCE_base_le :
      C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left hbase_le (le_of_lt hCEpos)
  calc
    (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ)
        ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          + 2 * ((Nat.sqrt n : ℝ) + 1) := h_rep
    _ ≤ (C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + C_E * refinedReservoir n (Nat.sqrt n))
          + 2 * ((Nat.sqrt n : ℝ) + 1) := by
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
            rw [href]
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
              goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
              goldbachSingularMultiplier n) := by
            linarith
    _ = (C1 * C2 + C_E + 1) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n := by
            field_simp [ne_of_gt hlog_sq_pos]

/-- The final-assembly residue-sifted target at `z = Nat.sqrt n`, plus
local-factor Mertens control, implies the singular-factor representation
bound.  This avoids requiring a full all-`z` local main-term theorem. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrt_components
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt)
    (hMert : GoldbachLocalFactorMertensBound) :
    GoldbachRepresentationBoundWithSingularFactor := by
  obtain ⟨C1, Nsift, hC1pos, hSiftBd⟩ := hSift
  obtain ⟨C2, N₂, hC2pos, hMertBd⟩ := hMert
  obtain ⟨Nsmall, hSmall⟩ := smallSieveSideCondition_holds
  refine ⟨C1 * C2 + 2, max (max (max Nsift N₂) Nsmall) 2, by positivity, ?_⟩
  intro n hn
  have hnSift : Nsift ≤ n := by
    exact (le_max_left Nsift N₂ |>.trans
      (le_max_left (max Nsift N₂) Nsmall) |>.trans
      (le_max_left (max (max Nsift N₂) Nsmall) 2) |>.trans hn)
  have hnM : N₂ ≤ n := by
    exact (le_max_right Nsift N₂ |>.trans
      (le_max_left (max Nsift N₂) Nsmall) |>.trans
      (le_max_left (max (max Nsift N₂) Nsmall) 2) |>.trans hn)
  have hnSmall : Nsmall ≤ n := by
    exact (le_max_right (max Nsift N₂) Nsmall |>.trans
      (le_max_left (max (max Nsift N₂) Nsmall) 2) |>.trans hn)
  have hn2 : 2 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hbase_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hsing_one : 1 ≤ goldbachSingularMultiplier n :=
    one_le_goldbachSingularMultiplier n
  have hsing_nonneg : 0 ≤ goldbachSingularMultiplier n := by
    linarith
  have h_rep_nat := goldbachRepresentationCount_le_siftedPair_add n (Nat.sqrt n)
  have h_rep : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + 2 * ((Nat.sqrt n : ℝ) + 1) := by
    have hcast : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + (2 * (Nat.sqrt n + 1) : ℕ) := by
      exact_mod_cast h_rep_nat
    have h_cast2 :
        ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
      push_cast
      ring
    rwa [h_cast2] at hcast
  have h_res_sift := hSiftBd n hnSift hn2
  have h_pair_le_res :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤
        (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le_residueSiftedCount n (Nat.sqrt n)
  have h_res_to_local :
      (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ) ≤
        C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) +
          refinedReservoir n (Nat.sqrt n) := by
    have hfactor_eq :
        goldbachResidueMainFactor n (Nat.sqrt n) =
          goldbachLocalFactor n (Nat.sqrt n) :=
      goldbachResidueMainFactor_eq_goldbachLocalFactor n (Nat.sqrt n)
    have herr_eq :
        goldbachResidueRefinedError n (Nat.sqrt n) =
          refinedReservoir n (Nat.sqrt n) := by
      simp [goldbachResidueRefinedError]
    simpa [hfactor_eq, herr_eq] using h_res_sift
  have h_sift :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤
        C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) +
          refinedReservoir n (Nat.sqrt n) :=
    h_pair_le_res.trans h_res_to_local
  have h_local := hMertBd n hnM hn2
  have hmain_le : C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) ≤
      C1 * (n : ℝ) *
        (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left h_local
      (mul_nonneg (le_of_lt hC1pos) (by positivity))
  have href : refinedReservoir n (Nat.sqrt n) =
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    simp [refinedReservoir]
  have hsmall := hSmall n hnSmall hn2
  have hbase_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n := by
    exact le_mul_of_one_le_right hbase_nonneg hsing_one
  calc
    (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ)
        ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          + 2 * ((Nat.sqrt n : ℝ) + 1) := h_rep
    _ ≤ (C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n))
          + 2 * ((Nat.sqrt n : ℝ) + 1) := by
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
            rw [href]
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
            linarith
    _ = (C1 * C2 + 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n := by
            field_simp [ne_of_gt hlog_sq_pos]
            ring

/-- The final-assembly paired local main term at `z = Nat.sqrt n`, plus
local-factor Mertens control, implies the singular-factor representation
bound.  This is the narrowest local-factor target consumed by the final
Path C assembly. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_components
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt)
    (hMert : GoldbachLocalFactorMertensBound) :
    GoldbachRepresentationBoundWithSingularFactor := by
  obtain ⟨C1, Nmain, hC1pos, hMainBd⟩ := hMain
  obtain ⟨C2, N₂, hC2pos, hMertBd⟩ := hMert
  obtain ⟨Nsmall, hSmall⟩ := smallSieveSideCondition_holds
  refine ⟨C1 * C2 + 2, max (max (max Nmain N₂) Nsmall) 2, by positivity, ?_⟩
  intro n hn
  have hnMain : Nmain ≤ n := by
    exact (le_max_left Nmain N₂ |>.trans
      (le_max_left (max Nmain N₂) Nsmall) |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hnM : N₂ ≤ n := by
    exact (le_max_right Nmain N₂ |>.trans
      (le_max_left (max Nmain N₂) Nsmall) |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hnSmall : Nsmall ≤ n := by
    exact (le_max_right (max Nmain N₂) Nsmall |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hn2 : 2 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hbase_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hsing_one : 1 ≤ goldbachSingularMultiplier n :=
    one_le_goldbachSingularMultiplier n
  have hsing_nonneg : 0 ≤ goldbachSingularMultiplier n := by
    linarith
  have h_rep_nat := goldbachRepresentationCount_le_siftedPair_add n (Nat.sqrt n)
  have h_rep : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + 2 * ((Nat.sqrt n : ℝ) + 1) := by
    have hcast : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + (2 * (Nat.sqrt n + 1) : ℕ) := by
      exact_mod_cast h_rep_nat
    have h_cast2 :
        ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
      push_cast
      ring
    rwa [h_cast2] at hcast
  have h_sift := hMainBd n hnMain hn2
  have h_local := hMertBd n hnM hn2
  have hmain_le : C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) ≤
      C1 * (n : ℝ) *
        (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left h_local
      (mul_nonneg (le_of_lt hC1pos) (by positivity))
  have href : refinedReservoir n (Nat.sqrt n) =
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    simp [refinedReservoir]
  have hsmall := hSmall n hnSmall hn2
  have hbase_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n := by
    exact le_mul_of_one_le_right hbase_nonneg hsing_one
  calc
    (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ)
        ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          + 2 * ((Nat.sqrt n : ℝ) + 1) := h_rep
    _ ≤ (C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + refinedReservoir n (Nat.sqrt n))
          + 2 * ((Nat.sqrt n : ℝ) + 1) := by
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
            rw [href]
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
            linarith
    _ = (C1 * C2 + 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n := by
            field_simp [ne_of_gt hlog_sq_pos]
            ring

/-- The final-assembly paired local main term at `z = Nat.sqrt n` with a
fixed error constant, plus local-factor Mertens control, implies the
singular-factor representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant_components
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant)
    (hMert : GoldbachLocalFactorMertensBound) :
    GoldbachRepresentationBoundWithSingularFactor := by
  obtain ⟨C1, C_E, Nmain, hC1pos, hCEpos, hMainBd⟩ := hMain
  obtain ⟨C2, N₂, hC2pos, hMertBd⟩ := hMert
  obtain ⟨Nsmall, hSmall⟩ := smallSieveSideCondition_holds
  refine ⟨C1 * C2 + C_E + 1, max (max (max Nmain N₂) Nsmall) 2, by positivity, ?_⟩
  intro n hn
  have hnMain : Nmain ≤ n := by
    exact (le_max_left Nmain N₂ |>.trans
      (le_max_left (max Nmain N₂) Nsmall) |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hnM : N₂ ≤ n := by
    exact (le_max_right Nmain N₂ |>.trans
      (le_max_left (max Nmain N₂) Nsmall) |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hnSmall : Nsmall ≤ n := by
    exact (le_max_right (max Nmain N₂) Nsmall |>.trans
      (le_max_left (max (max Nmain N₂) Nsmall) 2) |>.trans hn)
  have hn2 : 2 ≤ n := by
    exact (le_max_right _ _).trans hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hlog_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hbase_nonneg : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hsing_one : 1 ≤ goldbachSingularMultiplier n :=
    one_le_goldbachSingularMultiplier n
  have hsing_nonneg : 0 ≤ goldbachSingularMultiplier n := by
    linarith
  have h_rep_nat := goldbachRepresentationCount_le_siftedPair_add n (Nat.sqrt n)
  have h_rep : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + 2 * ((Nat.sqrt n : ℝ) + 1) := by
    have hcast : (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ) ≤
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ) + (2 * (Nat.sqrt n + 1) : ℕ) := by
      exact_mod_cast h_rep_nat
    have h_cast2 :
        ((2 * (Nat.sqrt n + 1) : ℕ) : ℝ) = 2 * ((Nat.sqrt n : ℝ) + 1) := by
      push_cast
      ring
    rwa [h_cast2] at hcast
  have h_sift := hMainBd n hnMain hn2
  have h_local := hMertBd n hnM hn2
  have hmain_le : C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) ≤
      C1 * (n : ℝ) *
        (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left h_local
      (mul_nonneg (le_of_lt hC1pos) (by positivity))
  have href : refinedReservoir n (Nat.sqrt n) =
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    simp [refinedReservoir]
  have hsmall := hSmall n hnSmall hn2
  have hbase_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n := by
    exact le_mul_of_one_le_right hbase_nonneg hsing_one
  have hCE_base_le :
      C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n) := by
    exact mul_le_mul_of_nonneg_left hbase_le (le_of_lt hCEpos)
  calc
    (Gdbh.PathCTwinAsymptotic.goldbachRepresentationCount n : ℝ)
        ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          + 2 * ((Nat.sqrt n : ℝ) + 1) := h_rep
    _ ≤ (C1 * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
          + C_E * refinedReservoir n (Nat.sqrt n))
          + 2 * ((Nat.sqrt n : ℝ) + 1) := by
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
            rw [href]
            linarith
    _ ≤ C1 * (n : ℝ) *
          (C2 / (Real.log (n : ℝ)) ^ 2 * goldbachSingularMultiplier n)
          + C_E * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
              goldbachSingularMultiplier n)
          + ((n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
              goldbachSingularMultiplier n) := by
            linarith
    _ = (C1 * C2 + C_E + 1) * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 *
          goldbachSingularMultiplier n := by
            field_simp [ne_of_gt hlog_sq_pos]

/-- After the Abel/Mertens closures, the corrected singular-factor
Goldbach representation bound depends only on the honest local Brun main
term. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main
    (hMain : BrunGoldbachLocalMainTermRefined) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_components hMain
    goldbachLocalFactorMertensBound_holds

/-- After the Abel/Mertens closures, the corrected singular-factor
Goldbach representation bound also follows from the constant-error local
main-term target. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main_with_error_constant
    (hMain : BrunGoldbachLocalMainTermRefinedWithErrorConstant) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_components_with_error_constant
    hMain goldbachLocalFactorMertensBound_holds

/-- After the Abel/Mertens closures, the final-assembly paired local main
term at `z = Nat.sqrt n` directly gives the singular-factor representation
bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrt) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_components
    hMain goldbachLocalFactorMertensBound_holds

/-- After the Abel/Mertens closures, the final-assembly paired local main
term with a fixed error constant directly gives the singular-factor
representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant
    (hMain : BrunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant_components
    hMain goldbachLocalFactorMertensBound_holds

/-- After the Abel/Mertens closures, the final-assembly residue-sifted target
at `z = Nat.sqrt n` directly gives the singular-factor representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrt
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrt) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrt_components
    hSift goldbachLocalFactorMertensBound_holds

/-- After the Abel/Mertens closures, the final-assembly residue-sifted target
with a fixed error constant directly gives the singular-factor representation
bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
    (hSift : GoldbachResidueSiftedRefinedUpperBoundAtSqrtWithErrorConstant) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main_atSqrt_with_error_constant
    (brunGoldbachLocalMainTermRefinedAtSqrtWithErrorConstant_of_residueSiftedRefinedUpperBoundAtSqrtWithErrorConstant
      hSift)

/-- After the Abel/Mertens closures, the canonical refined-error residue-sifted
finite-sieve target directly gives the singular-factor Goldbach
representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBound
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main
    (brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBound hUpper)

/-- After the Abel/Mertens closures, the large-sieve-range refined-error
residue-sifted target directly gives the singular-factor Goldbach
representation bound. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundForLargeZ
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main
    (brunGoldbachLocalMainTermRefined_of_residueSiftedRefinedUpperBoundForLargeZ hLarge)

/-- Same connector routed through the constant-error local interface.  This is
useful for finite-sieve workers that naturally produce the bundled
bounded-error form. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBound_errorConstant
    (hUpper : GoldbachResidueSiftedRefinedUpperBound) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main_with_error_constant
    (brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBound hUpper)

/-- Same large-sieve-range connector routed through the constant-error local
interface. -/
theorem goldbachRepresentationBoundWithSingularFactor_of_residueSiftedRefinedUpperBoundForLargeZ_errorConstant
    (hLarge : GoldbachResidueSiftedRefinedUpperBoundForLargeZ) :
    GoldbachRepresentationBoundWithSingularFactor :=
  goldbachRepresentationBoundWithSingularFactor_of_local_main_with_error_constant
    (brunGoldbachLocalMainTermRefinedWithErrorConstant_of_residueSiftedRefinedUpperBoundForLargeZ
      hLarge)

end PathCLocalToSingular
end Gdbh
