/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResiduePairCountingIntervalEnvelope
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Path C -- sharp D-level pair-counting envelope

Round 90 closes the D-level CRT interval discrepancy left by
`PathC_ResiduePairCountingIntervalEnvelope`.

The proof decomposes the sharp bound into four smaller algebraic facts:

* incompatible gcd support contributes zero;
* compatible divisor-pair support is one residue class modulo `lcm D1 D2`;
* the full range `Ico 0 n` count differs from `(n : R) / lcm` by at most `1`;
* replacing `Ico 0 n` by `Icc 1 (n - 1)` deletes at most the endpoint `0`.

Together these give `ResiduePairDivisorSharpIntervalEnvelope 2`.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResiduePairDivisorSharpEnvelope

open Finset

open Gdbh.PathCResidueDoubleDivisorQuotientDecomposition
  (residuePairQuotientMainTerm)
open Gdbh.PathCResiduePairCountingIntervalEnvelope
  (ResiduePairDivisorSharpIntervalEnvelope residuePairDivisorCountingRemainder)

/-! ## Small quotient facts -/

/-- The real quotient by a positive natural denominator lies below the next
integer after natural division. -/
theorem real_nat_div_lt_floor_add_one (n L : ℕ) (hL : 0 < L) :
    (n : ℝ) / (L : ℝ) < ((n / L + 1 : ℕ) : ℝ) := by
  have hlt_nat : n < (n / L + 1) * L := by
    calc
      n = L * (n / L) + n % L := (Nat.div_add_mod n L).symm
      _ = n / L * L + n % L := by rw [Nat.mul_comm L (n / L)]
      _ < n / L * L + L := Nat.add_lt_add_left (Nat.mod_lt n hL) _
      _ = (n / L + 1) * L := by
        rw [Nat.add_mul, Nat.one_mul]
  have hlt_real : (n : ℝ) < ((n / L + 1 : ℕ) : ℝ) * (L : ℝ) := by
    exact_mod_cast hlt_nat
  have hL_real : 0 < (L : ℝ) := by
    exact_mod_cast hL
  rw [div_lt_iff₀ hL_real]
  simpa [mul_comm] using hlt_real

/-! ## Incompatible branch -/

/-- If the product gcd obstruction does not divide `n`, then the D-level
pair count and quotient main term are both zero. -/
theorem residuePairDivisorCountingRemainder_eq_zero_of_not_gcd_dvd
    (n D1 D2 : ℕ) (hnot : ¬ Nat.gcd D1 D2 ∣ n) :
    residuePairDivisorCountingRemainder n D1 D2 = 0 := by
  unfold residuePairDivisorCountingRemainder residuePairQuotientMainTerm
  have hcard_zero :
      ((Finset.Icc 1 (n - 1)).filter
        (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro m hm hcond
    obtain ⟨_hm_ge, _hm_le_pred⟩ := Finset.mem_Icc.mp hm
    have hm_le_n : m ≤ n := by omega
    obtain ⟨hD1m, hD2nm⟩ := hcond
    have hg_m : Nat.gcd D1 D2 ∣ m :=
      Nat.dvd_trans (Nat.gcd_dvd_left _ _) hD1m
    have hg_nm : Nat.gcd D1 D2 ∣ n - m :=
      Nat.dvd_trans (Nat.gcd_dvd_right _ _) hD2nm
    have hsum : (n - m) + m = n := Nat.sub_add_cancel hm_le_n
    have hg_n : Nat.gcd D1 D2 ∣ n := by
      have hdiv := Nat.dvd_add hg_nm hg_m
      simpa [hsum] using hdiv
    exact hnot hg_n
  rw [hcard_zero, if_neg hnot]
  norm_num

/-! ## Compatible branch as one residue class -/

/-- For `m ≤ n`, divisibility of the natural subtraction is equivalent to
the corresponding modular congruence. -/
theorem dvd_sub_iff_modEq {n m d : ℕ} (hmn : m ≤ n) :
    d ∣ (n - m) ↔ m ≡ n [MOD d] := by
  rw [Nat.modEq_iff_dvd' hmn]

/-- On the compatible gcd branch, the paired divisibility condition is a
single congruence modulo `lcm D1 D2`. -/
theorem residuePairDivisorCondition_iff_modEq_lcm
    {n m D1 D2 : ℕ}
    (hcompat : 0 ≡ n [MOD Nat.gcd D1 D2]) (hmn : m ≤ n) :
    (D1 ∣ m ∧ D2 ∣ (n - m)) ↔
      m ≡ (Nat.chineseRemainder' hcompat).val [MOD Nat.lcm D1 D2] := by
  classical
  set c : ℕ := (Nat.chineseRemainder' hcompat).val with hc_def
  have hcr := (Nat.chineseRemainder' hcompat).property
  constructor
  · rintro ⟨hD1m, hD2nm⟩
    have hm1 : m ≡ 0 [MOD D1] := Nat.modEq_zero_iff_dvd.mpr hD1m
    have hm2 : m ≡ n [MOD D2] := (dvd_sub_iff_modEq hmn).mp hD2nm
    have hmc1 : m ≡ c [MOD D1] := by
      simpa [hc_def] using hm1.trans hcr.1.symm
    have hmc2 : m ≡ c [MOD D2] := by
      simpa [hc_def] using hm2.trans hcr.2.symm
    exact Nat.mod_lcm hmc1 hmc2
  · intro hmc
    have hm1c : m ≡ c [MOD D1] := by
      exact hmc.of_dvd (Nat.dvd_lcm_left D1 D2)
    have hm2c : m ≡ c [MOD D2] := by
      exact hmc.of_dvd (Nat.dvd_lcm_right D1 D2)
    have hm1 : m ≡ 0 [MOD D1] := by
      simpa [hc_def] using hm1c.trans hcr.1
    have hm2 : m ≡ n [MOD D2] := by
      simpa [hc_def] using hm2c.trans hcr.2
    exact ⟨Nat.modEq_zero_iff_dvd.mp hm1, (dvd_sub_iff_modEq hmn).mpr hm2⟩

/-- On the compatible branch, the full `Ico 0 n` paired count is the standard
single-residue count modulo `lcm D1 D2`. -/
theorem residuePairDivisorFullRangeCount_eq_of_gcd_dvd
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hdiv : Nat.gcd D1 D2 ∣ n) :
    ((Finset.Ico 0 n).filter
      (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card =
      n / Nat.lcm D1 D2 +
        (if
          (Nat.chineseRemainder'
            ((Nat.modEq_zero_iff_dvd.mpr hdiv).symm :
              0 ≡ n [MOD Nat.gcd D1 D2])).val %
              Nat.lcm D1 D2 < n % Nat.lcm D1 D2
          then 1 else 0) := by
  classical
  let hcompat : 0 ≡ n [MOD Nat.gcd D1 D2] :=
    (Nat.modEq_zero_iff_dvd.mpr hdiv).symm
  set c : ℕ := (Nat.chineseRemainder' hcompat).val with hc_def
  have hL : 0 < Nat.lcm D1 D2 := Nat.lcm_pos hD1 hD2
  have hfilt :
      (Finset.Ico 0 n).filter (fun m => D1 ∣ m ∧ D2 ∣ (n - m)) =
        (Finset.Ico 0 n).filter
          (fun m => m ≡ c [MOD Nat.lcm D1 D2]) := by
    apply Finset.filter_congr
    intro m hm
    have hmn : m ≤ n := (Finset.mem_Ico.mp hm).2.le
    simpa [hc_def] using
      (residuePairDivisorCondition_iff_modEq_lcm
        (n := n) (m := m) (D1 := D1) (D2 := D2) hcompat hmn)
  rw [hfilt]
  have hrange : Finset.Ico 0 n = Finset.range n := by
    ext x
    simp [Finset.mem_range]
  rw [hrange]
  have hcount :=
    Nat.count_eq_card_filter_range
      (p := fun m => m ≡ c [MOD Nat.lcm D1 D2]) n
  rw [← hcount]
  simpa [hc_def, hcompat] using Nat.count_modEq_card n hL c

/-- The full compatible `Ico 0 n` count differs from the real quotient by at
most `1`. -/
theorem residuePairDivisorFullRangeCount_abs_sub_quotient_le_one_of_gcd_dvd
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hdiv : Nat.gcd D1 D2 ∣ n) :
    |(((Finset.Ico 0 n).filter
        (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
      - (n : ℝ) / (Nat.lcm D1 D2 : ℝ)| ≤ 1 := by
  classical
  let hcompat : 0 ≡ n [MOD Nat.gcd D1 D2] :=
    (Nat.modEq_zero_iff_dvd.mpr hdiv).symm
  set c : ℕ := (Nat.chineseRemainder' hcompat).val with hc_def
  set L : ℕ := Nat.lcm D1 D2 with hL_def
  have hLpos : 0 < L := by
    simpa [hL_def] using Nat.lcm_pos hD1 hD2
  have hfull :=
    residuePairDivisorFullRangeCount_eq_of_gcd_dvd n D1 D2 hD1 hD2 hdiv
  have hfloor_le :
      (((n / L : ℕ) : ℝ) ≤ (n : ℝ) / (L : ℝ)) := by
    exact Nat.cast_div_le
  have hquot_le_succ :
      (n : ℝ) / (L : ℝ) ≤ ((n / L + 1 : ℕ) : ℝ) :=
    le_of_lt (real_nat_div_lt_floor_add_one n L hLpos)
  have hsucc_cast :
      ((n / L + 1 : ℕ) : ℝ) = ((n / L : ℕ) : ℝ) + 1 := by
    norm_num
  by_cases hcase : c % L < n % L
  · have hfull_nat :
        ((Finset.Ico 0 n).filter
          (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card = n / L + 1 := by
      simpa [c, hc_def, L, hL_def, hcompat, hcase] using hfull
    have hfull_real :
        (((Finset.Ico 0 n).filter
          (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) =
            ((n / L + 1 : ℕ) : ℝ) := by
      exact_mod_cast hfull_nat
    rw [hfull_real]
    have hnonneg :
        0 ≤ ((n / L + 1 : ℕ) : ℝ) - (n : ℝ) / (L : ℝ) :=
      sub_nonneg.mpr hquot_le_succ
    rw [abs_of_nonneg hnonneg]
    nlinarith [hfloor_le, hsucc_cast]
  · have hfull_nat :
        ((Finset.Ico 0 n).filter
          (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card = n / L := by
      simpa [c, hc_def, L, hL_def, hcompat, hcase] using hfull
    have hfull_real :
        (((Finset.Ico 0 n).filter
          (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) =
            ((n / L : ℕ) : ℝ) := by
      exact_mod_cast hfull_nat
    rw [hfull_real]
    have hnonpos :
        ((n / L : ℕ) : ℝ) - (n : ℝ) / (L : ℝ) ≤ 0 :=
      sub_nonpos.mpr hfloor_le
    rw [abs_of_nonpos hnonpos]
    nlinarith [hquot_le_succ, hsucc_cast]

/-! ## Endpoint deletion -/

/-- The full range `Ico 0 n` is the interval `Icc 1 (n - 1)` plus the
possible endpoint `0`. -/
theorem residuePairDivisorFullRangeCount_eq_iccCount_add_zero
    (n D1 D2 : ℕ) (hn : 1 ≤ n) :
    ((Finset.Ico 0 n).filter
      (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card =
      ((Finset.Icc 1 (n - 1)).filter
        (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card +
        (if D2 ∣ n then 1 else 0) := by
  classical
  have hicc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
  have hsplit : Finset.Ico 0 n = insert 0 (Finset.Ico 1 n) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    constructor
    · rintro ⟨_, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact Or.inl rfl
      · exact Or.inr ⟨hk0, hk⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Nat.zero_le _, hn⟩
      · exact ⟨Nat.zero_le _, h2⟩
  have hzero_not_mem : 0 ∉ Finset.Ico 1 n := by
    intro h
    have := (Finset.mem_Ico.mp h).1
    omega
  set p : ℕ → Prop := fun m => D1 ∣ m ∧ D2 ∣ (n - m) with hp_def
  have hp0 : p 0 ↔ D2 ∣ n := by
    simp [hp_def]
  have hfilt_split :
      (Finset.Ico 0 n).filter p =
        if p 0 then insert 0 ((Finset.Ico 1 n).filter p)
              else (Finset.Ico 1 n).filter p := by
    rw [hsplit]
    exact Finset.filter_insert p (0 : ℕ) (Finset.Ico 1 n)
  by_cases h0 : p 0
  · have hdvdn : D2 ∣ n := hp0.mp h0
    rw [if_pos hdvdn, hicc]
    have hzero_not_mem' : 0 ∉ (Finset.Ico 1 n).filter p := by
      intro hmem
      exact hzero_not_mem (Finset.mem_filter.mp hmem).1
    change ((Finset.Ico 0 n).filter p).card =
      ((Finset.Ico 1 n).filter p).card + 1
    rw [hfilt_split, if_pos h0,
      Finset.card_insert_of_notMem hzero_not_mem']
  · have hndvdn : ¬ D2 ∣ n := fun h => h0 (hp0.mpr h)
    rw [if_neg hndvdn, Nat.add_zero, hicc]
    change ((Finset.Ico 0 n).filter p).card =
      ((Finset.Ico 1 n).filter p).card
    rw [hfilt_split, if_neg h0]

/-- Passing from `Ico 0 n` to `Icc 1 (n - 1)` changes the pair count by at
most one. -/
theorem residuePairDivisorIccCount_abs_sub_fullRangeCount_le_one
    (n D1 D2 : ℕ) :
    |(((Finset.Icc 1 (n - 1)).filter
        (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
      - (((Finset.Ico 0 n).filter
        (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)| ≤ 1 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    norm_num
  · have hn : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
    have hfull :=
      residuePairDivisorFullRangeCount_eq_iccCount_add_zero n D1 D2 hn
    by_cases hdvd : D2 ∣ n
    · have hfull_nat :
          ((Finset.Ico 0 n).filter
            (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card =
            ((Finset.Icc 1 (n - 1)).filter
              (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card + 1 := by
        simpa [hdvd] using hfull
      have hfull_real :
          (((Finset.Ico 0 n).filter
            (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) =
            (((Finset.Icc 1 (n - 1)).filter
              (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) + 1 := by
        exact_mod_cast hfull_nat
      rw [hfull_real]
      ring_nf
      norm_num
    · have hfull_nat :
          ((Finset.Ico 0 n).filter
            (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card =
            ((Finset.Icc 1 (n - 1)).filter
              (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card := by
        simpa [hdvd] using hfull
      have hfull_real :
          (((Finset.Ico 0 n).filter
            (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) =
            (((Finset.Icc 1 (n - 1)).filter
              (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ) := by
        exact_mod_cast hfull_nat
      rw [hfull_real]
      simp

/-! ## Sharp envelope -/

/-- Compatible D-level pair remainders have absolute value at most `2`. -/
theorem residuePairDivisorCountingRemainder_abs_le_two_of_gcd_dvd
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hdiv : Nat.gcd D1 D2 ∣ n) :
    |residuePairDivisorCountingRemainder n D1 D2| ≤ (2 : ℝ) := by
  unfold residuePairDivisorCountingRemainder residuePairQuotientMainTerm
  rw [if_pos hdiv]
  set a : ℝ :=
    (((Finset.Icc 1 (n - 1)).filter
      (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
  set b : ℝ :=
    (((Finset.Ico 0 n).filter
      (fun m => D1 ∣ m ∧ D2 ∣ (n - m))).card : ℝ)
  set q : ℝ := (n : ℝ) / (Nat.lcm D1 D2 : ℝ)
  have h_endpoint : |a - b| ≤ (1 : ℝ) := by
    dsimp [a, b]
    exact residuePairDivisorIccCount_abs_sub_fullRangeCount_le_one n D1 D2
  have h_full : |b - q| ≤ (1 : ℝ) := by
    dsimp [b, q]
    exact residuePairDivisorFullRangeCount_abs_sub_quotient_le_one_of_gcd_dvd
      n D1 D2 hD1 hD2 hdiv
  calc
    |a - q| = |(a - b) + (b - q)| := by ring_nf
    _ ≤ |a - b| + |b - q| := abs_add_le (a - b) (b - q)
    _ ≤ (1 : ℝ) + 1 := add_le_add h_endpoint h_full
    _ = (2 : ℝ) := by norm_num

/-- Uniform D-level pair-counting discrepancy. -/
theorem residuePairDivisorCountingRemainder_abs_le_two_of_pos
    (n D1 D2 : ℕ) (hD1 : 0 < D1) (hD2 : 0 < D2) :
    |residuePairDivisorCountingRemainder n D1 D2| ≤ (2 : ℝ) := by
  by_cases hdiv : Nat.gcd D1 D2 ∣ n
  · exact residuePairDivisorCountingRemainder_abs_le_two_of_gcd_dvd
      n D1 D2 hD1 hD2 hdiv
  · rw [residuePairDivisorCountingRemainder_eq_zero_of_not_gcd_dvd n D1 D2 hdiv]
    norm_num

/-- Closed sharp interval envelope with bound `2`. -/
theorem residuePairDivisorSharpIntervalEnvelope_two :
    ResiduePairDivisorSharpIntervalEnvelope (2 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  intro n D1 D2 hD1 hD2
  exact residuePairDivisorCountingRemainder_abs_le_two_of_pos n D1 D2 hD1 hD2

/-! ## Round 89 bridges with the sharp bound -/

/-- The closed sharp CRT discrepancy supplies a uniform interval envelope
for every large-range threshold. -/
theorem residuePairDivisorIntervalEnvelopeAfter_two (N : ℕ) :
    _root_.Gdbh.PathCResiduePairCountingIntervalEnvelope.ResiduePairDivisorIntervalEnvelopeAfter
      N (fun _ => (2 : ℝ)) :=
  _root_.Gdbh.PathCResiduePairCountingIntervalEnvelope.residuePairDivisorIntervalEnvelopeAfter_of_sharp
    N residuePairDivisorSharpIntervalEnvelope_two

/-- The filtered witness-cover pair remainder has a bound `2` envelope. -/
theorem residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two
    (N : ℕ) :
    _root_.Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise.ResidueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter
      N (fun _ => (2 : ℝ)) :=
  _root_.Gdbh.PathCResiduePairCountingIntervalEnvelope.residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_of_divisorIntervalEnvelope
    (residuePairDivisorIntervalEnvelopeAfter_two N)

end PathCResiduePairDivisorSharpEnvelope
end Gdbh

#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorCondition_iff_modEq_lcm
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorFullRangeCount_abs_sub_quotient_le_one_of_gcd_dvd
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorIccCount_abs_sub_fullRangeCount_le_one
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorCountingRemainder_abs_le_two_of_pos
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorSharpIntervalEnvelope_two
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residuePairDivisorIntervalEnvelopeAfter_two
#print axioms
  Gdbh.PathCResiduePairDivisorSharpEnvelope.residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two
