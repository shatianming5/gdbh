/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueBonferroniAtSqrtCanonical

/-!
# Path C -- residue Bonferroni kernel decomposition

This file decomposes the strict residue canonical target
`BrunGoldbachResidueSiftedAtSqrtCanonicalKernel` into a smaller
Bonferroni-truncated-sum residual.

The closed part is mechanical:

* rewrite the residue-sifted cardinality as a sum of divisibility
  indicators using the already-proved bad-residue/divisibility equivalence;
* apply the closed paired Brun-Bonferroni indicator inequality termwise;
* leave only the truncated double-divisor sum estimate as the named worker
  target.

The remaining open Prop keeps the honest local factor
`goldbachResidueMainFactor n (Nat.sqrt n)` and the canonical tail from
`PathC_ResidueBonferroniAtSqrtCanonical`; it does not replace them by a
naive `n / (log n)^2` or any pointwise singular-series log-log estimate.
-/

namespace Gdbh
namespace PathCResidueBonferroniKernelDecomposition

open scoped BigOperators
open Finset

open Gdbh.PathCGoldbachResidues
  (goldbachBadResidueSet goldbachResidueSiftedCount goldbachResidueSiftedSet
   goldbachResidueMainFactor mem_goldbachResidueSiftedSet
   not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub)
open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel residueBonferroniTailAtSqrt
   pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Closed indicator/counting rewrites -/

/-- Odd-prime moduli used in the residue-sifted Goldbach sieve. -/
noncomputable def residuePrimeSet (z : ℕ) : Finset ℕ :=
  (Finset.Icc 3 z).filter Nat.Prime

/-- Every element of `residuePrimeSet z` is prime. -/
theorem residuePrimeSet_prime {z p : ℕ} (hp : p ∈ residuePrimeSet z) :
    Nat.Prime p :=
  (Finset.mem_filter.mp hp).2

/-- The divisibility-indicator form of the odd-prime residue-sifted count. -/
noncomputable def residueDivisibilityIndicatorSum (n z : ℕ) : ℝ := by
  classical
  let P : Finset ℕ := residuePrimeSet z
  exact ∑ m ∈ Finset.Icc 1 (n - 1),
    (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0)

/-- One side of the truncated Möbius-divisor majorant. -/
noncomputable def truncatedMoebiusDivisorSum (z k m : ℕ) : ℝ := by
  classical
  let P : Finset ℕ := residuePrimeSet z
  exact ∑ d ∈ P.powerset.filter (fun d => d.card ≤ k),
    (ArithmeticFunction.moebius (d.prod id) : ℝ) *
      (if (d.prod id) ∣ m then (1 : ℝ) else 0)

/-- The canonical paired Bonferroni majorant for one value of `m`. -/
noncomputable def residuePairedBonferroniMajorant (n z m : ℕ) : ℝ :=
  truncatedMoebiusDivisorSum z (canonicalK n) m *
    truncatedMoebiusDivisorSum z (canonicalK n) (n - m)

/-- The paired truncated Möbius-divisor sum produced by the closed
Brun-Bonferroni indicator inequality. -/
noncomputable def pairedTruncatedDivisorSum (n z k : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.Icc 1 (n - 1),
    truncatedMoebiusDivisorSum z k m *
      truncatedMoebiusDivisorSum z k (n - m)

/-- The residue-sifted set is exactly the paired divisibility-avoidance
filter over odd prime moduli. -/
theorem goldbachResidueSiftedSet_eq_divisibilityFilter (n z : ℕ) :
    goldbachResidueSiftedSet n z =
      (Finset.Icc 1 (n - 1)).filter (fun m =>
        (∀ p ∈ residuePrimeSet z, ¬ p ∣ m) ∧
          (∀ p ∈ residuePrimeSet z, ¬ p ∣ (n - m))) := by
  classical
  ext m
  rw [mem_goldbachResidueSiftedSet, Finset.mem_filter]
  constructor
  · rintro ⟨hmIcc, hbad⟩
    have hmn : m ≤ n := by omega
    refine ⟨Finset.mem_Icc.mpr hmIcc, ?_⟩
    constructor
    · intro p hp
      exact
        ((not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub
          (n := n) (p := p) (m := m) hmn).mp (hbad p hp)).1
    · intro p hp
      exact
        ((not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub
          (n := n) (p := p) (m := m) hmn).mp (hbad p hp)).2
  · rintro ⟨hmIcc, hdiv⟩
    have hmIcc' := Finset.mem_Icc.mp hmIcc
    have hmn : m ≤ n := by omega
    refine ⟨hmIcc', ?_⟩
    intro p hp
    exact
      (not_mem_goldbachBadResidueSet_iff_not_dvd_and_not_dvd_sub
        (n := n) (p := p) (m := m) hmn).mpr
        ⟨hdiv.1 p hp, hdiv.2 p hp⟩

/-- The residue-sifted count equals the divisibility-indicator sum. -/
theorem goldbachResidueSiftedCount_eq_divisibilityIndicatorSum (n z : ℕ) :
    (goldbachResidueSiftedCount n z : ℝ) =
      residueDivisibilityIndicatorSum n z := by
  classical
  unfold goldbachResidueSiftedCount residueDivisibilityIndicatorSum
  rw [goldbachResidueSiftedSet_eq_divisibilityFilter]
  simp [Finset.sum_boole]

/-- Closed termwise Bonferroni step from the residue indicator sum to the
paired truncated Möbius-divisor sum. -/
theorem residueDivisibilityIndicatorSum_le_pairedTruncatedDivisorSum
    (n z k : ℕ) (hk : Even k) :
    residueDivisibilityIndicatorSum n z ≤ pairedTruncatedDivisorSum n z k := by
  classical
  unfold residueDivisibilityIndicatorSum pairedTruncatedDivisorSum
  let P : Finset ℕ := residuePrimeSet z
  apply Finset.sum_le_sum
  intro m hm
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact residuePrimeSet_prime hp
  have hmn : m ≤ n := by
    have hm_le : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
    omega
  simpa [truncatedMoebiusDivisorSum, P] using
    Gdbh.PathCPairedBonferroniIndicator.pairedBonferroniIndicator_holds
      P m n k hP hk hmn

/-! ## Smaller residual and bridges -/

/-- The strict smaller Bonferroni worker target at the canonical depth
`canonicalK n = 2 * n`.

This is smaller than `BrunGoldbachResidueSiftedAtSqrtCanonicalKernel`
because the residue-set cardinality and the Bonferroni indicator layer have
already been peeled off; the only remaining content is the canonical estimate
for the truncated double-divisor sum. -/
def ResidueBonferroniTruncatedSumCanonicalBoundAtSqrt : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    pairedTruncatedDivisorSum n (Nat.sqrt n) (canonicalK n)
      ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- The same residual written as the `m`-sum of canonical paired Bonferroni
majorants.  This is the handoff point for the closed rearrangement layer. -/
def ResidueDoubleSumCanonicalAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    (∑ m ∈ Finset.Icc 1 (n - 1),
        residuePairedBonferroniMajorant n (Nat.sqrt n) m)
      ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
        + residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-- The explicit double-sum residual is the canonical truncated-sum residual. -/
theorem residueBonferroniTruncatedSumCanonicalBoundAtSqrt_of_doubleSum
    (h : ResidueDoubleSumCanonicalAtSqrtBound) :
    ResidueBonferroniTruncatedSumCanonicalBoundAtSqrt := by
  intro n hn
  simpa [pairedTruncatedDivisorSum, residuePairedBonferroniMajorant] using h n hn

/-- The truncated-sum residual closes the existing strict residue canonical
kernel. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_truncatedSumBound
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrt) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel := by
  intro n hn
  have hk : Even (canonicalK n) := by
    unfold canonicalK
    exact even_two_mul n
  calc
    (goldbachResidueSiftedCount n (Nat.sqrt n) : ℝ)
        = residueDivisibilityIndicatorSum n (Nat.sqrt n) :=
          goldbachResidueSiftedCount_eq_divisibilityIndicatorSum n (Nat.sqrt n)
    _ ≤ pairedTruncatedDivisorSum n (Nat.sqrt n) (canonicalK n) :=
          residueDivisibilityIndicatorSum_le_pairedTruncatedDivisorSum
            n (Nat.sqrt n) (canonicalK n) hk
    _ ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)
          + residueBonferroniTailAtSqrt n (Nat.sqrt n) :=
          h n hn

/-- The double-sum residual closes the existing strict residue canonical
kernel. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleSum
    (h : ResidueDoubleSumCanonicalAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_truncatedSumBound
    (residueBonferroniTruncatedSumCanonicalBoundAtSqrt_of_doubleSum h)

/-- Final route from the smaller truncated-sum residual and any supported
counting input.  The canonical tail domination is already closed in
`PathC_ResidueBonferroniAtSqrtCanonical`. -/
theorem pathC_kGoldbach_of_residueTruncatedSumBound_and_countingInput
    (h : ResidueBonferroniTruncatedSumCanonicalBoundAtSqrt)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueBonferroniCanonical_and_countingInput_closedTail
    (brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_truncatedSumBound h)
    hCounting

end PathCResidueBonferroniKernelDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.goldbachResidueSiftedSet_eq_divisibilityFilter
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.goldbachResidueSiftedCount_eq_divisibilityIndicatorSum
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.residueDivisibilityIndicatorSum_le_pairedTruncatedDivisorSum
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.residueBonferroniTruncatedSumCanonicalBoundAtSqrt_of_doubleSum
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_truncatedSumBound
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleSum
#print axioms
  Gdbh.PathCResidueBonferroniKernelDecomposition.pathC_kGoldbach_of_residueTruncatedSumBound_and_countingInput
