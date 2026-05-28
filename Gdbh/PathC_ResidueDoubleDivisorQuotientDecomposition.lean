/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResidueDoubleSumDecomposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path C -- residue double-divisor quotient decomposition

`PathC_ResidueDoubleSumDecomposition` reduces the residue Bonferroni
canonical kernel to the explicit double-divisor count
`ResidueDoubleDivisorCanonicalAtSqrtBound`.

This file peels off the next algebraic layer.  For each divisor pair, the
expected CRT main term is the quotient by the least common multiple, present
only when the common divisor obstruction divides `n`.  The exact count is
split into:

* a quotient main sum;
* a signed counting remainder.

The remaining worker targets are then two strictly smaller Props: identify or
bound the quotient main sum by the actual residue Euler factor, and bound the
signed remainder by the already canonical Bonferroni tail.
-/

namespace Gdbh
namespace PathCResidueDoubleDivisorQuotientDecomposition

open scoped BigOperators
open Finset

open Gdbh.PathCBrunBonferroniSubSqrtCanonical (canonicalK)
open Gdbh.PathCGoldbachResidues (goldbachResidueMainFactor)
open Gdbh.PathCResidueBonferroniAtSqrtCanonical
  (BrunGoldbachResidueSiftedAtSqrtCanonicalKernel residueBonferroniTailAtSqrt)
open Gdbh.PathCResidueBonferroniKernelDecomposition (residuePrimeSet)
open Gdbh.PathCResidueDoubleSumDecomposition
  (ResidueDoubleDivisorCanonicalAtSqrtBound residueDoubleDivisorCountingSum
   residueDoubleDivisorCountingSumAtSqrt
   brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
   pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput)
open Gdbh.PathCSingularCountingInterface (PathCCountingInput)

/-! ## Quotient main term and signed remainder -/

/-- The CRT quotient main term for one product pair.

The congruences `D1 ∣ m` and `D2 ∣ n - m` are compatible only when
`gcd D1 D2 ∣ n`; in that case the expected main count is `n / lcm D1 D2`.
-/
noncomputable def residuePairQuotientMainTerm (n D1 D2 : ℕ) : ℝ :=
  if Nat.gcd D1 D2 ∣ n then
    (n : ℝ) / ((Nat.lcm D1 D2 : ℕ) : ℝ)
  else
    0

/-- The signed remainder after subtracting the CRT quotient main term for one
pair of subset divisors. -/
noncomputable def residuePairCountingRemainder
    (n : ℕ) (d1 d2 : Finset ℕ) : ℝ :=
  (((Finset.Icc 1 (n - 1)).filter
      (fun m => (d1.prod id) ∣ m ∧ (d2.prod id) ∣ (n - m))).card : ℝ)
    - residuePairQuotientMainTerm n (d1.prod id) (d2.prod id)

/-- The quotient main part of the explicit double-divisor sum. -/
noncomputable def residueDoubleDivisorQuotientMainSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residuePairQuotientMainTerm n (d1.prod id) (d2.prod id)

/-- The signed remainder part of the explicit double-divisor sum. -/
noncomputable def residueDoubleDivisorRemainderSum
    (n z k : ℕ) : ℝ :=
  ∑ d1 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
    ∑ d2 ∈ (residuePrimeSet z).powerset.filter (fun d => d.card ≤ k),
      (ArithmeticFunction.moebius (d1.prod id) : ℝ) *
        (ArithmeticFunction.moebius (d2.prod id) : ℝ) *
        residuePairCountingRemainder n d1 d2

/-- At-sqrt quotient main sum at the canonical depth. -/
noncomputable def residueDoubleDivisorQuotientMainSumAtSqrt (n : ℕ) : ℝ :=
  residueDoubleDivisorQuotientMainSum n (Nat.sqrt n) (canonicalK n)

/-- At-sqrt signed remainder sum at the canonical depth. -/
noncomputable def residueDoubleDivisorRemainderSumAtSqrt (n : ℕ) : ℝ :=
  residueDoubleDivisorRemainderSum n (Nat.sqrt n) (canonicalK n)

/-! ## Exact algebraic split -/

/-- The explicit double-divisor count splits exactly into its quotient main
part plus the signed counting remainder. -/
theorem residueDoubleDivisorCountingSum_eq_quotientMain_add_remainder
    (n z k : ℕ) :
    residueDoubleDivisorCountingSum n z k =
      residueDoubleDivisorQuotientMainSum n z k +
        residueDoubleDivisorRemainderSum n z k := by
  classical
  unfold residueDoubleDivisorCountingSum
    residueDoubleDivisorQuotientMainSum residueDoubleDivisorRemainderSum
    residuePairCountingRemainder
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d1 _hd1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d2 _hd2
  ring

/-- At the final threshold, the exact double-divisor count splits into the
at-sqrt quotient main sum and at-sqrt signed remainder. -/
theorem residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder
    (n : ℕ) :
    residueDoubleDivisorCountingSumAtSqrt n =
      residueDoubleDivisorQuotientMainSumAtSqrt n +
        residueDoubleDivisorRemainderSumAtSqrt n := by
  simpa [residueDoubleDivisorCountingSumAtSqrt,
    residueDoubleDivisorQuotientMainSumAtSqrt,
    residueDoubleDivisorRemainderSumAtSqrt] using
      residueDoubleDivisorCountingSum_eq_quotientMain_add_remainder
        n (Nat.sqrt n) (canonicalK n)

/-! ## Strict smaller residual Props -/

/-- Residual main-term worker target: the quotient main sum is bounded by the
actual residue Euler factor at `z = sqrt n`.

This is strictly smaller than the previous double-divisor residual because it
contains no interval counting error. -/
def ResidueDoubleDivisorQuotientMainAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorQuotientMainSumAtSqrt n
      ≤ (n : ℝ) * goldbachResidueMainFactor n (Nat.sqrt n)

/-- Residual CRT-error worker target: the signed counting remainder is bounded
above by the canonical Bonferroni tail.

This is strictly smaller than the previous double-divisor residual because the
quotient main term has already been removed. -/
def ResidueDoubleDivisorRemainderAtSqrtBound : Prop :=
  ∀ n : ℕ, 16 ≤ n →
    residueDoubleDivisorRemainderSumAtSqrt n
      ≤ residueBonferroniTailAtSqrt n (Nat.sqrt n)

/-! ## Bridges back to the active Path C route -/

/-- The quotient-main residual plus the signed-remainder residual imply the
previous explicit double-divisor residual. -/
theorem residueDoubleDivisorCanonicalAtSqrtBound_of_quotientMain_and_remainder
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    ResidueDoubleDivisorCanonicalAtSqrtBound := by
  intro n hn
  rw [residueDoubleDivisorCountingSumAtSqrt_eq_quotientMain_add_remainder]
  have hMain' := hMain n hn
  have hRem' := hRem n hn
  linarith

/-- The quotient-main and signed-remainder residuals close the strict residue
canonical kernel through the existing double-divisor bridge. -/
theorem brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_quotientMain_and_remainder
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound) :
    BrunGoldbachResidueSiftedAtSqrtCanonicalKernel :=
  brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_doubleDivisor
    (residueDoubleDivisorCanonicalAtSqrtBound_of_quotientMain_and_remainder
      hMain hRem)

/-- Final K-Goldbach bridge from the quotient-main residual, the
signed-remainder residual, and any supported counting input. -/
theorem pathC_kGoldbach_of_residueDoubleDivisorQuotient_and_countingInput
    (hMain : ResidueDoubleDivisorQuotientMainAtSqrtBound)
    (hRem : ResidueDoubleDivisorRemainderAtSqrtBound)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residueDoubleDivisorCanonical_and_countingInput
    (residueDoubleDivisorCanonicalAtSqrtBound_of_quotientMain_and_remainder
      hMain hRem)
    hCounting

end PathCResidueDoubleDivisorQuotientDecomposition
end Gdbh

#print axioms
  Gdbh.PathCResidueDoubleDivisorQuotientDecomposition.residueDoubleDivisorCountingSum_eq_quotientMain_add_remainder
#print axioms
  Gdbh.PathCResidueDoubleDivisorQuotientDecomposition.residueDoubleDivisorCanonicalAtSqrtBound_of_quotientMain_and_remainder
#print axioms
  Gdbh.PathCResidueDoubleDivisorQuotientDecomposition.brunGoldbachResidueSiftedAtSqrtCanonicalKernel_of_quotientMain_and_remainder
#print axioms
  Gdbh.PathCResidueDoubleDivisorQuotientDecomposition.pathC_kGoldbach_of_residueDoubleDivisorQuotient_and_countingInput
