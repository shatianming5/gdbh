/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex master controller
-/
import Gdbh.PathC_ResiduePairDivisorSharpEnvelope

/-!
# Path C -- sharp filtered-cover tail reduction

Round 91 packages the closed Round 90 CRT interval discrepancy into the
Round 87 filtered-cover tail decomposition.  The termwise remainder is now
closed with the constant envelope `R n = 2`; the remaining large-range work is
the scalar cardinal-tail estimate for that constant envelope, together with
the divisor-family cardinality envelope.
-/

set_option maxHeartbeats 500000

namespace Gdbh
namespace PathCResidueRemainderWitnessCoverFilteredSharpTail

open Gdbh.PathCResidueRemainderWitnessCoverFiltered
  (ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredTailDecomposition
  (ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter
   ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyCardinalityAfter
   ResidueSharedPrimeWitnessFilteredCoverCardinalityTailAfter
   ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter
   ResidueSharedPrimeWitnessFilteredCoverTailDecompositionAfter
   residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_cardinalityTail
   residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_tailDecomposition)
open Gdbh.PathCResidueRemainderWitnessCoverFilteredTermwise
  (ResidueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter
   residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_pairRemainderEnvelope
   residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_of_pairRemainderEnvelope)
open Gdbh.PathCResiduePairDivisorSharpEnvelope
  (residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two)

/-! ## Constant-2 termwise closure -/

/-- The Round 90 sharp CRT interval discrepancy closes the Round 87 uniform
shared-prime remainder input with the constant envelope `R n = 2`. -/
theorem residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_two
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverUniformRemainderAfter
      N (fun _ => (2 : ℝ)) :=
  residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_of_pairRemainderEnvelope
    (residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two N)

/-- Bundled termwise decomposition with the constant envelope `R n = 2`. -/
theorem residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_two
    (N : ℕ) :
    ResidueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter
      N (fun _ => (2 : ℝ)) :=
  residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_of_pairRemainderEnvelope
    (residueSharedPrimeWitnessFilteredCoverPairRemainderEnvelopeAfter_two N)

/-! ## Residual scalar tail -/

/-- The remaining scalar cardinal-tail inequality after the constant-2
termwise closure has been inserted. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverTwoCardinalityTailAfter
    (N : ℕ) (Cw Cd : ℕ → ℝ) (A : ℝ) : Prop :=
  ResidueSharedPrimeWitnessFilteredCoverCardinalityTailAfter
    N (fun _ => (2 : ℝ)) Cw Cd A

/-- Round 91 residual after closing the termwise filtered-cover remainder:
only cardinality control and the scalar constant-2 tail remain. -/
noncomputable def
    ResidueSharedPrimeWitnessFilteredCoverSharpTailResidualAfter
    (N : ℕ) (Cw Cd : ℕ → ℝ) (A : ℝ) : Prop :=
  ResidueSharedPrimeWitnessFilteredCoverDivisorFamilyCardinalityAfter N Cw Cd ∧
    ResidueSharedPrimeWitnessFilteredCoverTwoCardinalityTailAfter N Cw Cd A

/-- The sharp residual supplies the full Round 87 tail decomposition with
`R n = 2`. -/
theorem
    residueSharedPrimeWitnessFilteredCoverTailDecompositionAfter_two_of_sharpTailResidual
    {N : ℕ} {Cw Cd : ℕ → ℝ} {A : ℝ}
    (hResidual :
      ResidueSharedPrimeWitnessFilteredCoverSharpTailResidualAfter N Cw Cd A) :
    ResidueSharedPrimeWitnessFilteredCoverTailDecompositionAfter
      N (fun _ => (2 : ℝ)) Cw Cd A := by
  rcases hResidual with ⟨hCard, hTail⟩
  exact
    ⟨residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_two N,
      hCard, hTail⟩

/-- The sharp residual supplies the weighted-prime tail estimate with
`R n = 2`. -/
theorem
    residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_sharpTailResidual
    {N : ℕ} {Cw Cd : ℕ → ℝ} {A : ℝ}
    (hResidual :
      ResidueSharedPrimeWitnessFilteredCoverSharpTailResidualAfter N Cw Cd A) :
    ResidueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter
      N (fun _ => (2 : ℝ)) A :=
  residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_cardinalityTail
    (fun _n _hn _hsqrt => by norm_num)
    hResidual.1 hResidual.2

/-- The sharp residual is enough for the existing filtered-cover
log-squared worker. -/
theorem
    residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_sharpTailResidual
    {N : ℕ} {Cw Cd : ℕ → ℝ} {A : ℝ}
    (hResidual :
      ResidueSharedPrimeWitnessFilteredCoverSharpTailResidualAfter N Cw Cd A) :
    ResidueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter N A :=
  residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_tailDecomposition
    (residueSharedPrimeWitnessFilteredCoverTailDecompositionAfter_two_of_sharpTailResidual
      hResidual)

end PathCResidueRemainderWitnessCoverFilteredSharpTail
end Gdbh

#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredSharpTail.residueSharedPrimeWitnessFilteredCoverUniformRemainderAfter_two
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredSharpTail.residueSharedPrimeWitnessFilteredCoverTermwiseDecompositionAfter_two
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredSharpTail.residueSharedPrimeWitnessFilteredCoverTailDecompositionAfter_two_of_sharpTailResidual
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredSharpTail.residueSharedPrimeWitnessFilteredCoverWeightedPrimeTailAfter_of_sharpTailResidual
#print axioms
  Gdbh.PathCResidueRemainderWitnessCoverFilteredSharpTail.residueSharedPrimeWitnessFilteredCoverLogSquaredUpperAfter_of_sharpTailResidual
