import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_Final
import Gdbh.PathC_SingularCountingInterface

namespace Gdbh
namespace PathCFinalClosedReductions

open Gdbh.PathCBrunRefinedComposition (BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCClosedReductions (goldbachRepresentationBound_of_refined_main)
open Gdbh.PathCGoldbachResidues
  (BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError
   GoldbachResidueErrorBoundedByRefinedAtSqrt
   GoldbachResidueSiftedAtSqrtBoundedErrorData)
open Gdbh.PathCSingularCountingInterface
  (PathCAtSqrtSplitCountingData PathCCountingInput PathCFiniteSieveInput
   PathCUnifiedInputData
   pathC_kGoldbach_of_atSqrt_split_counting_data
   pathC_kGoldbach_of_finiteSieveInput_and_countingInput
   pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
   pathC_kGoldbach_of_unified_input_data)

/-! ## Corrected singular-factor final adapter -/

/-- Corrected Path C final team content.

The finite-sieve worker supplies any supported corrected local/singular-factor
finite-sieve input; the counting worker supplies any supported counting bridge.
This is the final-layer adapter for the honest `n`-dependent Goldbach local
factor route, avoiding the older uniform `GoldbachRepresentationBound`
handoff. -/
structure PathC_CorrectedSingularTeamContent where
  finiteSieve : PathCFiniteSieveInput
  counting : PathCCountingInput

/-- Corrected Path C final team content for the raw split at-sqrt finite-sieve
handoff.

This is the shape produced when the finite-sieve work is split into one worker
for the at-sqrt sifted upper bound and another worker for domination of the
error term by the refined reservoir. -/
structure PathC_CorrectedSingularAtSqrtRawTeamContent where
  B : ℕ → ℕ → ℝ
  upperBound : BrunGoldbachResidueSiftedUpperBoundAtSqrtWithError B
  errorBound : GoldbachResidueErrorBoundedByRefinedAtSqrt B
  counting : PathCCountingInput

/-- Corrected Path C final team content after the split finite-sieve workers
have been integrated into the at-sqrt bounded-error data bundle. -/
structure PathC_CorrectedSingularAtSqrtDataTeamContent where
  finiteSieve : GoldbachResidueSiftedAtSqrtBoundedErrorData
  counting : PathCCountingInput

/-- Final Path C headline from the corrected singular-factor unified input
data bundle. -/
theorem pathC_kGoldbach_of_corrected_singular_unified_input_data
    (data : PathCUnifiedInputData) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_unified_input_data data

/-- Final Path C headline from corrected singular-factor team content. -/
theorem pathC_kGoldbach_of_corrected_singular_team_content
    (content : PathC_CorrectedSingularTeamContent) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_finiteSieveInput_and_countingInput
    content.finiteSieve content.counting

/-- Final Path C headline from raw split at-sqrt corrected singular-factor
team content. -/
theorem pathC_kGoldbach_of_corrected_singular_atSqrt_raw_team_content
    (content : PathC_CorrectedSingularAtSqrtRawTeamContent) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_residue_sifted_atSqrt_error_bound_and_countingInput
    content.upperBound content.errorBound content.counting

/-- Final Path C headline from the at-sqrt bounded-error finite-sieve data
bundle plus any supported counting worker output. -/
theorem pathC_kGoldbach_of_corrected_singular_atSqrt_data_and_countingInput
    (data : GoldbachResidueSiftedAtSqrtBoundedErrorData)
    (hCounting : PathCCountingInput) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_atSqrt_split_counting_data
    { finiteSieve := data, counting := hCounting }

/-- Final Path C headline from corrected singular-factor at-sqrt data team
content. -/
theorem pathC_kGoldbach_of_corrected_singular_atSqrt_data_team_content
    (content : PathC_CorrectedSingularAtSqrtDataTeamContent) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  pathC_kGoldbach_of_corrected_singular_atSqrt_data_and_countingInput
    content.finiteSieve content.counting

/-- Current Path C headline from the single remaining refined Brun main-term
input.  This is a connector theorem: the Abel/Mertens side is already closed
in `PathC_ClosedReductions`, and `PathC_Final` consumes only
`GoldbachRepresentationBound` at Phase 10. -/
theorem pathC_kGoldbach_of_refined_main
    (hMain : BrunGoldbachPairedMainTermRefined) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ ps : List ℕ, ps.length ≤ K ∧
        (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n :=
  Gdbh.PathCFinal.pathC_kGoldbach_phase10_reduced
    { goldbachRepresentationBound := goldbachRepresentationBound_of_refined_main hMain }

end PathCFinalClosedReductions
end Gdbh
