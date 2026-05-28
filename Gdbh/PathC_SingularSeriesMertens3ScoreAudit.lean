/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Codex Round 2 controller
-/
import Gdbh.PathC_BrunGoldbachSingularSeries
import Gdbh.PathC_SingularSeriesPointwiseBound

/-!
# Path C — score audit for `SingularSeriesMertens3Bound`

This file records, in Lean, the exact shape of the current
`SingularSeriesMertens3Bound` residual.  It is definitionally the same as the
generic pointwise Mertens bound on `singularSeries`.

This does not close the residual.  Its purpose is queue control for the
master-controller workflow: any future task trying to close this residual must
first account for the project false-prop notes around pointwise singular-series
`log log` bounds.
-/

namespace Gdbh
namespace PathCSingularSeriesMertens3ScoreAudit

open Gdbh.PathCBrunGoldbachSingularSeries
  (SingularSeriesMertens3Bound)
open Gdbh.PathCHardyLittlewoodForm
  (singularSeries)
open Gdbh.PathCSingularSeriesPointwiseBound
  (SingularSeriesMertensBound)

/-- The Phase 29 `SingularSeriesMertens3Bound` is exactly the generic
pointwise Mertens bound specialised to the Goldbach singular series. -/
theorem singularSeriesMertens3Bound_iff_pointwiseMertensBound :
    SingularSeriesMertens3Bound ↔
      SingularSeriesMertensBound singularSeries :=
  Iff.rfl

/-- Forward spelling of the definitional equivalence. -/
theorem pointwiseMertensBound_of_singularSeriesMertens3Bound
    (h : SingularSeriesMertens3Bound) :
    SingularSeriesMertensBound singularSeries :=
  singularSeriesMertens3Bound_iff_pointwiseMertensBound.mp h

/-- Reverse spelling of the definitional equivalence. -/
theorem singularSeriesMertens3Bound_of_pointwiseMertensBound
    (h : SingularSeriesMertensBound singularSeries) :
    SingularSeriesMertens3Bound :=
  singularSeriesMertens3Bound_iff_pointwiseMertensBound.mpr h

end PathCSingularSeriesMertens3ScoreAudit
end Gdbh

#print axioms
  Gdbh.PathCSingularSeriesMertens3ScoreAudit.singularSeriesMertens3Bound_iff_pointwiseMertensBound
#print axioms
  Gdbh.PathCSingularSeriesMertens3ScoreAudit.pointwiseMertensBound_of_singularSeriesMertens3Bound
#print axioms
  Gdbh.PathCSingularSeriesMertens3ScoreAudit.singularSeriesMertens3Bound_of_pointwiseMertensBound
