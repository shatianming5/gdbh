/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Wave 1 / Path C closure integration
-/
import Gdbh.PathC_VonMangoldtAsymptotic
import Gdbh.PathC_VonMangoldtDivisorIdentity
import Gdbh.PathC_LogFactorialStirling
import Gdbh.PathC_PrimePowerTail

/-!
# Path C -- Mertens first theorem closure

This file is a small integration layer: the component proofs for the
von Mangoldt identity, Stirling bound, and prime-power tail have already
been proved in separate files.  We compose them into the original
`MertensFirstTheoremBound` interface.
-/

namespace Gdbh
namespace PathCMertensFirstClosure

open Gdbh.PathCMertensSecondProof (MertensFirstTheoremBound)

/-- Mertens' first theorem bound, assembled from the already closed
von Mangoldt, Stirling, and prime-power-tail components. -/
theorem mertensFirstTheoremBound_holds : MertensFirstTheoremBound :=
  Gdbh.PathCVonMangoldtAsymptotic.mertensFirstTheoremBound_via_vonMangoldt_components
    Gdbh.PathCVonMangoldtDivisorIdentity.logFactorialVonMangoldtIdentity_holds
    Gdbh.PathCLogFactorialStirling.logFactorialStirlingBound_holds
    Gdbh.PathCPrimePowerTail.primePowerTailBound

end PathCMertensFirstClosure
end Gdbh
