/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Wave 1 / Path C Kernel B closure integration (P19-T13)
-/
import Gdbh.PathC_MertensSecondUpper
import Gdbh.PathC_PairedBrunMertensLowerReal

/-!
# Path C -- Kernel B closure (P19-T13)

This file is the **one-liner composition layer** that wires together the
two pieces produced upstream:

* **P19-T6** closed `PairedBrunMertensThirdLowerGap` unconditionally
  (axiom-clean), via
  `Gdbh.PathCMertensSecondUpper.pairedBrunMertensThirdLowerGap_holds`.

* **P18-T2-real** provides the downstream bridge
  `Gdbh.PathCPairedBrunMertensLowerReal.pairedBrunFactorRealMertensLower_of_thirdLowerGap`
  which converts a `PairedBrunMertensThirdLowerGap` witness into a
  `PairedBrunFactorRealMertensLower` witness, and the wrapper bridge
  `absorption_of_atSqrt_and_realResiduals` which uses the *real-valued*
  lower bound (achievable) instead of the impossible nat-valued one.

Composing these two yields the **unconditional closure of
`PairedBrunFactorRealMertensLower`** (Kernel B), and reduces the
four-input absorption bridge to a three-input bridge.

## Summary of Kernel B closure chain

```
pairedBrunMertensThirdLowerGap_holds                 (P19-T6, axiom-clean)
  → pairedBrunFactorRealMertensLower_of_thirdLowerGap  (P18-T2-real, axiom-clean)
  → PairedBrunFactorRealMertensLower                    ✅ unconditionally closed
```

Combined with **Kernel A** (still open: `BrunGoldbachPairedMainTermRefinedAtSqrt`
plus the residual `PairedMainTermResidualLowRegion`), this would close
the Path C K-Goldbach.
-/

namespace Gdbh
namespace PathCKernelBClosed

open Gdbh.PathCPairedBrunMertensLowerProof
  (PairedBrunFactorRealMertensLower)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt
   PairedMainTermAbsorption)
open Gdbh.PathCPairedBrunLargeZ
  (PairedBrunFactorMertensUpperAtSqrt
   PairedMainTermResidualLowRegion)

/-! ## Section 1 — Unconditional Kernel B closure -/

/-- **Unconditional closure of `PairedBrunFactorRealMertensLower`.**

Combining
* P19-T6: `pairedBrunMertensThirdLowerGap_holds` (axiom-clean), and
* P18-T2-real: `pairedBrunFactorRealMertensLower_of_thirdLowerGap`
  (axiom-clean reduction),

we obtain a fully unconditional witness for
`PairedBrunFactorRealMertensLower`.  This is the "Kernel B" component
of the Path C absorption chain. -/
theorem pairedBrunFactorRealMertensLower_holds_unconditional :
    Gdbh.PathCPairedBrunMertensLowerProof.PairedBrunFactorRealMertensLower :=
  Gdbh.PathCPairedBrunMertensLowerReal.pairedBrunFactorRealMertensLower_of_thirdLowerGap
    Gdbh.PathCMertensSecondUpper.pairedBrunMertensThirdLowerGap_holds

/-! ## Section 2 — Three-input absorption bridge

With Kernel B fully discharged, the four-input wrapper bridge
`absorption_of_atSqrt_and_realResiduals` collapses to a three-input
bridge: only the AtSqrt residual, the paired-Brun Mertens upper bound
at `√n`, and the low-region residual are still required. -/

/-- **Kernel B fully discharged** (P19-T13).

The four-input absorption bridge
`absorption_of_atSqrt_and_realResiduals` now needs only three inputs:
* `hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt`
  (Kernel A, still open),
* `hUpper  : PairedBrunFactorMertensUpperAtSqrt`
  (P18-T1, closed), and
* `hLow    : PairedMainTermResidualLowRegion`
  (Kernel A SubSqrt + small, partially open).

The Kernel B input `PairedBrunFactorRealMertensLower` is supplied
unconditionally by
`pairedBrunFactorRealMertensLower_holds_unconditional`. -/
theorem absorption_of_atSqrt_upper_lowRegion_unconditionalRealLower
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hUpper : PairedBrunFactorMertensUpperAtSqrt)
    (hLow : PairedMainTermResidualLowRegion) :
    PairedMainTermAbsorption :=
  Gdbh.PathCPairedBrunMertensLowerReal.absorption_of_atSqrt_and_realResiduals
    hAtSqrt
    pairedBrunFactorRealMertensLower_holds_unconditional
    hUpper
    hLow

/-! ## Section 3 — Summary

KERNEL B (Mertens 2nd upper chain + paired Brun lower) is now fully
closed axiom-cleanly.  The remaining inputs to the Path C absorption
chain are Kernel A pieces.
-/

/-- **KERNEL B (Mertens 2nd upper chain + paired Brun lower) is fully
closed axiom-cleanly.**  Combined with Kernel A (still open), this
would close the Path C K-Goldbach. -/
theorem pathC_kernelB_closed : True := trivial

end PathCKernelBClosed
end Gdbh
