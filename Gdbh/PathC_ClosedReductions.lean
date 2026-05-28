import Gdbh.PathC_AbelIntegrandSplit
import Gdbh.PathC_AbelPrimeRecipIdentity
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_LogRecipIntegral
import Gdbh.PathC_MertensErrorIntegral
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_SmallSieveSideCondition

namespace Gdbh
namespace PathCClosedReductions

open Gdbh.PathCAbelInversion
open Gdbh.PathCAbelPrimeRecipIdentity
open Gdbh.PathCAbelIntegrandSplit
open Gdbh.PathCBrunRefinedComposition
open Gdbh.PathCLogRecipIntegral
open Gdbh.PathCMertensErrorIntegral
open Gdbh.PathCMertensSecondProof (AbelInversionMertensSecondFromFirst)
open Gdbh.PathCMertensFirstClosure
open Gdbh.PathCSmallSieveSideCondition

/-- Once the remaining Mertens-error integral is closed, Abel inversion is
fully closed from the already-proved identity, log-integral, and split
components. -/
theorem abelInversionMertensSecondFromFirst_of_mertensErrorIntegralBound
    (hErr : MertensErrorIntegralBound) :
    AbelInversionMertensSecondFromFirst :=
  abelInversionMertensSecondFromFirst_of_components
    abelPrimeReciprocalIdentity
    logReciprocalIntegralAsymptotic_closed
    hErr
    abelIntegrandSplit_holds

/-- Abel inversion is now closed unconditionally from the already formalized
Abel identity, log-integral asymptotic, Mertens-error integral bound, and
integrand split. -/
theorem abelInversionMertensSecondFromFirst_holds :
    AbelInversionMertensSecondFromFirst :=
  abelInversionMertensSecondFromFirst_of_mertensErrorIntegralBound
    mertensErrorIntegralBound_holds

/-- Current refined Path C reduction after the Wave 1 closures: the remaining
inputs are the Brun/Halberstam-Richert main term and Abel inversion. -/
theorem goldbachRepresentationBound_of_refined_main_and_abel
    (hMain : BrunGoldbachPairedMainTermRefined)
    (hAbel : AbelInversionMertensSecondFromFirst) :
    Gdbh.PathCTwinAsymptotic.GoldbachRepresentationBound :=
  goldbachRepresentationBound_of_refined_coordinated
    hMain
    mertensFirstTheoremBound_holds
    hAbel
    smallSieveSideCondition_holds

/-- Current refined Path C reduction after the Wave 1 closures, expressed with
the Abel error integral as the only non-Brun input. -/
theorem goldbachRepresentationBound_of_refined_main_and_mertensError
    (hMain : BrunGoldbachPairedMainTermRefined)
    (hErr : MertensErrorIntegralBound) :
    Gdbh.PathCTwinAsymptotic.GoldbachRepresentationBound :=
  goldbachRepresentationBound_of_refined_main_and_abel hMain
    (abelInversionMertensSecondFromFirst_of_mertensErrorIntegralBound hErr)

/-- After the Abel-side closures, the refined Brun/Halberstam-Richert main
term is the only remaining input needed for the current `GoldbachRepresentationBound`
interface. -/
theorem goldbachRepresentationBound_of_refined_main
    (hMain : BrunGoldbachPairedMainTermRefined) :
    Gdbh.PathCTwinAsymptotic.GoldbachRepresentationBound :=
  goldbachRepresentationBound_of_refined_main_and_abel hMain
    abelInversionMertensSecondFromFirst_holds

end PathCClosedReductions
end Gdbh
