import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLineStatement

namespace GlobalTheory.RowReal

open GlobalTheory.RowClaim

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem realLine : Big fun ch => RealLine ch :=
  big_mono (fun ch h => realLine_of_periodsOnLine ch h) GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine

end GlobalTheory.RowReal
