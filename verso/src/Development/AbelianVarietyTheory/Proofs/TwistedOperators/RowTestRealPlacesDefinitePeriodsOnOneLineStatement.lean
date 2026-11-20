import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowReal.periodsOnLine_big` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRowTestRealPlacesDefinitePeriodsOnOneLine.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine : Big fun ch => PeriodsOnLine ch := by
  first | exact @GlobalTheory.RowReal.periodsOnLine_big | exact GlobalTheory.RowReal.periodsOnLine_big | (intros; apply GlobalTheory.RowReal.periodsOnLine_big <;> assumption)
