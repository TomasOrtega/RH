import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.genFun_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLengthCountGeneratingSeriesFormula.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.length_count_generating_series_formula : GenFun := by
  first | exact @GlobalTheory.InertZeta.genFun_holds | exact GlobalTheory.InertZeta.genFun_holds | (intros; apply GlobalTheory.InertZeta.genFun_holds <;> assumption)
