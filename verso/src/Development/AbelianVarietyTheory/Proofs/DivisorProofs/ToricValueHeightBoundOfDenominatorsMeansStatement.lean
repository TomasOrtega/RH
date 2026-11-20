import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqTop.thbSt_of_inputs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FToricValueHeightBoundOfDenominatorsMeans.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  first | exact @GlobalTheory.SqTop.thbSt_of_inputs | exact GlobalTheory.SqTop.thbSt_of_inputs | (intros; apply GlobalTheory.SqTop.thbSt_of_inputs <;> assumption)
