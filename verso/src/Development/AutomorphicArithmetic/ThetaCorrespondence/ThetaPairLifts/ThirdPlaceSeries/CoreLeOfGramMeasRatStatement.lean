import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasureStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreLeOfGramMeasRat

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FCoreLeOfGramMeasRat.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  first | exact @_root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt | exact _root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt | (intros; apply _root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt <;> assumption)
end
