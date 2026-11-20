import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSizeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSize

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.NumSizes.numPt_of_size'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FNumPtOfSize.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.numerical_point_statement_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | exact _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | (intros; apply _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' <;> assumption)
end
