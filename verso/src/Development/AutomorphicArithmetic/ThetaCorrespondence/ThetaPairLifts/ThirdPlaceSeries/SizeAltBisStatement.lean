import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBis

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSizeAltBis.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.cov_size_bound : _root_.GlobalTheory.CovTop.SizeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | exact _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | (intros; apply _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis <;> assumption)
end
