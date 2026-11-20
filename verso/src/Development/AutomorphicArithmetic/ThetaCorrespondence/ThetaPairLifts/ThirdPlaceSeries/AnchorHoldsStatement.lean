import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.anchor_holds_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FAnchorHolds.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  first | exact @_root_.GlobalTheory.CovTop.anchor_holds_alt | exact _root_.GlobalTheory.CovTop.anchor_holds_alt | (intros; apply _root_.GlobalTheory.CovTop.anchor_holds_alt <;> assumption)
end
