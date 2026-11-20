import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecursionOfGramBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.liftRecursive_of_gram` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FRecAtOfGramAt.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.lift_recursion_of_gram_bound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := by
  first | exact @_root_.GlobalTheory.CovTop.liftRecursive_of_gram | exact _root_.GlobalTheory.CovTop.liftRecursive_of_gram | (intros; apply _root_.GlobalTheory.CovTop.liftRecursive_of_gram <;> assumption)
end
