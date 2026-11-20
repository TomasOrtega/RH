import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGoodStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGood

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.sumC_of_deepGood_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSumCOfDeepGood.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sum_c_of_deep_good : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := by
  first | exact @_root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | exact _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | (intros; apply _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt <;> assumption)
end
