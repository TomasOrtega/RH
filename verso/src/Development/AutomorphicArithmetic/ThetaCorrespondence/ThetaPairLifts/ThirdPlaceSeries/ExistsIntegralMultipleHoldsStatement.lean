import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHolds

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExistsIntegralMultipleHolds.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.scaling_function_bound' : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | exact _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt <;> assumption)
end
