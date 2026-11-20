import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallBoundTupleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefSt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FCoefSt.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.tuple_coef_le : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt <;> assumption)
end
