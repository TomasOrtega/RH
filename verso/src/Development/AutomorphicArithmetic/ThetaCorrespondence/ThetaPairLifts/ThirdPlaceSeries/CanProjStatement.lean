import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjectionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProj

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.canProj_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FCanProj.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.bigOn_canProj : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.canProj_alt | exact _root_.GlobalTheory.BigOn.Exp.canProj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.canProj_alt <;> assumption)
end
