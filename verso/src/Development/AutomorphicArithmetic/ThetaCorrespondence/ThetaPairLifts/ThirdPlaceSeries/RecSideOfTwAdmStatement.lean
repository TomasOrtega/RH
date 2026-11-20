import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideOfTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdm

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FRecSideOfTwAdm.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.reciprocity_side_of_twAdm : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt <;> assumption)
end
