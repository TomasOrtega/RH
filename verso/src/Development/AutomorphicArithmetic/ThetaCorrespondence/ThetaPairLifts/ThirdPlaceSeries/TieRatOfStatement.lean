import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRowStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOf

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FTieRatOf.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.tieRat_of_twAdm_and_at : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace → _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | exact _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt <;> assumption)
end
