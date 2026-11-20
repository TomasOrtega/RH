import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtCompStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FTwAdm.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.twist_admissible' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twAdm_alt <;> assumption)
end
