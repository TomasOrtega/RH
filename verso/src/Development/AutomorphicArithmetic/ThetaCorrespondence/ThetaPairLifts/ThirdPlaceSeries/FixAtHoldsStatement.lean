import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixAtHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FFixAtHolds.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.twisted_conj_fix_at' : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt <;> assumption)
end
