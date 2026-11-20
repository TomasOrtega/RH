import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLatticesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSmallStAltBis.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.small_tuple_statement_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.SmallSpan.smallSt_alt | exact _root_.GlobalTheory.SmallSpan.smallSt_alt | (intros; apply _root_.GlobalTheory.SmallSpan.smallSt_alt <;> assumption)
end
