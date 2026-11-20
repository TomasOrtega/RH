import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOfStatement

set_option synthInstance.maxHeartbeats 200000

section
/- English proof (citation)
Apply `GlobalTheory.T.aut_statement_of_small_exponent_statement` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FAutAtOfStatement.lean&line=11#L11)
-/
theorem GlobalTheory.FrameAut.frame_autSt_of_smallSt : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement
end
