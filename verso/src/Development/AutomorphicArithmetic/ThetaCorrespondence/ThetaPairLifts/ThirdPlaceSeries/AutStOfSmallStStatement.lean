import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutStOfSmallSt

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FAutStOfSmallSt.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.frame_aut_of_small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  first | exact @_root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt | exact _root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt | (intros; apply _root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt <;> assumption)
end
