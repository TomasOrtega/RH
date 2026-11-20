import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSize

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSettingOfSize.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt <;> assumption)
end
