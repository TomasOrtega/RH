import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtAltAlt

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSizeAtAltAlt.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt <;> assumption)
end
