import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTie

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FIpaTie.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.leafHeightMapBound_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  first | exact @_root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | exact _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | (intros; apply _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK <;> assumption)
end
