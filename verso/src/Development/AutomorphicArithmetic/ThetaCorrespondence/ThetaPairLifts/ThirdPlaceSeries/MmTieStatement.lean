import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTie

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FMmTie.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.leafMinimalMass_of_setAt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt <;> assumption)
end
