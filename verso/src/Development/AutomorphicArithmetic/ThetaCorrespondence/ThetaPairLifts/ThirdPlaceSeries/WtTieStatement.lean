import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTie

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.BigTop.Fun.wt_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.wt_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.wt_tie_alt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weight_of_size_bound' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.LeafWeightBound @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.wt_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.wt_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.wt_tie_alt <;> assumption)
end
