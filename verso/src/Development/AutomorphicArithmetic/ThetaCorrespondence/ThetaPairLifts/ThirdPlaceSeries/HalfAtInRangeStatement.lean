import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRange

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfLabels.halfAt_inRange_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FHalfAtInRange.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.inRange_halfAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  first | exact @_root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | exact _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | (intros; apply _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt <;> assumption)
end
