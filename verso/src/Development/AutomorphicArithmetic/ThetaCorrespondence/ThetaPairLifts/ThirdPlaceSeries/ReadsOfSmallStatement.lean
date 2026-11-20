import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsAtSmallPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmall

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameRead.reads_of_small_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FReadsOfSmall.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.readsAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  first | exact @_root_.GlobalTheory.FrameRead.reads_of_small_alt | exact _root_.GlobalTheory.FrameRead.reads_of_small_alt | (intros; apply _root_.GlobalTheory.FrameRead.reads_of_small_alt <;> assumption)
end
