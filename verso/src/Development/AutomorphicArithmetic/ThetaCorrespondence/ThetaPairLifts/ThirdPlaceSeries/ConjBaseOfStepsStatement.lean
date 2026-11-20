import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfSteps

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FConjBaseOfSteps.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | exact _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity <;> assumption)
end
