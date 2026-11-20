import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeries

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExistsSeries.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | exact _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | (intros; apply _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field <;> assumption)
end
