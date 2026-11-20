import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseGeOfSteps

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.baseGe_of_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FBaseGeOfSteps.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.baseGe_of_alt | exact _root_.GlobalTheory.BigOn.Exp.baseGe_of_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.baseGe_of_alt <;> assumption)
end
