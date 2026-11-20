import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.levelSq_yBound_atRec_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FLevelSqYBoundAtRec.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.leafLevelSq_and_leafYBound : _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @_root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | exact _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | (intros; apply _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt <;> assumption)
end
