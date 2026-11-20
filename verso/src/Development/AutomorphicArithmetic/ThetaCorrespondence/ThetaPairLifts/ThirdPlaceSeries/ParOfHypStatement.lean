import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHyp

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExpTie.parOf_hyp_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FParOfHyp.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.parOf_hyp_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @_root_.GlobalTheory.ExpTie.parOf_hyp_alt | exact _root_.GlobalTheory.ExpTie.parOf_hyp_alt | (intros; apply _root_.GlobalTheory.ExpTie.parOf_hyp_alt <;> assumption)
end
