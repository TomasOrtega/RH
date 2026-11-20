import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsEstimateStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRunsAt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExistsRunsAt.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.runs_estimate_statement' : _root_.GlobalTheory.BigOn.TwoRunsStatement := by
  first | exact @_root_.GlobalTheory.BigOn.bigOn_runsSt | exact _root_.GlobalTheory.BigOn.bigOn_runsSt | (intros; apply _root_.GlobalTheory.BigOn.bigOn_runsSt <;> assumption)
end
