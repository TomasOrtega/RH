import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsEstimateStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRunsEstimateStatement.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.runs_estimate_statement : RunsSt := by
  first | exact @GlobalTheory.BigOn.runsSt | exact GlobalTheory.BigOn.runsSt | (intros; apply GlobalTheory.BigOn.runsSt <;> assumption)
