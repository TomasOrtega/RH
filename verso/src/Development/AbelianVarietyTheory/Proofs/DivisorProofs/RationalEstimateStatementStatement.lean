import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.ratSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalEstimateStatement.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.rational_estimate_statement : RatSt := by
  first | exact @GlobalTheory.BigOn.ratSt | exact GlobalTheory.BigOn.ratSt | (intros; apply GlobalTheory.BigOn.ratSt <;> assumption)
