import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.Proj.projSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectionStatementHolds.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.projection_statement_holds : ProjSt := by
  first | exact @GlobalTheory.FlatModel.Proj.projSt | exact GlobalTheory.FlatModel.Proj.projSt | (intros; apply GlobalTheory.FlatModel.Proj.projSt <;> assumption)
