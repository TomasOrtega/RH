import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FlatModel.Proj.projSt | exact GlobalTheory.FlatModel.Proj.projSt | (intros; apply GlobalTheory.FlatModel.Proj.projSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.projection_statement_holds : ProjSt := by
  first | exact @GlobalTheory.FlatModel.Proj.projSt | exact GlobalTheory.FlatModel.Proj.projSt | (intros; apply GlobalTheory.FlatModel.Proj.projSt <;> assumption)
