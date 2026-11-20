import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.densSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDensityStatementHolds.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.density_statement_holds : DensSt := by
  first | exact @GlobalTheory.FlatModel.densSt | exact GlobalTheory.FlatModel.densSt | (intros; apply GlobalTheory.FlatModel.densSt <;> assumption)
