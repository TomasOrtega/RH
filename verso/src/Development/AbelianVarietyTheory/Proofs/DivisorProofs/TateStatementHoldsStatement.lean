import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.tateSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTateStatementHolds.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.tate_statement_holds : TateSt := by
  first | exact @GlobalTheory.FlatModel.tateSt | exact GlobalTheory.FlatModel.tateSt | (intros; apply GlobalTheory.FlatModel.tateSt <;> assumption)
