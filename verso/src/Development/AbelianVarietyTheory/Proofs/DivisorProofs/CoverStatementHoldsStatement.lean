import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.coverSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoverStatementHolds.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.cover_statement_holds : CoverSt := by
  first | exact @GlobalTheory.FlatModel.coverSt_holds | exact GlobalTheory.FlatModel.coverSt_holds | (intros; apply GlobalTheory.FlatModel.coverSt_holds <;> assumption)
