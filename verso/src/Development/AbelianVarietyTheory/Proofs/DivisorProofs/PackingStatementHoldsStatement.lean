import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.packSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPackingStatementHolds.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.packing_statement_holds : PackSt := by
  first | exact @GlobalTheory.FlatModel.packSt | exact GlobalTheory.FlatModel.packSt | (intros; apply GlobalTheory.FlatModel.packSt <;> assumption)
