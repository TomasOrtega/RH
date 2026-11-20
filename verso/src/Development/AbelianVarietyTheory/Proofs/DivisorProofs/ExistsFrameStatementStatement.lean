import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetHT.exFrameSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFrameStatement.lean&line=251#L251)
-/
theorem _root_.GlobalTheory.T.ExistsFrameStatement : ExFrameSt := by
  first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)
