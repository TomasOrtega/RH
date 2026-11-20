import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionStatementHolds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GradedLines.statement` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGoodReductionStatementHolds.lean&line=220#L220)
-/
theorem _root_.GlobalTheory.T.good_reduction_statement_holds : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.Statement := by
  first | exact @GlobalTheory.GradedLines.statement | exact GlobalTheory.GradedLines.statement | (intros; apply GlobalTheory.GradedLines.statement <;> assumption)
