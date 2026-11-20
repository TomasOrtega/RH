import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagStatementHolds.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.flag_statement_holds : FlagSt := by
  first | exact @GlobalTheory.DetHT.FlagNorm.flagSt_holds | exact GlobalTheory.DetHT.FlagNorm.flagSt_holds | (intros; apply GlobalTheory.DetHT.FlagNorm.flagSt_holds <;> assumption)
