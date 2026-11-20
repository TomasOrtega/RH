import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DetHT.FlagNorm.flagSt_holds | exact GlobalTheory.DetHT.FlagNorm.flagSt_holds | (intros; apply GlobalTheory.DetHT.FlagNorm.flagSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flag_statement_holds : FlagSt := by
  first | exact @GlobalTheory.DetHT.FlagNorm.flagSt_holds | exact GlobalTheory.DetHT.FlagNorm.flagSt_holds | (intros; apply GlobalTheory.DetHT.FlagNorm.flagSt_holds <;> assumption)
