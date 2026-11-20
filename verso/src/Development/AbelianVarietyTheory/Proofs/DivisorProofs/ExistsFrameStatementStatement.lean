import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.ExistsFrameStatement : ExFrameSt := by
  first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)
