import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.EigDiff.eigSt_holds | exact GlobalTheory.EigDiff.eigSt_holds | (intros; apply GlobalTheory.EigDiff.eigSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.EigenvalueStatement : EigSt := by
  first | exact @GlobalTheory.EigDiff.eigSt_holds | exact GlobalTheory.EigDiff.eigSt_holds | (intros; apply GlobalTheory.EigDiff.eigSt_holds <;> assumption)
