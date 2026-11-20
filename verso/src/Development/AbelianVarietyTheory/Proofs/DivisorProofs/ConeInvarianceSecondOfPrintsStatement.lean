import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeInvarianceSecondOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ThK.LemF.coneInvB | exact GlobalTheory.ThK.LemF.coneInvB | (intros; apply GlobalTheory.ThK.LemF.coneInvB <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cone_invariance_second_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.ConeInvB := by
  first | exact @GlobalTheory.ThK.LemF.coneInvB | exact GlobalTheory.ThK.LemF.coneInvB | (intros; apply GlobalTheory.ThK.LemF.coneInvB <;> assumption)
