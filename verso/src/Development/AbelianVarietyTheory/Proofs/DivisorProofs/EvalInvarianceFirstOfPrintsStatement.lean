import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEvalInvarianceFirstOfHyp.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.eval_invariance_first_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.EvInvA := by
  first | exact @GlobalTheory.ThK.EvInvALoc.evInvA | exact GlobalTheory.ThK.EvInvALoc.evInvA | (intros; apply GlobalTheory.ThK.EvInvALoc.evInvA <;> assumption)
