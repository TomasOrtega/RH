import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagPushProof.flagPushForward` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullFlagBundlePushForwardFormula.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  first | exact @GlobalTheory.FlagPushProof.flagPushForward | exact GlobalTheory.FlagPushProof.flagPushForward | (intros; apply GlobalTheory.FlagPushProof.flagPushForward <;> assumption)
