import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaModelChange.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.theta_model_change : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ModelChange := by
  first | exact @GlobalTheory.ModelChg.modelChange | exact GlobalTheory.ModelChg.modelChange | (intros; apply GlobalTheory.ModelChg.modelChange <;> assumption)
