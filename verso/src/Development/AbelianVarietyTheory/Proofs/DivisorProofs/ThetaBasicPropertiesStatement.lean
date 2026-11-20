import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThKBasic.thetaBasic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaBasicProperties.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.theta_basic_properties : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  first | exact @GlobalTheory.ThKBasic.thetaBasic | exact GlobalTheory.ThKBasic.thetaBasic | (intros; apply GlobalTheory.ThKBasic.thetaBasic <;> assumption)
