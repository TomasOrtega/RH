import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaFacMain.factor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaFactorization.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.theta_factorization : GlobalTheory.ThK.KP → GlobalTheory.ThK.Factor := by
  first | exact @GlobalTheory.ThetaFacMain.factor | exact GlobalTheory.ThetaFacMain.factor | (intros; apply GlobalTheory.ThetaFacMain.factor <;> assumption)
