import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaNonvanishing.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.theta_nonvanishing : GlobalTheory.ThK.KP → GlobalTheory.ThK.NonZero := by
  first | exact @GlobalTheory.ThKNZ.nonZero | exact GlobalTheory.ThKNZ.nonZero | (intros; apply GlobalTheory.ThKNZ.nonZero <;> assumption)
