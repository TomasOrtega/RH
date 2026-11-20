import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ThKNZ.nonZero | exact GlobalTheory.ThKNZ.nonZero | (intros; apply GlobalTheory.ThKNZ.nonZero <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_nonvanishing : GlobalTheory.ThK.KP → GlobalTheory.ThK.NonZero := by
  first | exact @GlobalTheory.ThKNZ.nonZero | exact GlobalTheory.ThKNZ.nonZero | (intros; apply GlobalTheory.ThKNZ.nonZero <;> assumption)
