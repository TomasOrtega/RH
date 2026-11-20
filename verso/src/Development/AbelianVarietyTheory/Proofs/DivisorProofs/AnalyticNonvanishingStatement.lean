import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.analytic_nonvanishing : GlobalTheory.ThK.KP → GlobalTheory.ThK.NonZeroAn := by
  first | exact @GlobalTheory.ThKNonZero.nonZeroAn | exact GlobalTheory.ThKNonZero.nonZeroAn | (intros; apply GlobalTheory.ThKNonZero.nonZeroAn <;> assumption)
