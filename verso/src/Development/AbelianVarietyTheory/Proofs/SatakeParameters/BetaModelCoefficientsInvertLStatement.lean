import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BeCoefficients.beCoef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FBetaModelCoefficientsInvertL.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  first | exact @GlobalTheory.BeCoefficients.beCoef | exact GlobalTheory.BeCoefficients.beCoef | (intros; apply GlobalTheory.BeCoefficients.beCoef <;> assumption)
