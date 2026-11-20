import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTraceEPowerHighestWeightValueGeneratingSeries.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.traceEPowerHighestWeightValue_generating_series : ∀ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R), (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) = ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.Alc.hcVal_generating | exact GlobalTheory.Alc.hcVal_generating | (intros; apply GlobalTheory.Alc.hcVal_generating <;> assumption)
