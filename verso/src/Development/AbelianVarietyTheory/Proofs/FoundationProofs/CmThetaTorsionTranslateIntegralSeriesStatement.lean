import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmThetaTorsionTranslateIntegralSeries.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.cm_theta_torsion_translate_integral_series : ∀ D : D7, GL3Theta.transl D := by
  first | exact @GlobalTheory.ThetaTransl.transl_holds | exact GlobalTheory.ThetaTransl.transl_holds | (intros; apply GlobalTheory.ThetaTransl.transl_holds <;> assumption)
