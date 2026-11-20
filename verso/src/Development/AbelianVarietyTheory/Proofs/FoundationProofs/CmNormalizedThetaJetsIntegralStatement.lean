import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaJets.jetsPh_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmNormalizedThetaJetsIntegral.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.cm_normalized_theta_jets_integral : ∀ D : D7, GL3Theta.jetsPh D := by
  first | exact @GlobalTheory.ThetaJets.jetsPh_all | exact GlobalTheory.ThetaJets.jetsPh_all | (intros; apply GlobalTheory.ThetaJets.jetsPh_all <;> assumption)
