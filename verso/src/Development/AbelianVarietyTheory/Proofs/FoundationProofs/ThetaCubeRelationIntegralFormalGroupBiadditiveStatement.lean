import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaCubeRelationIntegralFormalGroupBiadditive.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  first | exact @GlobalTheory.ThetaCube.cube_addInt_beBiadd | exact GlobalTheory.ThetaCube.cube_addInt_beBiadd | (intros; apply GlobalTheory.ThetaCube.cube_addInt_beBiadd <;> assumption)
