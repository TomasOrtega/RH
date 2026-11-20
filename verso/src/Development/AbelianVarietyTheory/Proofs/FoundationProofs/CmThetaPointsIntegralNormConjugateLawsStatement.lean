import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmThetaPointsIntegralNormConjugateLaws.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  first | exact @GlobalTheory.CMEndo.endo_all | exact GlobalTheory.CMEndo.endo_all | (intros; apply GlobalTheory.CMEndo.endo_all <;> assumption)
