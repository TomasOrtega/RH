import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmThetaTaylorCoeffAlgebraicAndConjugate.lean&line=379#L379)
-/
theorem _root_.GlobalTheory.T.forall_use1 : ∀ D : D7, use1 D := by
  first | exact @GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | exact GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | (intros; apply GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate <;> assumption)
