import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryTheta.const_sq_eq_det` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaPullbackConstantSqEqDet.lean&line=591#L591)
-/
theorem _root_.GlobalTheory.T.thetaPullbackConstant_sq_eq_det : ∀ D : D7, LemmaCGaussConstant D := by
  first | exact @GlobalTheory.UnitaryTheta.const_sq_eq_det | exact GlobalTheory.UnitaryTheta.const_sq_eq_det | (intros; apply GlobalTheory.UnitaryTheta.const_sq_eq_det <;> assumption)
