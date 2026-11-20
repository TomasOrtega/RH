import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FClassSumDenominatorBoundOfCmThetaHypotheses.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses : (∀ D, Inp D) → IntSt := by
  first | exact @GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp | exact GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp | (intros; apply GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp <;> assumption)
