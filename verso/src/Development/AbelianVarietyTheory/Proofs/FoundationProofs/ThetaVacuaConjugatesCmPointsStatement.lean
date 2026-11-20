import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaConj.useConj_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaVacuaConjugatesCmPoints.lean&line=529#L529)
-/
theorem _root_.GlobalTheory.T.thetaVacua_conjugates_cmPoints : ∀ D : D7, useConj D := by
  first | exact @GlobalTheory.ThetaConj.useConj_all | exact GlobalTheory.ThetaConj.useConj_all | (intros; apply GlobalTheory.ThetaConj.useConj_all <;> assumption)
