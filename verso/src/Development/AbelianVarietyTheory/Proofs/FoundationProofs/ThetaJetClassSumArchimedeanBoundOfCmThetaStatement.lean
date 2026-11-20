import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchTop.archSt_of_inp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaJetClassSumArchimedeanBoundOfCmTheta.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta : (∀ D, Inp D) → ArchSt := by
  first | exact @GlobalTheory.ArchTop.archSt_of_inp | exact GlobalTheory.ArchTop.archSt_of_inp | (intros; apply GlobalTheory.ArchTop.archSt_of_inp <;> assumption)
