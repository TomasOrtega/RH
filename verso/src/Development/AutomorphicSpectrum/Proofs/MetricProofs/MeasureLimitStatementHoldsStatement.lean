import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMeasureLimitStatementHolds.lean&line=488#L488)
-/
theorem _root_.GlobalTheory.T.measure_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)
