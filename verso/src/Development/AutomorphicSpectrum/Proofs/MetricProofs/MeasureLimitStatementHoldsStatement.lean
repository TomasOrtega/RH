import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.measure_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)
