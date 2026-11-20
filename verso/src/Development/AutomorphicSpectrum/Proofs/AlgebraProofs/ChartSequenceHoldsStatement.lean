import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FChartSequenceHolds.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.chart_sequence_holds : ChartSequence := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | exact GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence <;> assumption)
