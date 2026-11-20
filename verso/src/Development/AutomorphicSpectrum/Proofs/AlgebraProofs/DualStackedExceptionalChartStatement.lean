import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalChart
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDualStackedExceptionalChart.lean&line=357#L357)
-/
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_chart : GroundTheory.Heights₂.Heights.DualStackedExcChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart <;> assumption)
