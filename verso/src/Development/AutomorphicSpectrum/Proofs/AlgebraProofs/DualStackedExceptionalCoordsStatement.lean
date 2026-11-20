import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDualStackedExceptionalCoords.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)
