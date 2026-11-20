import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)
