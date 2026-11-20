import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDualStackedGraphBihomogeneous.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.dual_stacked_graph_bihomogeneous : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | exact GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog <;> assumption)
