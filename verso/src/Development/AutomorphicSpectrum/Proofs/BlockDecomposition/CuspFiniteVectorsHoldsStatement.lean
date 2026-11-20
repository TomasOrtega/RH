import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFiniteVectorsHolds
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspFiniteVectorsHolds.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.cusp_finite_vectors_holds : GlobalTheory.Published.CuspFiniteVectorsGL := by
  first | exact @GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL | exact GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL | (intros; apply GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL <;> assumption)
