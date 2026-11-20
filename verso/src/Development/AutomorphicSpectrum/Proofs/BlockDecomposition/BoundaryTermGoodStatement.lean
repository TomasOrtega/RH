import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBoundaryTermGood.lean&line=199#L199)
-/
theorem _root_.GlobalTheory.T.boundary_term_good : BGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)
