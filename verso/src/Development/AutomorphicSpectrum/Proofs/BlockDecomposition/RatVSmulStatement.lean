import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRatVSmul.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.lines_decomposition : Lines := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLines.lines | exact GlobalTheory.CompanionTheory.RgEisLines.lines | (intros; apply GlobalTheory.CompanionTheory.RgEisLines.lines <;> assumption)
