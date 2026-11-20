import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnfoldingOfAverage.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.unfolding_of_average : SecLaw → AvgMem → Unfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisUnfold.unfold | exact GlobalTheory.CompanionTheory.RgEisUnfold.unfold | (intros; apply GlobalTheory.CompanionTheory.RgEisUnfold.unfold <;> assumption)
