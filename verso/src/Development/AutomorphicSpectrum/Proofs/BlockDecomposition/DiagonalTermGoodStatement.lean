import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgEisDGood.dGood` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDiagonalTermGood.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.diagonal_term_good : DGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisDGood.dGood | exact GlobalTheory.CompanionTheory.RgEisDGood.dGood | (intros; apply GlobalTheory.CompanionTheory.RgEisDGood.dGood <;> assumption)
