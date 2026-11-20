import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ScalWall.tScal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FScalarSectionExists.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.scalar_section_exists : TScal := by
  first | exact @GlobalTheory.CompanionTheory.ScalWall.tScal | exact GlobalTheory.CompanionTheory.ScalWall.tScal | (intros; apply GlobalTheory.CompanionTheory.ScalWall.tScal <;> assumption)
