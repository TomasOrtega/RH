import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.StdChart.tStd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStandardSectionExists.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.standard_section_exists : TStd := by
  first | exact @GlobalTheory.CompanionTheory.StdChart.tStd | exact GlobalTheory.CompanionTheory.StdChart.tStd | (intros; apply GlobalTheory.CompanionTheory.StdChart.tStd <;> assumption)
