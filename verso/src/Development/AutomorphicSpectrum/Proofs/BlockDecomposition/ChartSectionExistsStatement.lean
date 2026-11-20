import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TChartProof.tChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FChartSectionExists.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.chart_section_exists : TChart := by
  first | exact @GlobalTheory.CompanionTheory.TChartProof.tChart | exact GlobalTheory.CompanionTheory.TChartProof.tChart | (intros; apply GlobalTheory.CompanionTheory.TChartProof.tChart <;> assumption)
