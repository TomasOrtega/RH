import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAverageInvariance.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.average_invariance : AvgMem → AvgInv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | exact GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | (intros; apply GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem <;> assumption)
