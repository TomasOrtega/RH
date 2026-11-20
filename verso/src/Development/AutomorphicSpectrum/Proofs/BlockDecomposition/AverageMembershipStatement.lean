import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EisMirGen.avgMem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAverageMembership.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.average_membership : AvgMem := by
  first | exact @GlobalTheory.CompanionTheory.EisMirGen.avgMem | exact GlobalTheory.CompanionTheory.EisMirGen.avgMem | (intros; apply GlobalTheory.CompanionTheory.EisMirGen.avgMem <;> assumption)
