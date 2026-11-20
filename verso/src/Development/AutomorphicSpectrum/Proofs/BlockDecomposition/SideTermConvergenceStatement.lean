import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgEisSide.sideConv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSideTermConvergence.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)
