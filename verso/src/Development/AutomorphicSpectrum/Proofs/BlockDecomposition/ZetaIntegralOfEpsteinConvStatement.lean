import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZetaAlongK.zetaK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FZetaIntegralOfEpsteinConv.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.zeta_integral_of_epstein_conv : EpConv → ZetaK := by
  first | exact @GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | exact GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | (intros; apply GlobalTheory.CompanionTheory.ZetaAlongK.zetaK <;> assumption)
