import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZUnf.zUnfold` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFourierJacobiUnfolding.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.fourier_jacobi_unfolding : ZUnfold := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.zUnfold | exact GlobalTheory.CompanionTheory.ZUnf.zUnfold | (intros; apply GlobalTheory.CompanionTheory.ZUnf.zUnfold <;> assumption)
