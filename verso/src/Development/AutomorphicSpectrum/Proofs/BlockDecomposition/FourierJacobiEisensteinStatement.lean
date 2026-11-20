import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFourierJacobiEisenstein.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
