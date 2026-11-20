import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaIdentityOfLocalDensities.lean&line=564#L564)
-/
theorem _root_.GlobalTheory.T.theta_identity_of_local_densities : Scal → LocR → ThetaId := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)
