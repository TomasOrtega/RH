import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_identity_of_local_densities : Scal → LocR → ThetaId := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)
