import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.mixed_polarization_identity : GlobalTheory.CompanionTheory.MixZ.Polar := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | exact GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | (intros; apply GlobalTheory.CompanionTheory.MixZ.PolarProof.polar <;> assumption)
