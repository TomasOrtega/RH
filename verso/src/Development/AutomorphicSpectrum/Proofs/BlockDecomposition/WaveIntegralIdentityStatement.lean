import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.wave_integral_identity : GlobalTheory.CompanionTheory.KerFc.WaveInt := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)
