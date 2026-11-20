import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.wave_integral_identity : GlobalTheory.CompanionTheory.KerFc.WaveInt := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)
