import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.waveRep | exact GlobalTheory.CompanionTheory.KerFc.waveRep | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveRep <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.wave_representation : GlobalTheory.CompanionTheory.KerFc.WaveRep := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveRep | exact GlobalTheory.CompanionTheory.KerFc.waveRep | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveRep <;> assumption)
