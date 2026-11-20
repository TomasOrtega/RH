import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelSystemTransitionGaloisB.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.level_system_transition_galois_B : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) = ((levSys h).L m).σB g ((levSys h).dB m b) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | exact GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB <;> assumption)
