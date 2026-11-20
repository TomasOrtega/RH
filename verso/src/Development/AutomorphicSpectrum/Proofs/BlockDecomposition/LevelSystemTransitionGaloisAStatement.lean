import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelSystemTransitionGaloisA.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.level_system_transition_galois_A : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g a, (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | exact GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | (intros; apply GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA <;> assumption)
