import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelToBSurjective.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.level_toB_surjective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), Function.Surjective (lev h k).toB := by
  first | exact @GlobalTheory.CompanionTheory.LatLevels.toB_surjective | exact GlobalTheory.CompanionTheory.LatLevels.toB_surjective | (intros; apply GlobalTheory.CompanionTheory.LatLevels.toB_surjective <;> assumption)
