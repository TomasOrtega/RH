import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatC.levSys_existsUnique` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsUniquePeriodOfCompatible.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.existsUnique_period_of_compatible : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) → ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | exact GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_existsUnique <;> assumption)
