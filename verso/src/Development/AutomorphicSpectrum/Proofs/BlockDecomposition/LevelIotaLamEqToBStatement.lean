import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelIotaLamEqToB.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.level_iota_lam_eq_toB : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c → (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | exact GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB <;> assumption)
