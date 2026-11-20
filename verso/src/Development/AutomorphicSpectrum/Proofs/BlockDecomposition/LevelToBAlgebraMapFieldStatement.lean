import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatC.toB_on_K` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelToBAlgebraMapField.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.level_toB_algebraMap_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.toB_on_K | exact GlobalTheory.CompanionTheory.LatC.toB_on_K | (intros; apply GlobalTheory.CompanionTheory.LatC.toB_on_K <;> assumption)
