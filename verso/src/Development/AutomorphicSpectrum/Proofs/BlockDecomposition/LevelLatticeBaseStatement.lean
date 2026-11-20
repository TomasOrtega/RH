import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatCBase.latBase_lev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelLatticeBase.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.level_lattice_base : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  first | exact @GlobalTheory.CompanionTheory.LatCBase.latBase_lev | exact GlobalTheory.CompanionTheory.LatCBase.latBase_lev | (intros; apply GlobalTheory.CompanionTheory.LatCBase.latBase_lev <;> assumption)
