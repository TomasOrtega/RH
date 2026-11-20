import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelToBGaloisEquivariant.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.level_toB_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y → (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_toB | exact GlobalTheory.CompanionTheory.LatC.sigmaB_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_toB <;> assumption)
