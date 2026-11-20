import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariant
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatCSig.sig_lam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelLamGaloisEquivariant.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.level_lam_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g c, (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  first | exact @GlobalTheory.CompanionTheory.LatCSig.sig_lam | exact GlobalTheory.CompanionTheory.LatCSig.sig_lam | (intros; apply GlobalTheory.CompanionTheory.LatCSig.sig_lam <;> assumption)
