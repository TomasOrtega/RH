import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelGaloisFixesIntegers.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.level_galois_fixes_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigA_fix | exact GlobalTheory.CompanionTheory.LatC.sigA_fix | (intros; apply GlobalTheory.CompanionTheory.LatC.sigA_fix <;> assumption)
