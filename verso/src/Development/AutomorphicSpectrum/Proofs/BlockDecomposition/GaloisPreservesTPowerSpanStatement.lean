import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGaloisPreservesTPowerSpan.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.galois_preserves_t_power_span : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | exact GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | (intros; apply GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap <;> assumption)
