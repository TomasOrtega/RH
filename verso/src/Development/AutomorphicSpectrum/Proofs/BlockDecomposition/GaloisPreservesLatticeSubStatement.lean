import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGaloisPreservesLatticeSub.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.galois_preserves_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ) (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)), ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M, Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | exact GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatGal.gal_mem_sub <;> assumption)
