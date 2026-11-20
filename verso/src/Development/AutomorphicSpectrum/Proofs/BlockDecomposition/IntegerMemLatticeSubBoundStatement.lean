import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBound
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegerMemLatticeSubBound.lean&line=276#L276)
-/
theorem _root_.GlobalTheory.T.integer_mem_lattice_sub_bound : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∀ x : OK l K, ∃ c : ℕ, ∀ M k : ℕ, 2 * c ≤ M → Lat.pk l k (Lat.kP l K x) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub | exact GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub <;> assumption)
