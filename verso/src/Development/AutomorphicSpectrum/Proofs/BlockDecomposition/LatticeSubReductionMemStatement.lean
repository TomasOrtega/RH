import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLatticeSubReductionMem.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.lattice_sub_reduction_mem : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | exact GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub <;> assumption)
