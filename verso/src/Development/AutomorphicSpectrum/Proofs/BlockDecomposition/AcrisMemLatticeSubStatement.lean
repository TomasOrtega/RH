import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAcrisMemLatticeSub.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.acris_mem_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l), Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCris.cris_in | exact GlobalTheory.CompanionTheory.LatCris.cris_in | (intros; apply GlobalTheory.CompanionTheory.LatCris.cris_in <;> assumption)
