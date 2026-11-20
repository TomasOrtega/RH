import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFontaineLatticeDpowClosed.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.fontaine_lattice_dpow_closed : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  first | exact @GlobalTheory.CompanionTheory.LatCHc.hc_k | exact GlobalTheory.CompanionTheory.LatCHc.hc_k | (intros; apply GlobalTheory.CompanionTheory.LatCHc.hc_k <;> assumption)
