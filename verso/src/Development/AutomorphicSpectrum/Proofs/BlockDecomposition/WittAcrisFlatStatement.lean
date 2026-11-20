import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWittAcrisFlat.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.witt_acris_flat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K), Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  first | exact @GlobalTheory.CompanionTheory.FlatW.flat_AW | exact GlobalTheory.CompanionTheory.FlatW.flat_AW | (intros; apply GlobalTheory.CompanionTheory.FlatW.flat_AW <;> assumption)
