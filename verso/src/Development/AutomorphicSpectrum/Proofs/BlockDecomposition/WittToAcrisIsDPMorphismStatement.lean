import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWittToAcrisIsDPMorphism.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.witt_to_acris_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | exact GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism <;> assumption)
