import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicComplete
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAcrisIsAdicComplete.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.acris_isAdicComplete_span_prime : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  first | exact @GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | exact GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | (intros; apply GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete <;> assumption)
