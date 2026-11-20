import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicative
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlogMul.plogK_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTruncatedLogMultiplicative.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.truncated_log_multiplicative : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ), pdP δ s = ⊥ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ {x y : B}, x ∈ J → y ∈ J → plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  first | exact @GlobalTheory.CompanionTheory.PlogMul.plogK_mul | exact GlobalTheory.CompanionTheory.PlogMul.plogK_mul | (intros; apply GlobalTheory.CompanionTheory.PlogMul.plogK_mul <;> assumption)
