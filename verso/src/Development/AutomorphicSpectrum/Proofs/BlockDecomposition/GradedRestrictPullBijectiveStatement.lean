import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGradedRestrictPullBijective.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.graded_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | exact GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | (intros; apply GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective <;> assumption)
