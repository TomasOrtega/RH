import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsConeLift.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_cone_lift : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | exact GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | (intros; apply GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK <;> assumption)
