import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FInjectiveResolutionLiftPushforward.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.injective_resolution_lift_pushforward : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G'), ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  first | exact @GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | exact GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | (intros; apply GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift <;> assumption)
