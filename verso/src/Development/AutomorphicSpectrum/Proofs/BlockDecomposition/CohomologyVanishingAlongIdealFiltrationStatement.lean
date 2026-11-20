import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCohomologyVanishingAlongIdealFiltration.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.cohomology_vanishing_along_ideal_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A),
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  first | exact @GlobalTheory.CompanionTheory.TowerEnd.vanish | exact GlobalTheory.CompanionTheory.TowerEnd.vanish | (intros; apply GlobalTheory.CompanionTheory.TowerEnd.vanish <;> assumption)
