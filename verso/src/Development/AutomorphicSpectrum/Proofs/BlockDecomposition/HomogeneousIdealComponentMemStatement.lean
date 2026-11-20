import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHomogeneousIdealComponentMem.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.homogeneous_ideal_component_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first | exact @GlobalTheory.CompanionTheory.Geo.homIdeal_homog | exact GlobalTheory.CompanionTheory.Geo.homIdeal_homog | (intros; apply GlobalTheory.CompanionTheory.Geo.homIdeal_homog <;> assumption)
