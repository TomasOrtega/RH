import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHomogeneousIdealNeTop.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.homogeneous_ideal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), Nonempty X → homIdeal i ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | exact GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | (intros; apply GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top <;> assumption)
