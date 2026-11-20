import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHomogeneousRatioIsUnit.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.homogeneous_ratio_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  first | exact @GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | exact GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | (intros; apply GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit <;> assumption)
