import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Geo.evV_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBasicOpenEvalSurjective.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.basic_open_eval_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first | exact @GlobalTheory.CompanionTheory.Geo.evV_surjective | exact GlobalTheory.CompanionTheory.Geo.evV_surjective | (intros; apply GlobalTheory.CompanionTheory.Geo.evV_surjective <;> assumption)
