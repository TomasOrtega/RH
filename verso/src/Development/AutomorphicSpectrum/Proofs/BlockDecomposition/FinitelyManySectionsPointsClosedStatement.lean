import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosed
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFinitelyManySectionsPointsClosed.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finitely_many_sections_points_closed : ∀ (k : Type) [Field k] [IsAlgClosed k] (Z : Scheme.{0}) (s : Z ⟶ Sp k) [LocallyOfFiniteType s], Set.Finite {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} → ∀ z : Z, IsClosed ({z} : Set Z) := by
  first | exact @GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points | exact GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points | (intros; apply GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points <;> assumption)
