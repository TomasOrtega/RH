import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodProductZero
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSquareZeroNeighbourhoodProductZero.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.square_zero_neighbourhood_product_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme), i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤), i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero | exact GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero | (intros; apply GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero <;> assumption)
