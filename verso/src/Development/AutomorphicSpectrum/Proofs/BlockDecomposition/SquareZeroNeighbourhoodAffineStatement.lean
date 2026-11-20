import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodAffine
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSquareZeroNeighbourhoodAffine.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.square_zero_neighbourhood_affine : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U) [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  first | exact @GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq | exact GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq | (intros; apply GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq <;> assumption)
