import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Approx.exists_model_relDim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FSmoothMorphisms%2FAbelianSchemeSpreadsOut.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.abelian_scheme_spreads_out : ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_model_relDim | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_model_relDim | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_model_relDim <;> assumption)
