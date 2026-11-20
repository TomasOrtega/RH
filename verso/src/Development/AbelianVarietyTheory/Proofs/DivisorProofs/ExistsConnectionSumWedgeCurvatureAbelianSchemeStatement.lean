import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianScheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.exists_obRel_abelian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConnectionSumWedgeCurvatureAbelianScheme.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_connection_sumWedgeCurvature_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, ∃ (m : ℕ) (u v : Fin m → GlobForm A.hom), ObRel (OAff A.hom) x u v := by
  first | exact @GlobalTheory.AbCoh.exists_obRel_abelian | exact GlobalTheory.AbCoh.exists_obRel_abelian | (intros; apply GlobalTheory.AbCoh.exists_obRel_abelian <;> assumption)
