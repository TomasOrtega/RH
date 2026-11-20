import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOverFieldAxesWedge
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianOverFieldAxesWedge.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.abelian_over_field_axes_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  first | exact @GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge | exact GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge | (intros; apply GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge <;> assumption)
