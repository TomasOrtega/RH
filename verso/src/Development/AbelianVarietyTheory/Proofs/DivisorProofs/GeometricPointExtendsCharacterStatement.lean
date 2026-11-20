import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointExtendsCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.Cell.exists_geoF_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricPointExtendsCharacter.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.geometric_point_extends_character : ∀ {P : Type} [CommRing P] (t : PrimeSpectrum P) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : P →+* Ω), RingHom.ker χ = t.asIdeal → ∃ em : Cell.GeoF t →+* Ω, em.comp (Cell.geoHom t) = χ := by
  first | exact @GlobalTheory.ShFam.Cell.exists_geoF_lift | exact GlobalTheory.ShFam.Cell.exists_geoF_lift | (intros; apply GlobalTheory.ShFam.Cell.exists_geoF_lift <;> assumption)
