import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSch
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UObjDim.smoothOfRelativeDimension_obj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothOfRelativeDimensionShimuraObjectAbelianSch.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  first | exact @GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | exact GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | (intros; apply GlobalTheory.UObjDim.smoothOfRelativeDimension_obj <;> assumption)
