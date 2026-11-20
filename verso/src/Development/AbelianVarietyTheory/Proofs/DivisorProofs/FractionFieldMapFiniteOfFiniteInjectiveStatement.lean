import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFractionFieldMapFiniteOfFiniteInjective.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.fractionFieldMap_finite_of_finite_injective : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  first | exact @GlobalTheory.Mum.GenDesc.fracMap_finite | exact GlobalTheory.Mum.GenDesc.fracMap_finite | (intros; apply GlobalTheory.Mum.GenDesc.fracMap_finite <;> assumption)
