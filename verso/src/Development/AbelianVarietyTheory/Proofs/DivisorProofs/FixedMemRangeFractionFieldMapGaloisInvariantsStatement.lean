import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFixedMemRangeFractionFieldMapGaloisInvariants.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) → y ∈ (fracMap ρ hρ).range := by
  first | exact @GlobalTheory.Mum.GenDesc.fixed_mem_range | exact GlobalTheory.Mum.GenDesc.fixed_mem_range | (intros; apply GlobalTheory.Mum.GenDesc.fixed_mem_range <;> assumption)
