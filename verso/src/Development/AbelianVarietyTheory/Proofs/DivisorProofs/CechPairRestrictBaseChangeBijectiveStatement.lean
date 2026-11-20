import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Obs.PairExt.pairRes_ext_bijective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechPairRestrictBaseChangeBijective.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.cechPairRestrict_baseChange_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  first | exact @GlobalTheory.Obs.PairExt.pairRes_ext_bijective | exact GlobalTheory.Obs.PairExt.pairRes_ext_bijective | (intros; apply GlobalTheory.Obs.PairExt.pairRes_ext_bijective <;> assumption)
