import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbCoh.preRes_bijective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPreimageCochainRestrictionBijectiveClosedImmersi.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  first | exact @GlobalTheory.AbCoh.preRes_bijective | exact GlobalTheory.AbCoh.preRes_bijective | (intros; apply GlobalTheory.AbCoh.preRes_bijective <;> assumption)
