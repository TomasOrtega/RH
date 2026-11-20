import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechDR.pairRes_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAffinePairRestrictionInjectiveFirstCohomology.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.affinePairRestriction_injective_firstCohomology : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧ Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  first | exact @GlobalTheory.CechDR.pairRes_injective | exact GlobalTheory.CechDR.pairRes_injective | (intros; apply GlobalTheory.CechDR.pairRes_injective <;> assumption)
