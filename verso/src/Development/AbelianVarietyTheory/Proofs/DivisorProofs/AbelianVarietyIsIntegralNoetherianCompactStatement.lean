import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianVarietyIsIntegralNoetherianCompact.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact : ∀ (K : Type) [Field K] (A : AbVar K), IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  first | exact @GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | exact GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | (intros; apply GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace <;> assumption)
