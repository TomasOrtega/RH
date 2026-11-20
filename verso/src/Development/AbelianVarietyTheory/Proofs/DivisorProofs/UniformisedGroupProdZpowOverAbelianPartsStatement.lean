import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.PowData.over₀_prod_zpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformisedGroupProdZpowOverAbelianParts.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  first | exact @GlobalTheory.Mum.PowData.over₀_prod_zpow | exact GlobalTheory.Mum.PowData.over₀_prod_zpow | (intros; apply GlobalTheory.Mum.PowData.over₀_prod_zpow <;> assumption)
