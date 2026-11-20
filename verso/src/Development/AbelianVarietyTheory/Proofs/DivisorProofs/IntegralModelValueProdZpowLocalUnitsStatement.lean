import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.RatModel.val_prod_zpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralModelValueProdZpowLocalUnits.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.integralModel_value_prod_zpow_localUnits : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  first | exact @GlobalTheory.Poinc.RatModel.val_prod_zpow | exact GlobalTheory.Poinc.RatModel.val_prod_zpow | (intros; apply GlobalTheory.Poinc.RatModel.val_prod_zpow <;> assumption)
