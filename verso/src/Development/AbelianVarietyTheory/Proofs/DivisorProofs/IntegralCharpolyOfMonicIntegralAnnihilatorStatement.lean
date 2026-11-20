import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharpolyOfMonicIntegralAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralCharpolyOfMonicIntegralAnnihilator.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  first | exact @GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator | exact GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator | (intros; apply GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator <;> assumption)
