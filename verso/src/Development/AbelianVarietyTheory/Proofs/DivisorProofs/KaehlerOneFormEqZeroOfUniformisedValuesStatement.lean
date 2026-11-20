import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValues
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.form_eq_zero_of_evForm_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKaehlerOneFormEqZeroOfUniformisedValues.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.form_eq_zero_of_evForm_eq_zero | exact GlobalTheory.form_eq_zero_of_evForm_eq_zero | (intros; apply GlobalTheory.form_eq_zero_of_evForm_eq_zero <;> assumption)
