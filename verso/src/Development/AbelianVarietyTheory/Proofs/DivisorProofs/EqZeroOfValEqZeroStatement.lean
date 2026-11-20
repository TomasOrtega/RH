import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ValInj.eq_zero_of_val_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfValEqZero.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_val_eq_zero_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  first | exact @GlobalTheory.ValInj.eq_zero_of_val_eq_zero | exact GlobalTheory.ValInj.eq_zero_of_val_eq_zero | (intros; apply GlobalTheory.ValInj.eq_zero_of_val_eq_zero <;> assumption)
