import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfDimEqZero.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_dim_eq_zero' : ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | exact GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | (intros; apply GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero <;> assumption)
