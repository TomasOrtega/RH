import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCancelOfSurjectiveAbelianVarietyHom.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cancel_of_surjective_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left → ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  first | exact @GlobalTheory.AV.AbVar.cancel_of_surjective | exact GlobalTheory.AV.AbVar.cancel_of_surjective | (intros; apply GlobalTheory.AV.AbVar.cancel_of_surjective <;> assumption)
