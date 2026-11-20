import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AV.AbVar.isFinite_iff_finite_ker` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFiniteIffFiniteKer.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.isFinite_iff_finite_ker' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | exact GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_finite_ker <;> assumption)
