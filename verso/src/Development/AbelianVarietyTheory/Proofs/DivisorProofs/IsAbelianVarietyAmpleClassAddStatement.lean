import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AV.isAmpleCls_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAbelianVarietyAmpleClassAdd.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  first | exact @GlobalTheory.AV.isAmpleCls_add | exact GlobalTheory.AV.isAmpleCls_add | (intros; apply GlobalTheory.AV.isAmpleCls_add <;> assumption)
