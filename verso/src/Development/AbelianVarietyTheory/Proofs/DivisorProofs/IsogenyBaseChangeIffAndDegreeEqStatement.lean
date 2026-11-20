import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsogenyBaseChangeIffAndDegreeEq.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | exact GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap <;> assumption)
