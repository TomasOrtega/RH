import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFiniteIffTateModuleMapInjectiveAndIsogenyIff.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | exact GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective <;> assumption)
