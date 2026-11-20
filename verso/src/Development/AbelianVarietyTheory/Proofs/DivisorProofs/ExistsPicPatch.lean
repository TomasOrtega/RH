import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGeneratorOffClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchingLineBundleGeneratorsNearPinchingPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareGlueLineBundleOfLocalGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

/- English proof (translation)
Establish `hA1` using `GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme`. Establish `hA2` using `GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point`. Establish `hB` using `GlobalTheory.T.pinchingSquare_glue_lineBundle_of_local_generators`. Introduce `X X' Z Z' p i i' p' hsq hp hi hgl a b hab`. Take `⟨L', hL', rfl⟩` from `cls_surj a`.

Take `⟨LZ, hLZ, rfl⟩` from `cls_surj b`. Rewrite `hab` using `[← cls_pull hL' i' (pull_isLB hL' i'), ← cls_pull hLZ p' (pull_isLB hLZ p')]`. Take `⟨w, hw⟩` from `(cls_eq_iff _ _).1 hab`. Use `hB X X' Z Z' p i i' p' hsq hgl L' LZ hL' hLZ w hw fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : ∃ z, i z = x`.

Take `⟨z, rfl⟩` from `hx`. Conclude with `hA2 X X' Z Z' p i i' p' hsq hp hi hgl L' LZ hL' hLZ w hw z`. Use `push_neg at hx`. Take `⟨W, s', hxW, hbot, hs'⟩` from `hA1 X X' Z Z' p i i' p' hsq hp hi hgl L' hL' x hx`. Establish `hno : ∀ y : Z, y ∉ i ⁻¹ᵁ W` using `fun y hy => by rw [hbot] at hy; exact hy`.

Use `⟨W, s', fun _ => 1, hxW, hs', fun k l y _ _ hy => (hno y hy).elim, fun z j k _ _ hz _ => (hno _ hz).elim⟩` and prove the remaining obligations.
-/
theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (a : Pic X') (b : Pic Z), GlobalTheory.CechPic.pull i' a = GlobalTheory.CechPic.pull p' b → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = a ∧ GlobalTheory.CechPic.pull i e = b := by
  have hA1 := GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme
  have hA2 := GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point
  have hB := GlobalTheory.T.pinchingSquare_glue_lineBundle_of_local_generators
  intro X X' Z Z' p i i' p' hsq hp hi hgl a b hab
  obtain ⟨L', hL', rfl⟩ := cls_surj a
  obtain ⟨LZ, hLZ, rfl⟩ := cls_surj b
  rw [← cls_pull hL' i' (pull_isLB hL' i'), ← cls_pull hLZ p' (pull_isLB hLZ p')] at hab
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hab
  refine hB X X' Z Z' p i i' p' hsq hgl L' LZ hL' hLZ w hw fun x => ?_
  by_cases hx : ∃ z, i z = x
  · obtain ⟨z, rfl⟩ := hx
    exact hA2 X X' Z Z' p i i' p' hsq hp hi hgl L' LZ hL' hLZ w hw z
  · push_neg at hx
    obtain ⟨W, s', hxW, hbot, hs'⟩ := hA1 X X' Z Z' p i i' p' hsq hp hi hgl L' hL' x hx
    have hno : ∀ y : Z, y ∉ i ⁻¹ᵁ W := fun y hy => by rw [hbot] at hy; exact hy
    refine ⟨W, s', fun _ => 1, hxW, hs', fun k l y _ _ hy => (hno y hy).elim,
      fun z j k _ _ hz _ => (hno _ hz).elim⟩

end GlobalTheory.PinchLift
