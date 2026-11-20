import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `R _ F W X Y Z f g h k hpb hE n`. Establish `hf : sch.map f = sch.map hpb.isoPullback.hom ≫ sch.map (pullback.fst h k)`. Rewrite using `[← CategoryTheory.Functor.map_comp, IsPullback.isoPullback_hom_fst]`. Establish `hl : ∀ x, pull R (sch.map hpb.isoPullback.inv) F n (pull R (sch.map hpb.isoPullback.hom) F n x) = x`. Introduce `x`.

Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]`. Establish `hr : ∀ x, pull R (sch.map hpb.isoPullback.hom) F n (pull R (sch.map hpb.isoPullback.inv) F n x) = x`. Introduce `x`. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]`. Establish `hb : Function.Bijective (pull R (sch.map hpb.isoPullback.hom) F n)` using `Function.bijective_iff_has_inverse.mpr ⟨_, hl, hr⟩`.

Establish `hc : (pull R (sch.map f) F n : _ → _) = (pull R (sch.map hpb.isoPullback.hom) F n) ∘ (pull R (sch.map (pullback.fst h k)) F n)`. Use function extensionality and compare the values at `x`. Rewrite using `[hf, pull_comp]`. Both sides reduce to the same expression. Rewrite using `[hc]`.

Conclude with `hb.comp (hE n)`.
-/
theorem spPbEqv : ∀ (R : Type) [CommRing R] (F : Shv R) {W X Y Z : Scheme.{0}} (f : W ⟶ X) (g : W ⟶ Y)
    (h : X ⟶ Z) (k : Y ⟶ Z), IsPullback f g h k → Eqv R (sch.map (pullback.fst h k)) F →
    Eqv R (sch.map f) F := by
  intro R _ F W X Y Z f g h k hpb hE n
  have hf : sch.map f = sch.map hpb.isoPullback.hom ≫ sch.map (pullback.fst h k) := by
    rw [← CategoryTheory.Functor.map_comp, IsPullback.isoPullback_hom_fst]
  have hl : ∀ x, pull R (sch.map hpb.isoPullback.inv) F n (pull R (sch.map hpb.isoPullback.hom) F n x) = x := by
    intro x
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have hr : ∀ x, pull R (sch.map hpb.isoPullback.hom) F n (pull R (sch.map hpb.isoPullback.inv) F n x) = x := by
    intro x
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  have hb : Function.Bijective (pull R (sch.map hpb.isoPullback.hom) F n) :=
    Function.bijective_iff_has_inverse.mpr ⟨_, hl, hr⟩
  have hc : (pull R (sch.map f) F n : _ → _) =
      (pull R (sch.map hpb.isoPullback.hom) F n) ∘ (pull R (sch.map (pullback.fst h k)) F n) := by
    funext x
    rw [hf, pull_comp]
    rfl
  rw [hc]
  exact hb.comp (hE n)

end UpperTheory.Gal.Mod
