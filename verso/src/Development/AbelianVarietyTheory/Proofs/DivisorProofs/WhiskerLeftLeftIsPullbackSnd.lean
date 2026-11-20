import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]`. Use `IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_` and prove the remaining obligations. Establish `h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left`. Rewrite using `[← Over.comp_left, whiskerLeft_fst]`.

Establish `h2 : f.left ≫ T.hom = T'.hom` using `Over.w f`. Rewrite using `[h1, h2, Over.fst_left, Over.snd_left]`. Conclude with `IsPullback.of_hasPullback U.hom T'.hom`. Rewrite using `[Over.fst_left, Over.snd_left]`. Conclude with `IsPullback.of_hasPullback U.hom T.hom`.
-/
theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
