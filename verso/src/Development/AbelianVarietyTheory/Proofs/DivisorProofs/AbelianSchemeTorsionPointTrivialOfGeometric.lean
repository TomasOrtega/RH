import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRigid

/- English proof (translation)
Use `hA.smooth` as an intermediate fact. Set `AT` to `(Over.pullback T.hom).obj A`. Establish `hft : LocallyOfFiniteType AT.hom`. Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (pullback.snd A.hom T.hom)`. Use `infer_instance`.

Set `f` to `((Over.pullback T.hom).map (mulN A c)).left`. Establish `hfu : FormallyUnramified f`. Establish `h` using `GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc`. Rewrite `h` using `[← GlobalTheory.GrpTangent.pullback_map_mulN]`. Conclude with `h`.

Establish `hff : LocallyOfFiniteType f`. Establish `: LocallyOfFiniteType (f ≫ AT.hom)`. Rewrite using `[show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]`. Use `infer_instance`. Conclude with `locallyOfFiniteType_of_comp f AT.hom`.

Set `sec : (T ⟶ A) → (T.left ⟶ AT.left)` to `fun y => pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])`. Establish `sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left` using `fun y => pullback.lift_fst _ _ _`. Establish `sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _` using `fun y => pullback.lift_snd _ _ _`. Establish `f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left` using `pullback.lift_fst _ _ _`. Establish `f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom` using `pullback.lift_snd _ _ _`.

Establish `sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c)`. Introduce `y`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst, ← GlobalTheory.GrpTangent.comp_mulN]`. Both sides reduce to the same expression.

Rewrite using `[Category.assoc, f_snd, sec_snd, sec_snd]`. Establish `key : sec x ≫ f = sec 1 ≫ f` using `by rw [sec_f, sec_f, hx, one_pow]`. Set `Y : Over AT.left` to `Over.mk f`. Set `X : Over AT.left` to `Over.mk (sec 1 ≫ f)`. Set `fx : X ⟶ Y` to `Over.homMk (sec x) key`.

Set `f1 : X ⟶ Y` to `Over.homMk (sec 1) rfl`. Use `haveI : LocallyOfFiniteType Y.hom := hff`. Use `haveI : FormallyUnramified Y.hom := hfu`. Establish `hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1)`. Introduce `t`.

Take `⟨k, _, _, a, ha⟩` from `GlobalTheory.FinEt.exists_algClosed_point T.left t`. Establish `hk : (c : k) ≠ 0` using `(GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero`. Establish `h1` using `H k hk (a ≫ T.hom) (Over.homMk a rfl)`. Establish `h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left`. Use `congrArg CommaMorphism.left (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)` as an intermediate fact.

Conclude with `this`. Establish `h3 : a ≫ fx.left = a ≫ f1.left`. Express the relevant statement in the definitionally equal form `a ≫ sec x = a ≫ sec 1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, sec_fst, sec_fst, h2]`.

Rewrite using `[Category.assoc, Category.assoc, sec_snd, sec_snd]`. Establish `h4` using `(GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3`. Apply `h4` to reduce the goal to its premises. Rewrite using `[ha]`. Both sides reduce to the same expression.

Establish `hsec : sec x = sec 1`. Use `(GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by` as an intermediate fact. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `hpt _)`. Simplify `this` using `[fx, f1]`.

Use `ext1`. Rewrite using `[← sec_fst x, hsec, sec_fst]`.
-/
theorem eq_one_of_geometric (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (T : Over S) (x : T ⟶ A) (c : ℕ) (hc : IsUnit (c : Γ(T.left, ⊤)))
    (hx : x ^ c = 1)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S)
      (g : Over.mk z ⟶ T), g ≫ x = 1) : x = 1 := by
  have := hA.smooth
  let AT := (Over.pullback T.hom).obj A
  have hft : LocallyOfFiniteType AT.hom := by
    change LocallyOfFiniteType (pullback.snd A.hom T.hom); infer_instance
  let f := ((Over.pullback T.hom).map (mulN A c)).left
  have hfu : FormallyUnramified f := by
    have h := GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc
    rw [← GlobalTheory.GrpTangent.pullback_map_mulN] at h
    exact h
  have hff : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ AT.hom) := by
      rw [show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]
      infer_instance
    exact locallyOfFiniteType_of_comp f AT.hom
  let sec : (T ⟶ A) → (T.left ⟶ AT.left) := fun y =>
    pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])
  have sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left := fun y =>
    pullback.lift_fst _ _ _
  have sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _ := fun y =>
    pullback.lift_snd _ _ _
  have f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left :=
    pullback.lift_fst _ _ _
  have f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom :=
    pullback.lift_snd _ _ _
  have sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c) := by
    intro y
    apply pullback.hom_ext
    · rw [Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst,
        ← GlobalTheory.GrpTangent.comp_mulN]
      rfl
    · rw [Category.assoc, f_snd, sec_snd, sec_snd]
  have key : sec x ≫ f = sec 1 ≫ f := by rw [sec_f, sec_f, hx, one_pow]
  let Y : Over AT.left := Over.mk f
  let X : Over AT.left := Over.mk (sec 1 ≫ f)
  let fx : X ⟶ Y := Over.homMk (sec x) key
  let f1 : X ⟶ Y := Over.homMk (sec 1) rfl
  haveI : LocallyOfFiniteType Y.hom := hff
  haveI : FormallyUnramified Y.hom := hfu
  have hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1) := by
    intro t
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left t
    have hk : (c : k) ≠ 0 := (GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero
    have h1 := H k hk (a ≫ T.hom) (Over.homMk a rfl)
    have h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left := by
      have := congrArg CommaMorphism.left
        (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)
      exact this
    have h3 : a ≫ fx.left = a ≫ f1.left := by
      change a ≫ sec x = a ≫ sec 1
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, sec_fst, h2]
      · rw [Category.assoc, Category.assoc, sec_snd, sec_snd]
    have h4 := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3
    apply h4
    rw [ha]; rfl
  have hsec : sec x = sec 1 := by
    have := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by
      rintro _ ⟨t, rfl⟩; exact hpt _)
    simpa [fx, f1] using this
  ext1
  rw [← sec_fst x, hsec, sec_fst]

end GlobalTheory.TorsionRigid
