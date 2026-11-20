import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))`. Establish `e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G']` using `by rw [Hom.one_def]; simp`. Rewrite `e` using `[e₁]`. Use `e.trans ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[G]).left = _`.

Simplify using the standard rewrite rules.
-/
theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

/- English proof (translation)
Rewrite using `[Hom.one_def]`. Simplify using the standard rewrite rules.
-/
theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

/- English proof (translation)
Rewrite using `[← one_left]`. Conclude with `⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩`.
-/
theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z`. Rewrite using `[← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]`. Establish `u0` using `unit_comp Z.m0.toSABMap.cart`. Establish `u1` using `unit_comp Z.m.cart`. Establish `hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c)` using `Over.w (η[Z.oF.t.G])`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left`. Apply `Z.m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[h, Category.assoc, u1, ← hp]`.

Simplify using `only [Model.j, Category.assoc]`. Rewrite using `[liftEx_snd, Category.assoc, hs, Category.comp_id]`. Rewrite using `[← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]`. Introduce `h`. Establish `e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left`.

Apply `Z.m0.toSABMap.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]`. Rewrite using `[liftEx_snd, Category.assoc, hs, Category.comp_id]`. Rewrite using `[e, Category.assoc, u1, ← hp]`. Simplify using `only [Category.assoc]`.
-/
theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
