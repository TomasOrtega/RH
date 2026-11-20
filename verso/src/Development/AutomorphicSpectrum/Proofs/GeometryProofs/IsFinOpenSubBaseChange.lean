import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.PullSub

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (φ : R →+* R')
  (F : Γ'.G.left ⟶ Γ.G.left)

def pushPt (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G :=
  Over.homMk (x.left ≫ F) (by
    have hx : x.left ≫ Γ'.G.hom = S.hom := Over.w x
    simp only [Over.mk_hom, Category.assoc, hw]
    rw [← Category.assoc, hx])

variable {Γ Γ' φ F}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pushPt_left (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    (pushPt Γ Γ' φ F hw x).left = x.left ≫ F := rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[pushPt_left]`. Conclude with `(h.mul S x y _ _ (pushPt_left h.cart.w x) (pushPt_left h.cart.w y)).symm`.
-/
theorem pushPt_mul (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w (x * y) = pushPt Γ Γ' φ F h.cart.w x * pushPt Γ Γ' φ F h.cart.w y := by
  apply Over.OverMorphism.ext
  rw [pushPt_left]
  exact (h.mul S x y _ _ (pushPt_left h.cart.w x) (pushPt_left h.cart.w y)).symm

/- English proof (translation)
Establish `h1` using `pushPt_mul h (1 : S ⟶ Γ'.G) 1`. Rewrite `h1` using `[_root_.mul_one]`. Conclude with `_root_.mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)`.
-/
theorem pushPt_one (h : Γ'.IsBaseChange Γ φ F) (S : Over (Spec (CommRingCat.of R'))) :
    pushPt Γ Γ' φ F h.cart.w (1 : S ⟶ Γ'.G) = 1 := by
  have h1 := pushPt_mul h (1 : S ⟶ Γ'.G) 1
  rw [_root_.mul_one] at h1
  exact _root_.mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)

/- English proof (translation)
Establish `h2` using `pushPt_mul h x⁻¹ x`. Rewrite `h2` using `[_root_.inv_mul_cancel, pushPt_one h S]`. Conclude with `eq_inv_of_mul_eq_one_left h2.symm`.
-/
theorem pushPt_inv (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w x⁻¹ = (pushPt Γ Γ' φ F h.cart.w x)⁻¹ := by
  have h2 := pushPt_mul h x⁻¹ x
  rw [_root_.inv_mul_cancel, pushPt_one h S] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

end GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub in

/- English proof (translation)
Introduce `R _ _ T _ _ Γ R' _ _ _ Γ' F h U hU`. Establish `hpb` using `(isPullback_morphismRestrict F U).paste_vert h.cart`. Use `⟨MorphismProperty.of_isPullback (P := @IsFinite) hpb hU.finite, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G) = MonObj.one`.

Express the relevant statement in the definitionally equal form `SemiCartesianMonoidalCategory.toUnit _ ≫ MonObj.one = MonObj.one`. Rewrite using `[SemiCartesianMonoidalCategory.toUnit_unique (SemiCartesianMonoidalCategory.toUnit _) (𝟙 _), Category.id_comp]`. Establish `e2 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G).left ≫ F = (1 : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ.G).left`. Rewrite using `[← pushPt_left h.cart.w, pushPt_one h]`. Rewrite using `[Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← e1, e2]`.

Express the relevant statement in the definitionally equal form `(Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (MonObj.one : 𝟙_ _ ⟶ Γ.G))) x ∈ U`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `hU.one _`. Introduce `S x y hx hy z`. Establish `hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U` using `fun w => by`.

Rewrite using `[pushPt_left, Scheme.Hom.comp_apply]`. Conclude with `(Scheme.Hom.mem_preimage F).mp (hx w)`. Establish `hy' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w y).left w ∈ U` using `fun w => by`. Rewrite using `[pushPt_left, Scheme.Hom.comp_apply]`. Conclude with `(Scheme.Hom.mem_preimage F).mp (hy w)`.

Establish `hxy` using `hU.mul _ _ _ hx' hy' z`. Rewrite `hxy` using `[← pushPt_mul h, pushPt_left, Scheme.Hom.comp_apply]`. Conclude with `(Scheme.Hom.mem_preimage F).mpr hxy`. Introduce `S x hx z`. Establish `hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U` using `fun w => by`.

Rewrite using `[pushPt_left, Scheme.Hom.comp_apply]`. Conclude with `(Scheme.Hom.mem_preimage F).mp (hx w)`. Establish `hxi` using `hU.inv _ _ hx' z`. Rewrite `hxi` using `[← pushPt_inv h, pushPt_left, Scheme.Hom.comp_apply]`. Conclude with `(Scheme.Hom.mem_preimage F).mpr hxi`.
-/
theorem GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F h U hU
  have hpb := (isPullback_morphismRestrict F U).paste_vert h.cart
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) hpb hU.finite, ?_, ?_, ?_⟩
  · intro x
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G) = MonObj.one := by
      change SemiCartesianMonoidalCategory.toUnit _ ≫ MonObj.one = MonObj.one
      rw [SemiCartesianMonoidalCategory.toUnit_unique (SemiCartesianMonoidalCategory.toUnit _) (𝟙 _),
        Category.id_comp]
    have e2 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G).left ≫ F =
        (1 : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ.G).left := by
      rw [← pushPt_left h.cart.w, pushPt_one h]
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← e1, e2]
    change (Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (MonObj.one : 𝟙_ _ ⟶ Γ.G))) x ∈ U
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hU.one _
  · intro S x y hx hy z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hy' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w y).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hy w)
    have hxy := hU.mul _ _ _ hx' hy' z
    rw [← pushPt_mul h, pushPt_left, Scheme.Hom.comp_apply] at hxy
    exact (Scheme.Hom.mem_preimage F).mpr hxy
  · intro S x hx z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hxi := hU.inv _ _ hx' z
    rw [← pushPt_inv h, pushPt_left, Scheme.Hom.comp_apply] at hxi
    exact (Scheme.Hom.mem_preimage F).mpr hxi
