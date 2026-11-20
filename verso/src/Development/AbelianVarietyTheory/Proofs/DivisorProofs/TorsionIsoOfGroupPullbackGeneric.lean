import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

/- English proof (translation)
Substitute `hg` using the available equality. Set `m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G)` to `fun z => Over.homMk (z.left ≫ F) (by`. Establish `h : z.left ≫ G'.hom = t` using `Over.w z`. Use `show (z.left ≫ F) ≫ G.hom = t ≫ f`. Rewrite using `[Category.assoc, hF.1.w, ← Category.assoc, h])`.

Establish `hm : ∀ z, (m z).left = z.left ≫ F` using `fun _ => rfl`. Establish `hmul : ∀ x y, m (x * y) = m x * m y` using `fun x y => Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)`. Establish `hinj : Function.Injective m` using `fun x y h => by`. Use `Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))` and prove the remaining obligations. Rewrite using `[← hm, ← hm, h]`.

Establish `hsurj : Function.Surjective m` using `fun z => ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _), Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩`. Conclude with `⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩`.
-/
theorem exists_mulEquiv_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_mulEquiv_points_of_isGrpPullback hF (spMap (algebraMap K B)) (spMap (algebraMap R B)) (by`. Rewrite using `[IsScalarTower.algebraMap_eq R K B, spMap_comp_spMap])`. Conclude with `⟨{ toFun := fun z => ⟨e z.1, by rw [← map_pow, z.2, map_one]⟩ invFun := fun z => ⟨e.symm z.1, by rw [← map_pow, z.2, map_one]⟩ left_inv := fun z => Subtype.ext (e.symm_apply_apply z.1) right_inv := fun z => Subtype.ext (e.apply_symm_apply z.1) map_mul' := fun x y => Subtype.ext ( …`.
-/
theorem exists_tors_mulEquiv_of_isGrpPullback (R K : Type) [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R))
    [GrpObj G] [IsCommMonObj G] (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left)
    (hF : IsGrpPullback G₀ G (spMap (algebraMap R K)) F) (N : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B]
    [IsScalarTower R K B] : ∃ τ : Tors G₀ N B ≃* Tors G N B, ∀ z', (τ z').1.left = z'.1.left ≫ F := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points_of_isGrpPullback hF (spMap (algebraMap K B)) (spMap (algebraMap R B)) (by
    rw [IsScalarTower.algebraMap_eq R K B, spMap_comp_spMap])
  exact ⟨{ toFun := fun z => ⟨e z.1, by rw [← map_pow, z.2, map_one]⟩
           invFun := fun z => ⟨e.symm z.1, by rw [← map_pow, z.2, map_one]⟩
           left_inv := fun z => Subtype.ext (e.symm_apply_apply z.1)
           right_inv := fun z => Subtype.ext (e.apply_symm_apply z.1)
           map_mul' := fun x y => Subtype.ext (e.map_mul x.1 y.1) }, fun z => he z.1⟩

end GlobalTheory.GroupBplus.Aff
