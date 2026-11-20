import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

/- English proof (translation)
Set `P : Finset S ⥤ CommRingCat.{0}` to `{ obj t := .of (Algebra.adjoin F (t : Set S)) map {t t'} h := CommRingCat.ofHom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }`. Set `cP : Cocone P` to `{ pt := .of S := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }`. Establish `: ReflectsFilteredColimits (forget CommRingCat.{0})` using `⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩`. Establish `hcP : IsColimit cP` using `isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ by`. Set `x' : S` to `x`.

Conclude with `⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)`. Use the proof step `(fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))`. Set `G : (Finset S)ᵒᵖ ⥤ Scheme.{0}` to `P.op ⋙ Scheme.Spec`. Set `cG : Cone G` to `Scheme.Spec.mapCone cP.op`. Establish `hcG : IsLimit cG` using `isLimitOfPreserves Scheme.Spec hcP.op`.

Set `κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K` to `spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)`. Establish `hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ)`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t)` using `inferInstanceAs (IsAffine (Spec _))`.

Establish `hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f)` using `inferInstance`. Take `⟨i, y₀, hy₀, hy₁⟩` from `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } : G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))`. Conclude with `⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩`.
-/
theorem point_from_fg_subalgebra {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFinitePresentation s] (S : Type) [CommRing S] [Algebra F S] (x : Sp S ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap F S).comp φ)) :
    ∃ S₀ : Subalgebra F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ X, x₀ ≫ s = spMap ((algebraMap F S₀).comp φ) ∧
      spMap S₀.val.toRingHom ≫ x₀ = x := by
  classical
  let P : Finset S ⥤ CommRingCat.{0} :=
    { obj t := .of (Algebra.adjoin F (t : Set S))
      map {t t'} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cP : Cocone P :=
    { pt := .of S
      «ι» := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcP : IsColimit cP := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : S := x
        exact ⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset S)ᵒᵖ ⥤ Scheme.{0} := P.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cP.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcP.op
  let κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K :=
    spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)
  have hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t) := inferInstanceAs (IsAffine (Spec _))
  have hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f) := inferInstance
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x
    (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))
  exact ⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c S _ _ x hx`. Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth Dw.dim Xo.s`. Conclude with `point_from_fg_subalgebra (IntermediateField.inclusion c.le).toRingHom Xo.s S x hx`.
-/
theorem moduli_point_from_fg_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∃ S₀ : Subalgebra c.F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ Xo.X, x₀ ≫ Xo.s = sOf c S₀ ∧ spMap S₀.val.toRingHom ≫ x₀ = x := by
  intro E _ _ _ H Dw l Xo c S _ _ x hx
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  exact point_from_fg_subalgebra (IntermediateField.inclusion c.le).toRingHom Xo.s S x hx

end GlobalTheory
