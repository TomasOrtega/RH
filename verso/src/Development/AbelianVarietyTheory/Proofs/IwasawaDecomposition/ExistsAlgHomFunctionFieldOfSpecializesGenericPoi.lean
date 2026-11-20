import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

/- English proof (translation)
Introduce `F _ Y K _ _ q h hq`. Set `ψ₀ : Y.Fn →+* K` to `(Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom`. Establish `e : spMap ψ₀ ≫ (ratOf Y).pt = q`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`.

Conclude with `spMap_stalkClosedPointTo q`. Establish `hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K`. Establish `h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K)`. Establish `hs` using `(ratOf Y).pt_s`. Combine the equalities or inequalities in the displayed calculation.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`. Use `_ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]`. Use `_ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm`. Use `_ = q ≫ Y.str := by`.

Express the relevant statement in the definitionally equal form `(spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `_ = spMap (algebraMap F K) := hq`. Establish `h2` using `Spec.map_injective h1`.

Conclude with `congrArg CommRingCat.Hom.hom h2`. Use `⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩` and prove the remaining obligations. Conclude with `e.symm`.
-/
theorem exists_algHom_of_specializes_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X),
      q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) →
        ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  intro F _ Y K _ _ q h hq
  let ψ₀ : Y.Fn →+* K := (Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom
  have e : spMap ψ₀ ≫ (ratOf Y).pt = q := by
    change Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo q
  have hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K := by
    have h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K) := by
      have hs := (ratOf Y).pt_s
      calc spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap ψ₀ ≫ spMap (algebraMap F Y.Fn) := by
            change Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
        _ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]
        _ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm
        _ = q ≫ Y.str := by
            change (spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str
            rw [e]
            rfl
        _ = spMap (algebraMap F K) := hq
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩
  exact e.symm

end GlobalTheory.FlagBundle
