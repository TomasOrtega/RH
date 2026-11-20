import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenIso

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Substitute `hyq` using the available equality. Establish `: genMap η ⟨genPt η, hy⟩ = (Scheme.stalkClosedPointTo η).hom`. Simplify using `[genMap, TopCat.Presheaf.stalkSpecializes_refl]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hη.bij`.
-/
theorem genMap_bijective_of_eq {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X)
    (hη : IsCptGen η) (y : X) (hy : genPt η ⤳ y) (hyq : y = genPt η) :
    Function.Bijective (genMap η ⟨y, hy⟩) := by
  subst hyq
  have : genMap η ⟨genPt η, hy⟩ = (Scheme.stalkClosedPointTo η).hom := by
    simp [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [this]
  exact hη.bij

/- English proof (translation)
Establish `hy' : η (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ y` using `hy`. Express the relevant statement in the definitionally equal form `Spec.map (X.presheaf.stalkSpecializes hy' ≫ Scheme.stalkClosedPointTo η) ≫ _ = _`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`. Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk η`.
-/
theorem genMap_comp {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X) (y : X)
    (hy : genPt η ⤳ y) : spMap (genMap η ⟨y, hy⟩) ≫ X.fromSpecStalk y = η := by
  have hy' : η (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ y := hy
  change Spec.map (X.presheaf.stalkSpecializes hy' ≫ Scheme.stalkClosedPointTo η) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η

/- English proof (translation)
Introduce `X Ω Ω' _ _ ξ ξ' h h' hq`. Establish `hs : genPt ξ ⤳ genPt ξ'` using `hq ▸ specializes_rfl`. Set `p : Cpt ξ` to `⟨genPt ξ', hs⟩`. Set `p' : Cpt ξ'` to `⟨genPt ξ', specializes_rfl⟩`. Set `e` to `RingEquiv.ofBijective (genMap ξ p) (genMap_bijective_of_eq ξ h _ hs hq.symm)`.

Set `e'` to `RingEquiv.ofBijective (genMap ξ' p') (genMap_bijective_of_eq ξ' h' _ specializes_rfl rfl)`. Use `⟨e'.symm.trans e, ?_⟩` and prove the remaining obligations. Establish `c1 : spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') = ξ` using `genMap_comp ξ _ hs`. Establish `c2 : spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ') = ξ'` using `genMap_comp ξ' _ specializes_rfl`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[c2]`. Use `_ = spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') := by`. Rewrite using `[← Category.assoc]`. Use `congr 1`. Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `e (e'.symm (genMap ξ' p' x)) = genMap ξ p x`. Rewrite using `[show e'.symm (genMap ξ' p' x) = x from e'.symm_apply_apply x]`.

Both sides reduce to the same expression. Use `_ = ξ := c1`.
-/
theorem exists_iso_of_genPt_eq : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X),
    IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  intro X Ω Ω' _ _ ξ ξ' h h' hq
  have hs : genPt ξ ⤳ genPt ξ' := hq ▸ specializes_rfl
  let p : Cpt ξ := ⟨genPt ξ', hs⟩
  let p' : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  let e := RingEquiv.ofBijective (genMap ξ p) (genMap_bijective_of_eq ξ h _ hs hq.symm)
  let e' := RingEquiv.ofBijective (genMap ξ' p') (genMap_bijective_of_eq ξ' h' _ specializes_rfl rfl)
  refine ⟨e'.symm.trans e, ?_⟩
  have c1 : spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') = ξ := genMap_comp ξ _ hs
  have c2 : spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ') = ξ' := genMap_comp ξ' _ specializes_rfl
  calc spMap (e'.symm.trans e).toRingHom ≫ ξ'
      = spMap (e'.symm.trans e).toRingHom ≫ (spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ')) := by
        rw [c2]
    _ = spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') := by
        rw [← Category.assoc]
        congr 1
        rw [spMap, spMap, spMap, ← Spec.map_comp]
        congr 1
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
        change e (e'.symm (genMap ξ' p' x)) = genMap ξ p x
        rw [show e'.symm (genMap ξ' p' x) = x from e'.symm_apply_apply x]
        rfl
    _ = ξ := c1

end GlobalTheory.CompanionTheory.Ar.GenIso
