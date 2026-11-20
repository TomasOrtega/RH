import Mathlib
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.LocalRingGeneralisation

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Rewrite using `[← hU.fromSpecStalk_eq_fromSpecStalk hxU]`. Express the relevant statement in the definitionally equal form `Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)`. Establish `: Flat (Spec.map (X.presheaf.germ U x hxU))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`.

Set `` to `X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)`. Use `hU.isLocalization_stalk ⟨x, hxU⟩` as an intermediate fact. Conclude with `IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl`. Establish `h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU)` using `IsAffineOpen.isOpenImmersion_fromSpec hU`. Establish `h₃ : Flat (IsAffineOpen.fromSpec hU)` using `inferInstance`.

Conclude with `MorphismProperty.comp_mem @Flat _ _ this h₃`.
-/
theorem flat_fromSpecStalk (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

/- English proof (translation)
Use `flat_fromSpecStalk X x` as an intermediate fact. Establish `hs : SurjectiveOnStalks (X.fromSpecStalk x)` using `inferInstance`. Use `(ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩` and prove the remaining obligations. Establish `hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom` using `inferInstance`. Establish `h` using `Flat.stalkMap (X.fromSpecStalk x) y`.

Use `algebraize [((X.fromSpecStalk x).stalkMap y).hom]`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y)) ((Spec (X.presheaf.stalk x)).presheaf.stalk y))` using `hl`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem isIso_stalkMap_fromSpecStalk (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  have := flat_fromSpecStalk X x
  have hs : SurjectiveOnStalks (X.fromSpecStalk x) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩
  have hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom := inferInstance
  have h := Flat.stalkMap (X.fromSpecStalk x) y
  algebraize [((X.fromSpecStalk x).stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y))
    ((Spec (X.presheaf.stalk x)).presheaf.stalk y)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _

/- English proof (translation)
Introduce `X x p _`. Set `y : Spec (X.presheaf.stalk x)` to `(⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))`. Use `isIso_stalkMap_fromSpecStalk X x y` as an intermediate fact. Use `⟨X.fromSpecStalk x y, (asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_, ?_⟩` and prove the remaining obligations. Establish `: X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x)` using `⟨y, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Introduce `U hq hx s`. Establish `h1` using `Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s`. Use `show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _`. Rewrite using `[h1, Scheme.fromSpecStalk_app hx]`.

Establish `h2` using `congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s))) (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2`. Rewrite `h2` using `[← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom, Iso.inv_hom_id, CommRingCat.id_apply]`. Rewrite using `[← h2]`. Simplify using `only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]`.

Use `erw [TopCat.Presheaf.germ_res]`.
-/
theorem exists_stalk_equiv_localization : ∀ {X : Scheme.{0}} (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], ∃ (q : X) (e : X.presheaf.stalk q ≃+* Localization.AtPrime p), q ⤳ x ∧ ∀ (U : X.Opens) (hq : q ∈ U) (hx : x ∈ U) (s : Γ(X, U)), e ((X.presheaf.germ U q hq).hom s) = algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  intro X x p _
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨X.fromSpecStalk x y,
    (asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_, ?_⟩
  · have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  · intro U hq hx s
    have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
    show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
    rw [h1, Scheme.fromSpecStalk_app hx]
    have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
      (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
      Iso.inv_hom_id, CommRingCat.id_apply] at h2
    rw [← h2]
    simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
    erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
