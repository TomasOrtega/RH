import Mathlib
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

/- English proof (translation)
Use `set φ := Spec.map f with hφ`. Use `set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg`. Establish `hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g` using `(basicOpen_eq_of_affine (R := R) r).symm`. Rewrite using `[hbo]`. Establish `hU` using `isAffineOpen_top (Spec R)`.

Establish `hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens))`. Simplify using `using isAffineOpen_top (Spec S)`. Establish `nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x)` using `fun x => (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm`. Establish `hi` using `(IsLocalization.Away.map_injective_iff (S := Localization.Away r) (Q := Localization.Away (f.hom r)) f.hom r).mp h.1`. Establish `hs` using `(IsLocalization.Away.map_surjective_iff (S := Localization.Away r) (Q := Localization.Away (f.hom r)) f.hom r).mp h.2`.

Rewrite using `[isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g), hU.app_basicOpen_eq_away_map φ hpre g]`. Use `IsIso.comp_isIso' ?_ inferInstance` and prove the remaining obligations. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Use `hU.isLocalization_basicOpen g` as an intermediate fact. Use `hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Use `(IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a` from `⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩`. Rewrite `ha` using `[nat]`. Establish `hx : f x = 0`.

Use `congrArg (Scheme.ΓSpecIso S).hom ha` as an intermediate fact. Rewrite `this` using `[Iso.inv_hom_id_apply]`. Conclude with `this.trans (map_zero _)`. Take `⟨n, hn⟩` from `hi x hx`. Conclude with `⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩`.

Use `(IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b` from `⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩`. Take `⟨c, m, e⟩` from `hs y`. Conclude with `⟨(Scheme.ΓSpecIso R).inv c, m, by`. Rewrite using `[nat, hg, nat]`.

Conclude with `(congrArg (Scheme.ΓSpecIso S).inv.hom e).trans ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩`.
-/
theorem isIso_specMap_restrict_basicOpen_of_bijective {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by
  set φ := Spec.map f with hφ
  set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg
  have hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g :=
    (basicOpen_eq_of_affine (R := R) r).symm
  rw [hbo]
  have hU := isAffineOpen_top (Spec R)
  have hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) := by
    simpa using isAffineOpen_top (Spec S)
  have nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (f x) := fun x =>
    (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hi := (IsLocalization.Away.map_injective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.1
  have hs := (IsLocalization.Away.map_surjective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.2
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g),
    hU.app_basicOpen_eq_away_map φ hpre g]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen g
  have := hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)
  constructor
  · refine (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a :=
      ⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩
    rw [nat] at ha
    have hx : f x = 0 := by
      have := congrArg (Scheme.ΓSpecIso S).hom ha
      rw [Iso.inv_hom_id_apply] at this
      exact this.trans (map_zero _)
    obtain ⟨n, hn⟩ := hi x hx
    exact ⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b :=
      ⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩
    obtain ⟨c, m, e⟩ := hs y
    exact ⟨(Scheme.ΓSpecIso R).inv c, m, by
      rw [nat, hg, nat]
      exact (congrArg (Scheme.ΓSpecIso S).inv.hom e).trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW`. Use `haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..`. Use `haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..`. Use `haveI := (relativeGluingData hα).cover.map_prop V`. Use `haveI := (relativeGluingData hα').cover.map_prop V`.

Use `set φ := Spec.map (ι.app (Opposite.op V)) with hφ`. Establish `hnat : (relativeGluingData hα).natTrans.app V = φ ≫ (relativeGluingData hα').natTrans.app V`. Substitute `hαι` using the available equality. Simplify using `[relativeGluingData, hφ, Spec.map_comp]`. Establish `H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g`.

Use `IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)` and prove the remaining obligations. Rewrite using `[← hnat, hg]`. Conclude with `(relativeGluingData hα).isPullback_natTrans_ι_toBase V`. Establish `hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)` using `by ext1; exact hW`. Substitute `hW'` using the available equality.

Establish `h1` using `IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)`. Establish `hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) = PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b)`. Use extensionality with `x`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'`. Establish `H₂` using `(isPullback_morphismRestrict φ D').paste_vert H`. Use `haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb`. Use `haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by`. Rewrite using `[← H₂.flip.isoPullback_inv_snd]`.

Use `infer_instance`. Establish `hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange = (relativeGluingData hα').cover.f V ''ᵁ D'` using `by ext1`. Rewrite using `[Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]`. Both sides reduce to the same expression. Use `((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr (show IsIso _ from inferInstance)` as an intermediate fact.

Rewrite `this` using `[hr]`. Conclude with `this`. Rewrite using `[← h1, hpre]`. Both sides reduce to the same expression.
-/
theorem relSpec_map_isIso_over_basicOpen : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  intro X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI := (relativeGluingData hα).cover.map_prop V
  haveI := (relativeGluingData hα').cover.map_prop V
  set φ := Spec.map (ι.app (Opposite.op V)) with hφ
  have hnat : (relativeGluingData hα).natTrans.app V =
      φ ≫ (relativeGluingData hα').natTrans.app V := by
    subst hαι
    simp [relativeGluingData, hφ, Spec.map_comp]
  have H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g := by
    refine IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)
    rw [← hnat, hg]
    exact (relativeGluingData hα).isPullback_natTrans_ι_toBase V
  have hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) := by
    ext1; exact hW
  subst hW'
  have h1 := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H
    (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)
  have hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) =
      PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) := by
    ext x; rfl
  refine ⟨?_, ?_⟩
  · set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'
    have H₂ := (isPullback_morphismRestrict φ D').paste_vert H
    haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb
    haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by
      rw [← H₂.flip.isoPullback_inv_snd]
      infer_instance
    have hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange =
        (relativeGluingData hα').cover.f V ''ᵁ D' := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl
    have := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr
      (show IsIso _ from inferInstance)
    rw [hr] at this
    exact this
  · rw [← h1, hpre]
    rfl

end GlobalTheory
