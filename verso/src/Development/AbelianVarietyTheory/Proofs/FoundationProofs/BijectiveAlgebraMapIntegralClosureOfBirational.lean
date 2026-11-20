import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

namespace GlobalTheory

universe u

section Normal

variable {X Y : Scheme.{u}}

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Use `IsIntegrallyClosed.of_localization_maximal fun p _ _ => ?_` and prove the remaining obligations. Set `q : PrimeSpectrum Γ(Y, U)` to `⟨p, inferInstance⟩`. Establish `hq : hU.fromSpec q ∈ U`. Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨q, rfl⟩`.

Use `letI := Y.presheaf.algebra_section_stalk (U := U) ⟨hU.fromSpec q, hq⟩`. Use `haveI : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec q)) := hU.isLocalization_stalk' q hq`. Use `haveI := hY (hU.fromSpec q)`. Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec q)) (Localization.AtPrime p)).toRingEquiv`.
-/
theorem _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ => ?_
  let q : PrimeSpectrum Γ(Y, U) := ⟨p, inferInstance⟩
  have hq : hU.fromSpec q ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨hU.fromSpec q, hq⟩
  haveI : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec q)) :=
    hU.isLocalization_stalk' q hq
  haveI := hY (hU.fromSpec q)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec q))
      (Localization.AtPrime p)).toRingEquiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Establish `h` using `(genericPoint_spec X).image f.continuous`. Rewrite `h` using `[Set.image_univ, f.denseRange.closure_range]`. Conclude with `h.eq (genericPoint_spec Y)`.
-/
theorem _root_.GlobalTheory.apply_genericPoint_of_isDominant (f : X ⟶ Y) [IsDominant f] [IrreducibleSpace X]
    [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Use `haveI : Nonempty U := ⟨⟨y, hyU⟩⟩`. Substitute `hy` using the available equality. Conclude with `functionField_isFractionRing_of_isAffineOpen Y U hU`.
-/
theorem _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hyU : y ∈ U) (hy : y = genericPoint Y) :
    letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hyU⟩
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk y) := by
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  subst hy
  exact functionField_isFractionRing_of_isAffineOpen Y U hU

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
/- English proof (translation)
Establish `h2 : f (genericPoint X) = genericPoint Y` using `_root_.GlobalTheory.apply_genericPoint_of_isDominant f`. Take `⟨y, hy⟩` from `‹Nonempty U›`. Establish `hηU : f (genericPoint X) ∈ U`. Rewrite using `[h2]`. Conclude with `((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨y, trivial, hy⟩`.

Use `letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hηU⟩`. Use `haveI := _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint hU _ hηU h2`. Use `haveI := _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks hY hU`. Establish `hsq` using `f.germ_stalkMap_apply U (genericPoint X) hηU`. Establish `hgX` using `germ_injective_of_isIntegral X (U := f ⁻¹ᵁ U) (genericPoint X) hηU`.

Establish `hg` using `ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))`. Establish `hgY : Function.Injective (Y.presheaf.germ U _ hηU)` using `IsFractionRing.injective Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))`. Use `⟨fun a b hab => hgY (hg.1 ?_), fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hsq, hsq, hab]`. Use `letI := (f.app U).hom.toAlgebra`.

Set `ψ` to `(inv (f.stalkMap (genericPoint X))).hom.comp (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU).hom`. Establish `hψ : (algebraMap Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))).comp (RingHom.id _) = ψ.comp (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U))`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `Y.presheaf.germ U _ hηU a = (inv (f.stalkMap (genericPoint X))).hom (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU (f.app U a))`. Rewrite using `[← hsq, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]`.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hs.map_of_comp_eq (RingHom.id _) ψ hψ)`. Establish `hr' : Y.presheaf.germ U _ hηU r = (inv (f.stalkMap (genericPoint X))).hom (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU s)` using `hr`. Use `⟨r, hgX ?_⟩` and prove the remaining obligations. Rewrite using `[← hsq, hr', ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]`.
-/
private lemma app_injective_and_exists_app_eq_of_isIntegral (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    Function.Injective (f.app U) ∧ ∀ s : Γ(X, f ⁻¹ᵁ U),
      (letI := (f.app U).hom.toAlgebra; IsIntegral Γ(Y, U) s) → ∃ r, f.app U r = s := by
  have h2 : f (genericPoint X) = genericPoint Y := _root_.GlobalTheory.apply_genericPoint_of_isDominant f
  obtain ⟨y, hy⟩ := ‹Nonempty U›
  have hηU : f (genericPoint X) ∈ U := by
    rw [h2]; exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨y, trivial, hy⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hηU⟩
  haveI := _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint hU _ hηU h2
  haveI := _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks hY hU
  have hsq := f.germ_stalkMap_apply U (genericPoint X) hηU
  have hgX := germ_injective_of_isIntegral X (U := f ⁻¹ᵁ U) (genericPoint X) hηU
  have hg := ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))
  have hgY : Function.Injective (Y.presheaf.germ U _ hηU) :=
    IsFractionRing.injective Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))
  refine ⟨fun a b hab => hgY (hg.1 ?_), fun s hs => ?_⟩
  · rw [hsq, hsq, hab]
  · letI := (f.app U).hom.toAlgebra
    let ψ := (inv (f.stalkMap (genericPoint X))).hom.comp (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU).hom
    have hψ : (algebraMap Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))).comp (RingHom.id _) =
        ψ.comp (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
      ext a
      change Y.presheaf.germ U _ hηU a = (inv (f.stalkMap (genericPoint X))).hom
        (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU (f.app U a))
      rw [← hsq, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hs.map_of_comp_eq (RingHom.id _) ψ hψ)
    have hr' : Y.presheaf.germ U _ hηU r =
        (inv (f.stalkMap (genericPoint X))).hom (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU s) := hr
    refine ⟨r, hgX ?_⟩
    rw [← hsq, hr', ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
/- English proof (translation)
Use `letI := (f.app U).hom.toAlgebra`. Break down `isEmpty_or_nonempty U with hE | hN` into its components or cases. Establish `hU0 : U = ⊥`. Use extensionality with `x`. Simplify using `only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`.

Conclude with `fun hx => hE.false ⟨x, hx⟩`. Substitute `hU0` using the available equality. Establish `h01 : (0 : integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥)) = 1`. Rewrite using `[← map_zero (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))), ← map_one (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))), Subsingleton.elim (0 : Γ(Y, ⊥)) 1]`. Use `haveI := subsingleton_of_zero_eq_one h01`.

Conclude with `⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩`. Take `⟨hinj, hex⟩` from `app_injective_and_exists_app_eq_of_isIntegral f hY hU`. Use `⟨fun a b hab => hinj (congrArg Subtype.val hab), fun b => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `hex b.1 b.2`. Conclude with `⟨r, Subtype.ext hr⟩`.
-/
private lemma bijective_algebraMap_integralClosure_of_isIntegrallyClosed (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) := by
  letI := (f.app U).hom.toAlgebra
  rcases isEmpty_or_nonempty U with hE | hN
  · have hU0 : U = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hE.false ⟨x, hx⟩
    subst hU0
    have h01 : (0 : integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥)) = 1 := by
      rw [← map_zero (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        ← map_one (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        Subsingleton.elim (0 : Γ(Y, ⊥)) 1]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨hinj, hex⟩ := app_injective_and_exists_app_eq_of_isIntegral f hY hU
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun b => ?_⟩
    obtain ⟨r, hr⟩ := hex b.1 b.2
    exact ⟨r, Subtype.ext hr⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Establish `hpiece : ∀ U : Y.affineOpens, IsIso (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1)))`. Introduce `U`. Use `haveI : IsIso ((f.normalizationDiagramMap).app (Opposite.op U.1)) := (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_integralClosure_of_isIntegrallyClosed f hY U.2)`. Use `infer_instance`. Establish `hcomp : ∀ U : Y.affineOpens, IsOpenImmersion (f.normalizationOpenCover.f U ≫ f.fromNormalization)`.

Introduce `U`. Rewrite using `[Scheme.Hom.ι_fromNormalization]`. Use `haveI := hpiece U`. Use `haveI : IsOpenImmersion (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) := IsOpenImmersion.of_isIso _`. Conclude with `@IsOpenImmersion.comp _ _ _ _ _ this (IsAffineOpen.isOpenImmersion_fromSpec _)`.

Establish `hinj : Function.Injective f.fromNormalization`. Introduce `z₁ z₂ h`. Take `⟨V, hV, hyV, -⟩` from `(Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show f.fromNormalization z₁ ∈ (⊤ : Y.Opens) from trivial)`. Set `U : Y.affineOpens` to `⟨V, hV⟩`. Establish `h₁ : z₁ ∈ f.fromNormalization ⁻¹ᵁ U.1` using `hyV`.

Establish `h₂ : z₂ ∈ f.fromNormalization ⁻¹ᵁ U.1` using `by show f.fromNormalization z₂ ∈ V`. Rewrite using `[← h]`. Conclude with `hyV`. Rewrite `h₁`, `h₂` using `[Scheme.Hom.fromNormalization_preimage]`. Take `⟨q₁, rfl⟩` from `h₁`.

Take `⟨q₂, rfl⟩` from `h₂`. Use `haveI := hcomp U`. Use `congr 1`. Apply `(f.normalizationOpenCover.f U ≫ f.fromNormalization).isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]`.

Use `haveI : IsOpenImmersion f.fromNormalization := IsOpenImmersion.of_openCover_source _ f.normalizationOpenCover hinj hcomp`. Use `haveI : Epi f.fromNormalization.base := by`. Rewrite using `[TopCat.epi_iff_surjective]`. Introduce `y`. Take `⟨V, hV, hyV, -⟩` from `(Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show y ∈ (⊤ : Y.Opens) from trivial)`.

Set `U : Y.affineOpens` to `⟨V, hV⟩`. Establish `hV' : IsAffineOpen V` using `hV`. Use `haveI := hpiece U`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : y ∈ Set.range hV'.fromSpec := by`. Rewrite `hyV` using `[← SetLike.mem_coe, ← hV'.range_fromSpec]`.

Conclude with `hyV`. Take `⟨q, rfl⟩` from `(Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))).surjective p`. Use `⟨f.normalizationOpenCover.f U q, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp]`. Conclude with `(Scheme.Hom.comp_apply _ _ q).symm.trans ((congrArg (fun g => g q) (Scheme.Hom.ι_fromNormalization f U)).trans (Scheme.Hom.comp_apply _ _ q))`.

Conclude with `IsOpenImmersion.isIso _`.
-/
theorem _root_.GlobalTheory.isIso_fromNormalization_of_birational (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.fromNormalization := by
  have hpiece : ∀ U : Y.affineOpens,
      IsIso (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) := by
    intro U
    haveI : IsIso ((f.normalizationDiagramMap).app (Opposite.op U.1)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_integralClosure_of_isIntegrallyClosed f hY U.2)
    infer_instance
  have hcomp : ∀ U : Y.affineOpens,
      IsOpenImmersion (f.normalizationOpenCover.f U ≫ f.fromNormalization) := by
    intro U
    rw [Scheme.Hom.ι_fromNormalization]
    haveI := hpiece U
    haveI : IsOpenImmersion (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) :=
      IsOpenImmersion.of_isIso _
    exact @IsOpenImmersion.comp _ _ _ _ _ this (IsAffineOpen.isOpenImmersion_fromSpec _)
  have hinj : Function.Injective f.fromNormalization := by
    intro z₁ z₂ h
    obtain ⟨V, hV, hyV, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show f.fromNormalization z₁ ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have h₁ : z₁ ∈ f.fromNormalization ⁻¹ᵁ U.1 := hyV
    have h₂ : z₂ ∈ f.fromNormalization ⁻¹ᵁ U.1 := by
      show f.fromNormalization z₂ ∈ V
      rw [← h]; exact hyV
    rw [Scheme.Hom.fromNormalization_preimage] at h₁ h₂
    obtain ⟨q₁, rfl⟩ := h₁
    obtain ⟨q₂, rfl⟩ := h₂
    haveI := hcomp U
    congr 1
    apply (f.normalizationOpenCover.f U ≫ f.fromNormalization).isOpenEmbedding.injective
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]
  haveI : IsOpenImmersion f.fromNormalization :=
    IsOpenImmersion.of_openCover_source _ f.normalizationOpenCover hinj hcomp
  haveI : Epi f.fromNormalization.base := by
    rw [TopCat.epi_iff_surjective]
    intro y
    obtain ⟨V, hV, hyV, -⟩ :=
      (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show y ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have hV' : IsAffineOpen V := hV
    haveI := hpiece U
    obtain ⟨p, hp⟩ : y ∈ Set.range hV'.fromSpec := by
      rw [← SetLike.mem_coe, ← hV'.range_fromSpec] at hyV; exact hyV
    obtain ⟨q, rfl⟩ := (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))).surjective p
    refine ⟨f.normalizationOpenCover.f U q, ?_⟩
    rw [← hp]
    exact (Scheme.Hom.comp_apply _ _ q).symm.trans
      ((congrArg (fun g => g q) (Scheme.Hom.ι_fromNormalization f U)).trans
        (Scheme.Hom.comp_apply _ _ q))
  exact IsOpenImmersion.isIso _

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
/- English proof (translation)
Substitute `h` using the available equality. Establish `h'` using `Scheme.Hom.stalkMap_comp c f w`. Use `haveI : IsIso ((c ≫ f).stalkMap w) := inferInstance`. Use `haveI : IsIso (f.stalkMap (c w) ≫ c.stalkMap w) := h' ▸ this`. Conclude with `IsIso.of_isIso_comp_right _ (c.stalkMap w)`.
-/
private lemma isIso_stalkMap_of_comp_isOpenImmersion {W : Scheme.{u}} (f : X ⟶ Y) (c : W ⟶ X)
    [IsOpenImmersion c] (g : W ⟶ Y) [hg : IsOpenImmersion g] (h : c ≫ f = g) (w : W) :
    IsIso (f.stalkMap (c w)) := by
  subst h
  have h' := Scheme.Hom.stalkMap_comp c f w
  haveI : IsIso ((c ≫ f).stalkMap w) := inferInstance
  haveI : IsIso (f.stalkMap (c w) ≫ c.stalkMap w) := h' ▸ this
  exact IsIso.of_isIso_comp_right _ (c.stalkMap w)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Take `⟨y, hy⟩` from `hU`. Take `⟨x, -⟩` from `(f ∣_ U).surjective ⟨y, hy⟩`. Use `⟨⟨?_⟩, ?_⟩` and prove the remaining obligations. Use `(U.isOpen.dense ⟨y, hy⟩).mono ?_` and prove the remaining obligations. Introduce `z hz`.

Take `⟨w, hw⟩` from `(f ∣_ U).surjective ⟨z, hz⟩`. Conclude with `⟨w.1, by simpa using congrArg Subtype.val hw⟩`. Establish `hg : genericPoint X ∈ f ⁻¹ᵁ U` using `((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).2 ⟨x.1, trivial, x.2⟩`. Simplify using `using isIso_stalkMap_of_comp_isOpenImmersion f (f ⁻¹ᵁ U).ι (f ∣_ U ≫ U.ι) (morphismRestrict_ι f U).symm ⟨_, hg⟩`.
-/
theorem _root_.GlobalTheory.birational_of_isIso_morphismRestrict (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint X)) := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, -⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  refine ⟨⟨?_⟩, ?_⟩
  · refine (U.isOpen.dense ⟨y, hy⟩).mono ?_
    intro z hz
    obtain ⟨w, hw⟩ := (f ∣_ U).surjective ⟨z, hz⟩
    exact ⟨w.1, by simpa using congrArg Subtype.val hw⟩
  · have hg : genericPoint X ∈ f ⁻¹ᵁ U :=
      ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).2 ⟨x.1, trivial, x.2⟩
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f (f ⁻¹ᵁ U).ι (f ∣_ U ≫ U.ι)
      (morphismRestrict_ι f U).symm ⟨_, hg⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Take `⟨U, hU, hpre⟩` from `f.exists_isIso_morphismRestrict_toNormalization`. Establish `hsurj : Function.Surjective (f.toNormalization ⁻¹ᵁ U).ι`. Introduce `x`. Establish `hx : x ∈ f.toNormalization ⁻¹ᵁ U` using `by show x ∈ (f.toNormalization ⁻¹ᵁ U).carrier`. Rewrite using `[hpre]`.

Conclude with `f.quasiFiniteAt x`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Use `haveI : IsIso (f.toNormalization ⁻¹ᵁ U).ι := by`. Rewrite using `[isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]`. Conclude with `⟨inferInstance, hsurj⟩`.

Establish `h1 : IsOpenImmersion ((f.toNormalization ⁻¹ᵁ U).ι ≫ f.toNormalization)`. Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`. Use `haveI : IsOpenImmersion f.toNormalization := (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mp h1`. Use `haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY`.

Rewrite using `[← f.toNormalization_fromNormalization]`. Use `infer_instance`.
-/
theorem _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsOpenImmersion f := by
  obtain ⟨U, hU, hpre⟩ := f.exists_isIso_morphismRestrict_toNormalization
  have hsurj : Function.Surjective (f.toNormalization ⁻¹ᵁ U).ι := by
    intro x
    have hx : x ∈ f.toNormalization ⁻¹ᵁ U := by
      show x ∈ (f.toNormalization ⁻¹ᵁ U).carrier
      rw [hpre]
      exact f.quasiFiniteAt x
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : IsIso (f.toNormalization ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]
    exact ⟨inferInstance, hsurj⟩
  have h1 : IsOpenImmersion ((f.toNormalization ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [← morphismRestrict_ι]
    infer_instance
  haveI : IsOpenImmersion f.toNormalization :=
    (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mp h1
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Use `haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY`. Rewrite using `[← f.toNormalization_fromNormalization]`. Use `infer_instance`.
-/
theorem _root_.GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap (f : X ⟶ Y) [IsIntegralHom f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Use `haveI := _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY`. Use `haveI : Epi f.base := by`. Rewrite using `[TopCat.epi_iff_surjective, ← Set.range_eq_univ]`. Use `IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩ ?_` and prove the remaining obligations. Conclude with `Set.range_nonempty _`.

Conclude with `IsOpenImmersion.isIso f`.
-/
theorem _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY
  haveI : Epi f.base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    refine IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩ ?_
    exact Set.range_nonempty _
  exact IsOpenImmersion.isIso f

/- English proof (translation)
The claim follows from `have ⟨_, _⟩ := birational_of_isIso_morphismRestrict f U hU isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY`.
-/
theorem isOpenImmersion_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsOpenImmersion f :=
  have ⟨_, _⟩ := birational_of_isIso_morphismRestrict f U hU
  isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Take `⟨hd, hs⟩` from `_root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU`. Conclude with `_root_.GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap f hY`.
-/
theorem _root_.GlobalTheory.isIso_of_isFinite_of_birational (f : X ⟶ Y) [IsFinite f]
    [IsIntegral X] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨hd, hs⟩ := _root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU
  exact _root_.GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Take `⟨hd, hs⟩` from `_root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU`. Conclude with `_root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f hY`.
-/
theorem _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨hd, hs⟩ := _root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU
  exact _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

/- English proof (translation)
Take `⟨v, hv⟩` from `hV`. Establish `hg : genericPoint X ∈ V` using `((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨v, trivial, hv⟩`. Use `haveI : IsIso (f.stalkMap (genericPoint X)) := by`. Simplify using `using isIso_stalkMap_of_comp_isOpenImmersion f V.ι (V.ι ≫ f) rfl ⟨_, hg⟩`. Use `haveI : IsDominant f := by`.

Use `⟨((V.ι ≫ f).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, hv⟩, rfl⟩).mono ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨V.ι w, (Scheme.Hom.comp_apply _ _ w).symm⟩`. Conclude with `_root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY`.
-/
theorem _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : X.Opens) (hV : Nonempty V) [IsOpenImmersion (V.ι ≫ f)] : IsOpenImmersion f := by
  obtain ⟨v, hv⟩ := hV
  have hg : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨v, trivial, hv⟩
  haveI : IsIso (f.stalkMap (genericPoint X)) := by
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f V.ι (V.ι ≫ f) rfl ⟨_, hg⟩
  haveI : IsDominant f := by
    refine ⟨((V.ι ≫ f).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, hv⟩, rfl⟩).mono ?_⟩
    rintro _ ⟨w, rfl⟩
    exact ⟨V.ι w, (Scheme.Hom.comp_apply _ _ w).symm⟩
  exact _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY

/- English proof (translation)
Assemble the required witnesses or components as `⟨isOpenImmersion_of_quasiFinite_of_birational f hY U hU, fun _ ↦ isIso_of_isFinite_of_birational f hY U hU, fun _ ↦ isIso_of_isProper_of_quasiFinite_of_birational f hY U hU⟩`.
-/
theorem isOpenImmersion_and_isIso_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsOpenImmersion f ∧ (IsFinite f → IsIso f) ∧ (IsProper f → IsIso f) :=
  ⟨isOpenImmersion_of_quasiFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isProper_of_quasiFinite_of_birational f hY U hU⟩

end Normal

section Constructible

end Constructible

section Etale

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

end Etale

end GlobalTheory
