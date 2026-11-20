import Development.EtaleCohomology.CohomologicalPurity.LeafGenPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Establish `h` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]`. Both sides reduce to the same expression. Use `_ = RingHom.ker ((Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := by rw [h]; rfl`.

Use `_ = _ := by rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]`.
-/
theorem ker_specMap_mk_appTop {R : CommRingCat.{0}} (I : Ideal R) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom =
      I.comap (Scheme.ΓSpecIso R).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  calc RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      = RingHom.ker ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).hom).hom := by
        rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]; rfl
    _ = RingHom.ker ((Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := by rw [h]; rfl
    _ = _ := by rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]

/- English proof (translation)
Establish `h` using `Ideal.comap_symm (I := J) e.commRingCatIsoToRingEquiv`. Conclude with `h`.
-/
theorem comap_iso_inv {A B : CommRingCat.{0}} (e : A ≅ B) (J : Ideal A) :
    J.comap e.inv.hom = J.map e.hom.hom := by
  have h := Ideal.comap_symm (I := J) e.commRingCatIsoToRingEquiv
  exact h

/- English proof (translation)
Rewrite using `[Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, ← ker_specMap_mk_appTop]`. Use `Ideal.map_id _` and compare the differences between its conclusion and the goal. Rewrite using `[show (homOfLE (X := (Spec (CommRingCat.of B)).Opens) (le_top (a := ⊤))).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.
-/
theorem ker_specMap_mk_top {B : CommRingCat.{0}} (IB : Ideal B) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IB))).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      IB.comap (Scheme.ΓSpecIso B).hom.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, ← ker_specMap_mk_appTop]
  convert Ideal.map_id _
  rw [show (homOfLE (X := (Spec (CommRingCat.of B)).Opens) (le_top (a := ⊤))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]`. Rewrite using `[← Scheme.IdealSheafData.map_ideal I (U := ⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩) (V := V) hle]`. Rewrite using `[comap_iso_inv, Ideal.map_map, ← CommRingCat.hom_comp]`. Conclude with `congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) (I.ideal V)) key`.
-/
theorem comap_ideal_top {X : Scheme.{0}} {B : CommRingCat.{0}} (I : X.IdealSheafData) (w : Spec B ⟶ X)
    [IsOpenImmersion w] (V : X.affineOpens) (ψ : Γ(X, V.1) ⟶ B) (hle : w ''ᵁ ⊤ ≤ V.1)
    (key : X.presheaf.map (homOfLE hle).op ≫ (w.appIso ⊤).hom = ψ ≫ (Scheme.ΓSpecIso B).inv) :
    (I.comap w).ideal ⟨⊤, isAffineOpen_top _⟩ = (I.ideal V).map (ψ ≫ (Scheme.ΓSpecIso B).inv).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [← Scheme.IdealSheafData.map_ideal I (U := ⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩) (V := V) hle]
  rw [comap_iso_inv, Ideal.map_map, ← CommRingCat.hom_comp]
  exact congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) (I.ideal V)) key

/- English proof (translation)
Establish `e : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤ (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⁻¹ᵁ U`. Introduce `x _`. Conclude with `hle ⟨x, trivial, rfl⟩`. Establish `e1` using `Scheme.Hom.appLE_appIso_inv (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) e`. Establish `h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U` using `hU.fromSpec_preimage_self.ge`.

Establish `h2 : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ⁻¹ᵁ ⊤` using `le_top`. Establish `a1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso _).inv`. Rewrite using `[Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Rewrite using `[show ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h1).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _]`. Rewrite using `[CategoryTheory.Functor.map_id, Category.comp_id]`.

Establish `a2 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appLE ⊤ ⊤ h2 = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appTop`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]`.

Use `_ = _ := by`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ h1 h2, a1, a2, Scheme.ΓSpecIso_inv_naturality]`. Both sides reduce to the same expression.
-/
theorem key_gen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)]
    (hle : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ''ᵁ ⊤ ≤ U) :
    X.presheaf.map (homOfLE hle).op ≫
      (Scheme.Hom.appIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⊤).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫ (Scheme.ΓSpecIso _).inv := by
  have e : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro x _
    exact hle ⟨x, trivial, rfl⟩
  have e1 := Scheme.Hom.appLE_appIso_inv
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) e
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h2 : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ⁻¹ᵁ ⊤ := le_top
  have a1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h1).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have a2 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appLE ⊤ ⊤ h2 =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  calc _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).appLE U ⊤ e := by
        rw [← e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ h1 h2, a1, a2, Scheme.ΓSpecIso_inv_naturality]
      rfl

/- English proof (translation)
Rewrite using `[Scheme.Hom.image_top_eq_opensRange]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `show V.2.fromSpec _ ∈ (V.1 : Set X)`. Rewrite using `[← V.2.range_fromSpec]`. Conclude with `⟨_, rfl⟩`.
-/
theorem hle_loc {X : Scheme.{0}} (V : X.affineOpens) (r : Γ(X, V.1))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)] :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ''ᵁ ⊤ ≤ V.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨y, rfl⟩
  show V.2.fromSpec _ ∈ (V.1 : Set X)
  rw [← V.2.range_fromSpec]; exact ⟨_, rfl⟩

/- English proof (translation)
Introduce `X Z ι _ V r`. Establish `: IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)`. Establish `h1` using `Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(X, V.1)) r`. Establish `h2` using `V.2.isOpenImmersion_fromSpec`. Use `infer_instance`.

Establish `hle` using `hle_loc V r`. Apply `Scheme.IdealSheafData.ext_of_isAffine` to reduce the goal to its premises. Establish `hL` using `ker_specMap_mk_top (B := CommRingCat.of (Localization.Away r)) ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))`. Establish `hR` using `comap_ideal_top ι.ker _ V _ hle (key_gen V.2 r hle)`. Use `hL.trans (Eq.trans ?_ hR.symm)` and prove the remaining obligations.

Establish `hc` using `comap_iso_inv (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away r))).symm ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))`. Simplify using `only [Iso.symm_inv, Iso.symm_hom] at hc`. Rewrite using `[hc, Ideal.map_map]`. Both sides reduce to the same expression.
-/
theorem LeafGenKer_of : LeafGenKer := by
  intro X Z ι _ V r
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) := by
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  have hle := hle_loc V r
  apply Scheme.IdealSheafData.ext_of_isAffine
  have hL := ker_specMap_mk_top (B := CommRingCat.of (Localization.Away r))
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  have hR := comap_ideal_top ι.ker _ V _ hle (key_gen V.2 r hle)
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hc := comap_iso_inv (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away r))).symm
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  simp only [Iso.symm_inv, Iso.symm_hom] at hc
  rw [hc, Ideal.map_map]
  rfl

end LateralTheory.CohomologicalPurity.Cl
