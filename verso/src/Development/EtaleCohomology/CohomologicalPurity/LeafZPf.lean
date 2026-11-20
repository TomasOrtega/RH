import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Use `letI := φ.toAlgebra`. Set `e` to `Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I`. Use `(CommRingCat.isPushout_tensorProduct R B (R ⧸ I)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso.symm ?_ ?_ ?_ ?_` and prove the remaining obligations. Both sides reduce to the same expression. Both sides reduce to the same expression.

Use extensionality with `x`. Simplify using `[e]`. Rewrite using `[← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Use extensionality with `x`.

Simplify using `[e]`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.
-/
theorem zpf_pushout {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  letI := φ.toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  refine (CommRingCat.isPushout_tensorProduct R B (R ⧸ I)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toRingEquiv.toCommRingCatIso.symm ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext x
    simp [e]
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]; rfl
  · ext x
    simp [e]
    rw [Algebra.smul_def, mul_one]; rfl

/- English proof (translation)
Establish `h0 : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V)))) (ι.ker.subschemeCover.f V) V.2.fromSpec ι.ker.subschemeι`. Establish `hf` using `V.2.isOpenImmersion_fromSpec`. Establish `hc : IsOpenImmersion (ι.ker.subschemeCover.f V)` using `ι.ker.subschemeCover.map_prop V`. Use `@IsOpenImmersion.isPullback _ _ _ _ _ _ _ _ hc hf ?_ ?_` and prove the remaining obligations. Conclude with `(Scheme.IdealSheafData.subschemeCover_map_subschemeι _ V).trans (Scheme.IdealSheafData.glueDataObjι_ι _ V)`.

Conclude with `(congrArg (ι.ker.subschemeι ⁻¹ᵁ ·) V.2.opensRange_fromSpec).trans (Scheme.IdealSheafData.opensRange_subschemeCover_map _ V).symm`. Use `h0.of_iso (Iso.refl _) (Iso.refl _) (asIso ι.toImage).symm (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]`. Conclude with `ι.toImage_imageι`.
-/
theorem zpf_sqA (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V ≫ inv ι.toImage) V.2.fromSpec ι := by
  have h0 : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V) V.2.fromSpec ι.ker.subschemeι := by
    have hf := V.2.isOpenImmersion_fromSpec
    have hc : IsOpenImmersion (ι.ker.subschemeCover.f V) := ι.ker.subschemeCover.map_prop V
    refine @IsOpenImmersion.isPullback _ _ _ _ _ _ _ _ hc hf ?_ ?_
    · exact (Scheme.IdealSheafData.subschemeCover_map_subschemeι _ V).trans
        (Scheme.IdealSheafData.glueDataObjι_ι _ V)
    · exact (congrArg (ι.ker.subschemeι ⁻¹ᵁ ·) V.2.opensRange_fromSpec).trans
        (Scheme.IdealSheafData.opensRange_subschemeCover_map _ V).symm
  refine h0.of_iso (Iso.refl _) (Iso.refl _) (asIso ι.toImage).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact ι.toImage_imageι

/- English proof (translation)
Use `_root_.range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := J))` as an intermediate fact. Rewrite `this` using `[Ideal.mk_ker]`. Conclude with `this`.
-/
theorem zpf_range_mk {A : Type} [CommRing A] (J : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
  have := _root_.range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := J))
  rw [Ideal.mk_ker] at this
  exact this

/- English proof (translation)
Introduce `X Z ι _ V B _ φ`. Establish `hP` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (zpf_pushout φ (ι.ker.ideal V))).paste_vert (zpf_sqA X Z ι V)`. Use `⟨⟨_, hP⟩, ?_⟩` and prove the remaining obligations. Introduce `U hU`. Establish `hr : ∀ x, (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ Set.range ι ↔ x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ))))`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Take `⟨a, ha, -⟩` from `Scheme.Pullback.exists_preimage_pullback x y hy.symm`. Use `⟨hP.isoPullback.inv a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]`. Conclude with `ha`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨_, (Scheme.Hom.comp_apply _ _ a).symm.trans ((congrArg (fun k => k a) hP.w.symm).trans (Scheme.Hom.comp_apply _ _ a))⟩`. Use extensionality with `x`.

Establish `h1 : x ∈ off B ((ι.ker.ideal V).map φ) ↔ x ∉ PrimeSpectrum.zeroLocus (((ι.ker.ideal V).map φ : Ideal B) : Set B)` using `Iff.rfl`. Establish `h2 : x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U ↔ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ (U : Set X)` using `Iff.rfl`. Simplify using `only [SetLike.mem_coe]`. Rewrite using `[h1, h2, hU, Set.mem_compl_iff, hr, zpf_range_mk]`. Conclude with `Iff.rfl`.
-/
theorem LeafZ_of : LeafZ := by
  intro X Z ι _ V B _ φ
  have hP := (isPullback_SpecMap_of_isPushout _ _ _ _
    (zpf_pushout φ (ι.ker.ideal V))).paste_vert (zpf_sqA X Z ι V)
  refine ⟨⟨_, hP⟩, ?_⟩
  intro U hU
  have hr : ∀ x, (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ Set.range ι ↔
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) := by
    intro x; constructor
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      refine ⟨hP.isoPullback.inv a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]; exact ha
    · rintro ⟨a, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm.trans
        ((congrArg (fun k => k a) hP.w.symm).trans (Scheme.Hom.comp_apply _ _ a))⟩
  ext x
  have h1 : x ∈ off B ((ι.ker.ideal V).map φ) ↔ x ∉ PrimeSpectrum.zeroLocus (((ι.ker.ideal V).map φ : Ideal B) : Set B) :=
    Iff.rfl
  have h2 : x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U ↔
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ (U : Set X) := Iff.rfl
  simp only [SetLike.mem_coe]
  rw [h1, h2, hU, Set.mem_compl_iff, hr, zpf_range_mk]
  exact Iff.rfl
