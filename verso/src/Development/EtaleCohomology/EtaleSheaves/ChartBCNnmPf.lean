import Development.EtaleCohomology.EtaleSheaves.ProjectiveLineTwoAffineChartsPolynomialGenerated

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData LateralTheory.E.ProjectiveLineCharts₂

namespace LateralTheory.E.ChartBC_nnmPf

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem res_bijective {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  have : (homOfLE h) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pushout_gen {Z X Y P : CommRingCat.{0}} {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (R : Subring P) (hi : ∀ x, i x ∈ R) (hj : ∀ y, j y ∈ R) (p : P) : p ∈ R := by
  let i' : X ⟶ CommRingCat.of R := CommRingCat.ofHom (i.hom.codRestrict R hi)
  let j' : Y ⟶ CommRingCat.of R := CommRingCat.ofHom (j.hom.codRestrict R hj)
  have w' : f ≫ i' = g ≫ j' := by
    ext z
    have := congrArg (fun φ => φ.hom z) h.w
    simpa [i', j'] using this
  let σ := h.desc i' j' w'
  have hσ : σ ≫ CommRingCat.ofHom R.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc]; ext; rfl
    · rw [h.inr_desc_assoc]; ext; rfl
  have := congrArg (fun φ => φ.hom p) hσ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  rw [← this]; exact (σ.hom p).2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem restrict_appTop_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ (f ∣_ U).appTop =
      f.app U ≫ X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).le).op := by
  rw [morphismRestrict_appTop]
  have e := f.naturality (homOfLE (Scheme.Opens.ι_image_top U).le).op
  calc _ = (Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ f.app (U.ι ''ᵁ ⊤)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc, ← Functor.map_comp]; rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem snd_eq {A : Type} [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (V : L.Opens) :
    (V.ι ≫ l).appTop = l.appLE ⊤ V le_top ≫ L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top V).le).op := by
  unfold Scheme.Hom.appLE
  rw [Category.assoc, ← Functor.map_comp]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ChartBC_of : ChartBC := by
  intro A _ L l f hf W x hW hsx
  have hpb := IsPullback.paste_vert (isPullback_morphismRestrict f W) hf
  have : IsAffine W.toScheme := hW
  have hA : IsAffineOpen (f ⁻¹ᵁ W) := IsAffine.of_isPullback hpb
  refine ⟨hA, ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hA
  have hpo := isPushout_appTop_of_isPullback hpb
  let ψ := L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le).op
  have hψ := res_bijective (X := L) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).ge
  let R : Subring Γ((f ⁻¹ᵁ W).toScheme, ⊤) :=
    (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x)).range.map ψ.hom
  intro t
  have ht : ψ t ∈ R := pushout_gen hpo R ?_ ?_ (ψ t)
  · obtain ⟨r, ⟨q, rfl⟩, hr⟩ := Subring.mem_map.mp ht
    exact ⟨q, hψ.1 hr⟩
  · intro w
    obtain ⟨w0, rfl⟩ := (res_bijective (X := P1) (Scheme.Opens.ι_image_top W).le
      (Scheme.Opens.ι_image_top W).ge).2 w
    have h1 : (f ∣_ W).appTop (P1.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op w0) =
        ψ (f.app W w0) := congrArg (fun φ => φ.hom w0) (restrict_appTop_eq f W)
    erw [h1]
    obtain ⟨q, rfl⟩ := hsx w0
    refine Subring.mem_map.mpr ⟨_, ⟨q.map (Int.castRingHom A), rfl⟩, ?_⟩
    congr 1
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    congr 1; exact RingHom.ext_int _ _
  · intro a
    refine Subring.mem_map.mpr ⟨_, ⟨Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a), rfl⟩, ?_⟩
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, snd_eq]
    simp only [rA, RingHom.comp_apply]
    erw [Iso.hom_inv_id_apply]
    rfl

end LateralTheory.E.ChartBC_nnmPf
