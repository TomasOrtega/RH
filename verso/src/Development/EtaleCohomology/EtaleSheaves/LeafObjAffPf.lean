import Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjAffPf

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem desc_spec (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] (A : Type) [CommRing A]
    [Algebra Ω A] [Algebra.FinitePresentation Ω A] :
    Desc k (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) := by
  let P := Algebra.Presentation.ofFinitePresentation Ω A
  let R : Subalgebra k Ω := Algebra.adjoin k P.coeffs
  have : P.HasCoeffs R := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let B := P.ModelOfHasCoeffs R
  let e : Ω ⊗[R] B ≃ₐ[Ω] A := P.tensorModelOfHasCoeffsEquiv R
  have hR : R.FG := ⟨P.finite_coeffs.toFinset, by simp [R]⟩
  let gB : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.toRingEquiv.toCommRingCatIso.hom
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Ω)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap Ω A)) gB := by
    refine (CommRingCat.isPushout_tensorProduct R Ω B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change e (x ⊗ₜ 1) = algebraMap Ω A x
      simpa [Algebra.TensorProduct.algebraMap_apply] using e.commutes x
    · simp [gB]
  refine ⟨R, hR, Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap R B)), _, ?_,
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem desc_of_iso (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (i : X ≅ Y) (g : Y ⟶ Sp Ω) (h : Desc k g) : Desc k (i.hom ≫ g) := by
  obtain ⟨R, hR, D, q, v, hq, hpb⟩ := h
  exact ⟨R, hR, D, q, i.hom ≫ v, hq,
    hpb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Equip the data with the indicated structure.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LeafObjAff_of : LeafObjAff := by
  intro k _ Ω _ _ X f hX hf
  obtain ⟨h1, h2, h3⟩ := hf
  let g : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of Ω) := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  letI : Algebra Ω Γ(X, ⊤) := φ.hom.toAlgebra
  have hg : LocallyOfFinitePresentation g := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤))) = g := Spec.map_preimage g
  have hfp : Algebra.FinitePresentation Ω Γ(X, ⊤) := by
    rw [← Spec.map_preimage g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hg
    exact hg
  have := desc_spec k (Ω := Ω) Γ(X, ⊤)
  rw [hφ] at this
  have hf' : f = X.isoSpec.hom ≫ g := by simp [g]
  rw [hf']
  exact desc_of_iso k X.isoSpec g this

end LateralTheory.E.LeafObjAffPf
