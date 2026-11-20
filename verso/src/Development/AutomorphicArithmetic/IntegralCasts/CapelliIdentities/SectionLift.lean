import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.Yt7.Sp R' ⟶ UpperTheory.Reformulated.B.Yt7.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

open CategoryTheory AlgebraicGeometry in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.Yt7.ring_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {A : Type} [CommRing A] (φ : R →+* A) (hφ : φ.Finite)
    (ψ : A →+* K) (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, σ.comp φ = RingHom.id R ∧ (algebraMap R K).comp σ = ψ := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have hi : (algebraMap R K).IsIntegralElem (ψ a) := by
      rw [← h]
      exact (hφ.to_isIntegral a).map ψ
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let e : R ≃+* (algebraMap R K).range :=
    RingEquiv.ofBijective (algebraMap R K).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have key : ∀ a : A, algebraMap R K (e.symm ⟨ψ a, hmem a⟩) = ψ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext r
    apply hinj
    exact (key (φ r)).trans (RingHom.congr_fun h r)
  · ext a
    exact key a

open CategoryTheory AlgebraicGeometry in
/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.Yt7.section_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {P : Scheme} (g : P ⟶ Spec (CommRingCat.of R)) [IsFinite g]
    (s : Spec (CommRingCat.of K) ⟶ P)
    (h : s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ P,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t = s := by
  have : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ g)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (s ≫ P.isoSpec.hom)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, ← h]
    simp
  obtain ⟨σ, h1, h2⟩ := UpperTheory.Reformulated.B.Yt7.ring_lift (K := K) φ.hom hfin ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1' : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h1
  have h2' : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h1', Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h2', hψ]
    simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.Yt7.lift_finite :
    ∀ {R K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K]
      [IsIntegrallyClosed R] {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
      (y : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ S) (w : UpperTheory.Reformulated.B.Yt7.Sp K ⟶ X),
      CategoryTheory.CategoryStruct.comp w f =
          CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) y →
        ∃ (v : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ X),
          CategoryTheory.CategoryStruct.comp v f = y ∧
            CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) v = w := by
  intro R K _ _ _ _ _ _ X S f _ y w h
  obtain ⟨t, ht1, ht2⟩ := UpperTheory.Reformulated.B.Yt7.section_lift (K := K) (CategoryTheory.Limits.pullback.snd f y)
    (CategoryTheory.Limits.pullback.lift w _ h) (CategoryTheory.Limits.pullback.lift_snd _ _ _)
  refine ⟨CategoryTheory.CategoryStruct.comp t (CategoryTheory.Limits.pullback.fst f y), ?_, ?_⟩
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.condition,
      ← CategoryTheory.Category.assoc, ht1, CategoryTheory.Category.id_comp]
  · rw [← CategoryTheory.Category.assoc, ht2, CategoryTheory.Limits.pullback.lift_fst]
