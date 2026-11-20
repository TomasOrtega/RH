import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.HomExt

/- English proof (translation)
Establish `hs : Function.Surjective (pullback.fst x j)`. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]`. Conclude with `fun t ↦ h ⟨t, rfl⟩`. Establish `hp : IsPreimmersion (pullback.fst x j)` using `inferInstance`. Establish `: IsIso (pullback.fst x j)`.

Rewrite using `[isIso_iff_isIso_stalkMap]`. Use `⟨?_, isIso_stalkMap_of_flat_of_surjectiveOnStalks _⟩` and prove the remaining obligations. Conclude with `TopCat.isIso_of_bijective_of_isOpenMap _ ⟨hp.isEmbedding.injective, hs⟩ (hp.isEmbedding.isInducing.isOpenMap (by rw [hs.range_eq]; exact isOpen_univ))`. Conclude with `⟨inv (pullback.fst x j) ≫ pullback.snd x j, by`. Rewrite using `[Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩`.
-/
theorem exists_lift_of_range_subset {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (x : T ⟶ X) (h : Set.range x ⊆ Set.range j) : ∃ y : T ⟶ U, y ≫ j = x := by
  have hs : Function.Surjective (pullback.fst x j) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    exact fun t ↦ h ⟨t, rfl⟩
  have hp : IsPreimmersion (pullback.fst x j) := inferInstance
  have : IsIso (pullback.fst x j) := by
    rw [isIso_iff_isIso_stalkMap]
    refine ⟨?_, isIso_stalkMap_of_flat_of_surjectiveOnStalks _⟩
    exact TopCat.isIso_of_bijective_of_isOpenMap _ ⟨hp.isEmbedding.injective, hs⟩
      (hp.isEmbedding.isInducing.isOpenMap (by rw [hs.range_eq]; exact isOpen_univ))
  exact ⟨inv (pullback.fst x j) ≫ pullback.snd x j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

/- English proof (translation)
Take `⟨⟨w, φ⟩, rfl⟩` from `(Scheme.SpecToEquivOfField k Z).symm.surjective c`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at hz ⊢`. Choose the witnesses or unpack the hypotheses as in `rfl : z = w := by`. Take `⟨t, rfl⟩` from `hz`. Conclude with `(Scheme.Hom.comp_apply _ _ t).trans (Scheme.fromSpecResidueField_apply w _)`.

Establish `: Flat (Spec.map φ)`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Use `letI := φ.hom.toAlgebra`. Conclude with `RingHom.flat_algebraMap_iff.mpr inferInstance`. Establish `: Surjective (Spec.map φ)` using `⟨fun t ↦ ⟨default, Subsingleton.elim _ _⟩⟩`.

Establish `: Epi (Spec.map φ)` using `Flat.epi_of_flat_of_surjective _`. Rewrite using `[Category.assoc, Category.assoc, cancel_epi]`.
-/
theorem field_point_comp_eq_iff {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {k : Type} [Field k]
    (c : Spec (.of k) ⟶ Z) (z : Z) (hz : z ∈ Set.range c) :
    c ≫ g = c ≫ g' ↔ Z.fromSpecResidueField z ≫ g = Z.fromSpecResidueField z ≫ g' := by
  obtain ⟨⟨w, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective c
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz ⊢
  obtain rfl : z = w := by
    obtain ⟨t, rfl⟩ := hz
    exact (Scheme.Hom.comp_apply _ _ t).trans (Scheme.fromSpecResidueField_apply w _)
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨fun t ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective _
  rw [Category.assoc, Category.assoc, cancel_epi]

/- English proof (translation)
Establish `hP : Finite ↥(pullback f y)`. Use `finite_of_finite_sections (pullback.snd f y) ?_` and prove the remaining obligations. Use `Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) (fun x ↦ ⟨x.1 ≫ pullback.fst f y, by` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_`. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`. Rewrite using `[a.2, b.2]`. Rewrite using `[← Scheme.Pullback.range_fst]`.

Conclude with `Set.finite_range _`.
-/
theorem finite_preimage_of_finite_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (f ⁻¹' Set.range y).Finite := by
  have hP : Finite ↥(pullback f y) := by
    refine finite_of_finite_sections (pullback.snd f y) ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  rw [← Scheme.Pullback.range_fst]
  exact Set.finite_range _

/- English proof (translation)
Take `⟨w₀, hw₀⟩` from `genericPoints_subset_range_of_isDominant (i ≫ p) (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])`. Establish `hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ)`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite using `[← i.denseRange.closure_range]`. Use `closure_minimal ?_ isClosed_closure` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, rfl⟩`. Establish `h : w₀ ⤳ w`. Rewrite using `[← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]`. Conclude with `genericPoint_specializes _`. Conclude with `specializes_iff_mem_closure.mp (h.map i.continuous)`.

Establish `: IrreducibleSpace Γ` using `(irreducibleSpace_def Γ).mpr hgen.isIrreducible`. Establish `: IsIntegral Γ` using `isIntegral_of_irreducibleSpace_of_isReduced Γ`. Establish `he : i w₀ = genericPoint Γ` using `hgen.eq (genericPoint_spec Γ)`. Establish `: IsIso (p.stalkMap (genericPoint Γ))`. Rewrite using `[← he]`.

Establish `h₁` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀`. Establish `h₂` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀`. Rewrite `h₁` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `@IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁`. Use `isOpenImmersion_of_quasiFinite_of_isIso_stalkMap p (fun y ↦ inferInstance)` as an intermediate fact.

Conclude with `(isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, inferInstance⟩`.
-/
theorem isIso_of_densePart_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  obtain ⟨w₀, hw₀⟩ := genericPoints_subset_range_of_isDominant (i ≫ p)
    (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])
  have hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← i.denseRange.closure_range]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have h : w₀ ⤳ w := by
      rw [← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]
      exact genericPoint_specializes _
    exact specializes_iff_mem_closure.mp (h.map i.continuous)
  have : IrreducibleSpace Γ := (irreducibleSpace_def Γ).mpr hgen.isIrreducible
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have he : i w₀ = genericPoint Γ := hgen.eq (genericPoint_spec Γ)
  have : IsIso (p.stalkMap (genericPoint Γ)) := by
    rw [← he]
    have h₁ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀
    have h₂ := isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀
    rw [Scheme.Hom.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁
  have := isOpenImmersion_of_quasiFinite_of_isIso_stalkMap p (fun y ↦ inferInstance)
  exact (isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Set `V : Y → Y.Opens` to `fun y ↦ ⟨irreducibleComponent y, IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents y)⟩`. Establish `hV : iSup V = ⊤`. Rewrite using `[eq_top_iff]`. Conclude with `fun y _ ↦ Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩`. Use `(IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hV).mpr fun y ↦ ?_` and prove the remaining obligations.

Establish `: IrreducibleSpace (V y).toScheme` using `Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))`. Establish `: IsIntegral (V y).toScheme` using `IsNormalScheme.isIntegral_of_irreducibleSpace _`. Establish `e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y` using `morphismRestrict_comp _ _ _`. Establish `: IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y))` using `IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: IsDominant (i ∣_ (p ⁻¹ᵁ V y))` using `IsZariskiLocalAtTarget.restrict ‹_› _`.

Establish `: IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›`. Establish `: QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›`. Establish `: Surjective (p ∣_ V y)` using `IsZariskiLocalAtTarget.restrict ‹_› _`.

Establish `: LocallyQuasiFinite (p ∣_ V y)` using `MorphismProperty.of_isPullback (isPullback_morphismRestrict p (V y)).flip ‹_›`. Conclude with `isIso_of_densePart_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)`.
-/
theorem isIso_of_densePart {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  let V : Y → Y.Opens := fun y ↦ ⟨irreducibleComponent y,
    IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents y)⟩
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    exact fun y _ ↦ Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    V hV).mpr fun y ↦ ?_
  have : IrreducibleSpace (V y).toScheme :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))
  have : IsIntegral (V y).toScheme := IsNormalScheme.isIntegral_of_irreducibleSpace _
  have e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y := morphismRestrict_comp _ _ _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : Surjective (p ∣_ V y) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : LocallyQuasiFinite (p ∣_ V y) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p (V y)).flip ‹_›
  exact isIso_of_densePart_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)

end GlobalTheory.HomExt
