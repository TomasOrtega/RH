import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Set `φ : X.presheaf.stalk x ⟶ X.residueField x'` to `X.presheaf.stalkSpecializes h ≫ X.residue x'`. Take `⟨A, hA, hA_local⟩` from `IsLocalRing.exists_factor_valuationRing φ.hom`. Set `ψ : X.presheaf.stalk x ⟶ .of A` to `CommRingCat.ofHom (φ.hom.codRestrict _ hA)`. Establish `w : X.fromSpecResidueField x' = Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫ Spec.map ψ ≫ X.fromSpecStalk x`. Rewrite using `[Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]`.

Repeatedly rewrite using `[← Spec.map_comp_assoc]`. Both sides reduce to the same expression. Use `⟨A, inferInstance, inferInstance, inferInstance, Spec.map ψ ≫ X.fromSpecStalk x, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]`. Establish `: Spec.map ψ (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint (X.presheaf.stalk x)` using `IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)`.

Rewrite using `[this, X.fromSpecStalk_closedPoint]`. Establish `h1 : Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) (IsLocalRing.closedPoint (X.residueField x')) = (⊥ : PrimeSpectrum A)`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap A (X.residueField x')) (IsLocalRing.maximalIdeal (X.residueField x')) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.

Conclude with `Ideal.comap_bot_of_injective _ Subtype.val_injective`. Rewrite using `[← h1, ← Scheme.Hom.comp_apply, ← w, Scheme.fromSpecResidueField_apply]`.
-/
theorem exists_valuationRing_of_specializes (X : Scheme.{0}) (x' x : X) (h : x' ⤳ x) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V)
      (g : Spec (CommRingCat.of V) ⟶ X),
      g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  let φ : X.presheaf.stalk x ⟶ X.residueField x' :=
    X.presheaf.stalkSpecializes h ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk x ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map ψ ≫ X.fromSpecStalk x := by
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, Spec.map ψ ≫ X.fromSpecStalk x, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map ψ (IsLocalRing.closedPoint A) =
        IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [this, X.fromSpecStalk_closedPoint]
  · have h1 : Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x')))
        (IsLocalRing.closedPoint (X.residueField x')) = (⊥ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A (X.residueField x'))
        (IsLocalRing.maximalIdeal (X.residueField x')) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ Subtype.val_injective
    rw [← h1, ← Scheme.Hom.comp_apply, ← w, Scheme.fromSpecResidueField_apply]

end GlobalTheory
