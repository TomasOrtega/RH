import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureGenericFibreClopenSplitStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem smooth_genericFibre_closure_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R _ _ _ X f hf C C' hU h1 h2
  have key : ∀ (A : CommRingCat.{0}) (j : Spec A ⟶ X) [IsOpenImmersion j],
      Disjoint (j ⁻¹' closure C) (j ⁻¹' closure C') ∧
        (j ⁻¹' closure C) ∪ (j ⁻¹' closure C') = Set.univ := by
    intro A j _
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
    have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
    have hφs : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
    letI : Algebra R A := φ.hom.toAlgebra
    have hA : Algebra.Smooth R A := hφs
    have hcl : ∀ S : Set X, j ⁻¹' closure S = closure (j ⁻¹' S) := fun S =>
      j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous S
    rw [hcl, hcl]
    refine GlobalTheory.T.closure_generic_fibre_clopen_split_alt R A hA (j ⁻¹' C) (j ⁻¹' C') ?_ ?_ ?_
    · have : j ⁻¹' C ∪ j ⁻¹' C' = (Spec.map φ) ⁻¹' {(⊥ : PrimeSpectrum R)} := by
        rw [← Set.preimage_union, hU, hφ, ← Set.preimage_comp, Scheme.Hom.comp_base]
        rfl
      refine this.trans ?_
      ext r
      exact ⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩
    · have := h1.preimage j
      rw [hcl] at this
      exact this
    · have := h2.preimage j
      rw [hcl] at this
      exact this
  constructor
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    exact Set.disjoint_left.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).1 hx hx'
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    exact (Set.eq_univ_iff_forall.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).2) y

end GlobalTheory
