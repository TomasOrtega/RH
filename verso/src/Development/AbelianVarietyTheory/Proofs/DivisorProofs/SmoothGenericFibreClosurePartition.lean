import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureGenericFibreClopenSplitStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ X f hf C C' hU h1 h2`. Establish `key : ∀ (A : CommRingCat.{0}) (j : Spec A ⟶ X) [IsOpenImmersion j], Disjoint (j ⁻¹' closure C) (j ⁻¹' closure C') ∧ (j ⁻¹' closure C) ∪ (j ⁻¹' closure C') = Set.univ`. Introduce `A j _`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (j ≫ f)`. Establish `hs : Smooth (Spec.map φ)` using `by rw [hφ]; infer_instance`.

Establish `hφs : φ.hom.Smooth` using `(HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs`. Use `letI : Algebra R A := φ.hom.toAlgebra`. Establish `hA : Algebra.Smooth R A` using `hφs`. Establish `hcl : ∀ S : Set X, j ⁻¹' closure S = closure (j ⁻¹' S)` using `fun S => j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous S`. Rewrite using `[hcl, hcl]`.

Use `GlobalTheory.T.closure_generic_fibre_clopen_split_alt R A hA (j ⁻¹' C) (j ⁻¹' C') ?_ ?_ ?_` and prove the remaining obligations. Establish `: j ⁻¹' C ∪ j ⁻¹' C' = (Spec.map φ) ⁻¹' {(⊥ : PrimeSpectrum R)}`. Rewrite using `[← Set.preimage_union, hU, hφ, ← Set.preimage_comp, Scheme.Hom.comp_base]`. Both sides reduce to the same expression. Use `this.trans ?_` and prove the remaining obligations.

Use extensionality with `r`. Conclude with `⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩`. Use `h1.preimage j` as an intermediate fact. Rewrite `this` using `[hcl]`. Conclude with `this`.

Use `h2.preimage j` as an intermediate fact. Rewrite `this` using `[hcl]`. Conclude with `this`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Set.disjoint_left]`.

Introduce `x hx hx'`. Take `⟨i, y, rfl⟩` from `X.affineCover.exists_eq x`. Conclude with `Set.disjoint_left.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).1 hx hx'`. Rewrite using `[Set.eq_univ_iff_forall]`. Introduce `x`.

Take `⟨i, y, rfl⟩` from `X.affineCover.exists_eq x`. Conclude with `(Set.eq_univ_iff_forall.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).2) y`.
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
