import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `hH : HenselianLocalRing (CommRingCat.of A)` using `inferInstanceAs (HenselianLocalRing A)`. Establish `hfin : IsFinite ((finitePart π).ι ≫ π)` using `isFinite_finitePart (R := .of A) π`. Establish `haff : IsAffine (finitePart π).toScheme` using `isAffine_of_isAffineHom ((finitePart π).ι ≫ π)`. Set `e : Spec Γ((finitePart π).toScheme, ⊤) ≅ (finitePart π).toScheme` to `(finitePart π).toScheme.isoSpec.symm`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (e.hom ≫ (finitePart π).ι ≫ π)`.

Establish `h₁ : φ.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hφ]`. Use `infer_instance`. Establish `h₂ : φ.hom.Flat`. Rewrite using `[← Flat.SpecMap_iff, hφ]`.

Use `infer_instance`. Use `letI alg : Algebra A Γ((finitePart π).toScheme, ⊤) := φ.hom.toAlgebra`. Establish `i₁ : Module.Finite A Γ((finitePart π).toScheme, ⊤)` using `h₁`. Establish `i₂ : Module.Flat A Γ((finitePart π).toScheme, ⊤)` using `h₂`. Conclude with `⟨Γ((finitePart π).toScheme, ⊤), inferInstance, alg, i₁, Module.free_of_flat_of_isLocalRing, finitePart π, e, hφ.symm, fun t ht ↦ mem_finitePart_of_eq_closedPoint (R := .of A) π t ht⟩`.
-/
theorem exists_finite_free_chart_of_henselian (A : Type) [CommRing A] [HenselianLocalRing A]
    (T : Scheme.{0}) (π : T ⟶ Sp A) [IsSeparated π]
    [LocallyOfFinitePresentation π] [QuasiCompact π] [LocallyQuasiFinite π] [Flat π] :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Module.Finite A C) (_ : Module.Free A C)
      (U : T.Opens) (e : Sp C ≅ U.toScheme), e.hom ≫ U.ι ≫ π = spMap (algebraMap A C) ∧
        ∀ t : T, π t = IsLocalRing.closedPoint A → t ∈ U := by
  have hH : HenselianLocalRing (CommRingCat.of A) := inferInstanceAs (HenselianLocalRing A)
  have hfin : IsFinite ((finitePart π).ι ≫ π) := isFinite_finitePart (R := .of A) π
  have haff : IsAffine (finitePart π).toScheme := isAffine_of_isAffineHom ((finitePart π).ι ≫ π)
  let e : Spec Γ((finitePart π).toScheme, ⊤) ≅ (finitePart π).toScheme :=
    (finitePart π).toScheme.isoSpec.symm
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.hom ≫ (finitePart π).ι ≫ π)
  have h₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have h₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  letI alg : Algebra A Γ((finitePart π).toScheme, ⊤) := φ.hom.toAlgebra
  have i₁ : Module.Finite A Γ((finitePart π).toScheme, ⊤) := h₁
  have i₂ : Module.Flat A Γ((finitePart π).toScheme, ⊤) := h₂
  exact ⟨Γ((finitePart π).toScheme, ⊤), inferInstance, alg, i₁,
    Module.free_of_flat_of_isLocalRing, finitePart π, e, hφ.symm,
    fun t ht ↦ mem_finitePart_of_eq_closedPoint (R := .of A) π t ht⟩

end GlobalTheory
