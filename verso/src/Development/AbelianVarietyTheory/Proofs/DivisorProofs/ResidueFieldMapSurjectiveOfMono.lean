import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra K L := φ.hom.toAlgebra`. Establish `h : ∀ a : L, (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] a`. Introduce `a`. Establish `e : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R` using `K) (A := L) (B := L)) = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom := by`. Rewrite using `[← cancel_epi φ]`.

Use extensionality with `c`. Conclude with `congr($(Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := K) (A := L) (B := L)) c)`. Conclude with `congr(($e).hom a)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L) (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)`. Establish `g1 : g 1 = 1` using `by simpa using congr($hg 1)`.

Introduce `a`. Use `⟨g a, ?_⟩` and prove the remaining obligations. Use `congr(TensorProduct.rid K L (LinearMap.lTensor L g $(h a)))` as an intermediate fact. Simplify using `only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at this`. Conclude with `(Algebra.algebraMap_eq_smul_one (A := L) (g a)).trans this.symm`.
-/
theorem surjective_of_epi_of_field_to_field {K L : Type} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) [Epi φ] : Function.Surjective φ.hom := by
  letI : Algebra K L := φ.hom.toAlgebra
  have h : ∀ a : L, (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] a := by
    intro a
    have e : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L))
        = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom := by
      rw [← cancel_epi φ]
      ext c
      exact congr($(Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := K) (A := L) (B := L)) c)
    exact congr(($e).hom a)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have g1 : g 1 = 1 := by simpa using congr($hg 1)
  intro a
  refine ⟨g a, ?_⟩
  have := congr(TensorProduct.rid K L (LinearMap.lTensor L g $(h a)))
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at this
  exact (Algebra.algebraMap_eq_smul_one (A := L) (g a)).trans this.symm

/- English proof (translation)
Establish `h1 : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x))`. Rewrite using `[Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]`. Use `infer_instance`. Establish `h2 : Mono (Spec.map (f.residueFieldMap x))` using `mono_of_mono _ (Y.fromSpecResidueField (f x))`. Establish `h3 : Mono (f.residueFieldMap x).op` using `Scheme.Spec.mono_of_mono_map (f := (f.residueFieldMap x).op) h2`.

Establish `h4 : Epi (f.residueFieldMap x)` using `(CategoryTheory.op_mono_iff _).1 h3`. Conclude with `surjective_of_epi_of_field_to_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)`.
-/
theorem residueFieldMap_surjective_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by
  have h1 : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have h2 : Mono (Spec.map (f.residueFieldMap x)) := mono_of_mono _ (Y.fromSpecResidueField (f x))
  have h3 : Mono (f.residueFieldMap x).op :=
    Scheme.Spec.mono_of_mono_map (f := (f.residueFieldMap x).op) h2
  have h4 : Epi (f.residueFieldMap x) := (CategoryTheory.op_mono_iff _).1 h3
  exact surjective_of_epi_of_field_to_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)

end GlobalTheory
