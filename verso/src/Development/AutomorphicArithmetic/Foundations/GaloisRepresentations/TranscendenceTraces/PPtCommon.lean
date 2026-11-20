import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `X Ω Ω' _ _ z z' h`. Establish `key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y → ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y`. Introduce `K _ w y hy`. Substitute `hy` using the available equality. Conclude with `⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩`.

Take `⟨x, hx⟩ : ∃ x, pt z = x` from `⟨_, rfl⟩`. Take `⟨φ, hφ⟩` from `key Ω z x hx`. Take `⟨φ', hφ'⟩` from `key Ω' z' x (h.symm.trans hx)`. Establish `i1 : Function.Injective φ.hom` using `φ.hom.injective`. Establish `i2 : Function.Injective φ'.hom` using `φ'.hom.injective`.

Use `letI := φ.hom.toAlgebra`. Use `letI := φ'.hom.toAlgebra`. Use `haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')`. Use `letI := Ideal.Quotient.field M`.

Set `ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M)` to `(algebraMap _ _).comp (Ideal.Quotient.mk M)`. Establish `e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') = (1 : Ω) ⊗ₜ (φ'.hom c)`. Introduce `c`. Express the relevant statement in the definitionally equal form `algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Use `⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)), Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight : Ω' →ₐ[X.residueField x] TensorPro …` and prove the remaining obligations. Rewrite using `[hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `c`. Simplify using `[e1]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.ptCommon_of :
    PtCommon := by
  intro X Ω Ω' _ _ z z' h
  have key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y →
      ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y := by
    intro K _ w y hy
    subst hy
    exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩
  obtain ⟨x, hx⟩ : ∃ x, pt z = x := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := key Ω z x hx
  obtain ⟨φ', hφ'⟩ := key Ω' z' x (h.symm.trans hx)
  have i1 : Function.Injective φ.hom := φ.hom.injective
  have i2 : Function.Injective φ'.hom := φ'.hom.injective
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')
  letI := Ideal.Quotient.field M
  let ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  have e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') =
      (1 : Ω) ⊗ₜ (φ'.hom c) := by
    intro c
    change algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)),
    Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight :
      Ω' →ₐ[X.residueField x] TensorProduct (X.residueField x) Ω Ω').toRingHom)), ?_⟩
  rw [hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [e1]
