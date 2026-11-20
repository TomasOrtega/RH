import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hF : Module.Flat T F` using `IsLocalization.flat F (nonZeroDivisors T)`. Establish `hK : Module.Flat T K` using `Module.Flat.trans T F K`. Set `f : U →ₐ[T] L` to `IsScalarTower.toAlgHom T U L`. Set `g : C →ₐ[T] K` to `IsScalarTower.toAlgHom T C K`. Set `e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K` to `IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K`.

Use `⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Establish `hf : Function.Injective f.toLinearMap` using `IsFractionRing.injective U L`. Establish `hg : Function.Injective g.toLinearMap` using `IsFractionRing.injective C K`. Establish `h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap)` using `Module.Flat.lTensor_preserves_injective_linearMap _ hg`. Establish `h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap)` using `Module.Flat.rTensor_preserves_injective_linearMap _ hf`.

Establish `h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap)`. Rewrite using `[← LinearMap.rTensor_comp_lTensor]`. Conclude with `h2.comp h1`. Introduce `x y hxy`. Apply `h3` to reduce the goal to its premises.

Conclude with `e.symm.injective hxy`. Introduce `u c show e.symm (f u ⊗ₜ g c) = _`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression.
-/
theorem flat_tensor_embeds_tensor_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F]
    [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L]
    [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U] :
    ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧
      ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  have hF : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hK : Module.Flat T K := Module.Flat.trans T F K
  let f : U →ₐ[T] L := IsScalarTower.toAlgHom T U L
  let g : C →ₐ[T] K := IsScalarTower.toAlgHom T C K
  let e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K
  refine ⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp
    (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩
  · have hf : Function.Injective f.toLinearMap := IsFractionRing.injective U L
    have hg : Function.Injective g.toLinearMap := IsFractionRing.injective C K
    have h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hg
    have h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    have h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1
    intro x y hxy
    apply h3
    exact e.symm.injective hxy
  · intro u c
    show e.symm (f u ⊗ₜ g c) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl

end GlobalTheory
