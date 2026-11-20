import Mathlib

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set I : Ideal B := RingHom.ker (algebraMap B k) with hI`. Set `f : (B ⧸ I) →ₗ[B] k` to `Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)`.

Establish `hinj : Function.Injective (f.rTensor C)` using `Module.Flat.rTensor_preserves_injective_linearMap f hf`. Establish `hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0`. Apply `hinj` to reduce the goal to its premises. Establish `h1 : f (Ideal.Quotient.mk I 1) = 1` using `by show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1`. Rewrite using `[Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]`.

Rewrite using `[LinearMap.rTensor_tmul, map_zero, h1]`. Conclude with `h`. Establish `hq` using `congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx`. Rewrite `hq` using `[TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite `hq` using `[Ideal.smul_top_eq_map]`.

Conclude with `hq`.
-/
theorem mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq

end GlobalTheory
