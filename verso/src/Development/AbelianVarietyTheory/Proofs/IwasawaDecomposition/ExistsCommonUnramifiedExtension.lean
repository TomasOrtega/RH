import Mathlib
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k K L _ _ _ i j hf hu`. Use `letI : Algebra k K := i.toAlgebra`. Use `letI : Algebra k L := j.toAlgebra`. Use `haveI : Module.Finite k K := hf`. Use `haveI : Algebra.FormallyUnramified k K := hu`.

Use `haveI : Nontrivial (L ⊗[k] K) := inferInstance`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (L ⊗[k] K)`. Use `letI : Field (L ⊗[k] K ⧸ m) := Ideal.Quotient.field m`. Use `⟨L ⊗[k] K ⧸ m, inferInstance, (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : K →ₐ[k] L ⊗[k] K).toRingHom, algebraMap L (L ⊗[k] K ⧸ m), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a show Ideal.Quotient.mk m (1 ⊗ₜ (algebraMap k K a)) = Ideal.Quotient.mk m (algebraMap L (L ⊗[k] K) (algebraMap k L a))`.

Use `congr 1`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Conclude with `(RingHom.formallyUnramified_algebraMap).mpr inferInstance`.
-/
theorem compositum_finite_formallyUnramified : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  intro k K L _ _ _ i j hf hu
  letI : Algebra k K := i.toAlgebra
  letI : Algebra k L := j.toAlgebra
  haveI : Module.Finite k K := hf
  haveI : Algebra.FormallyUnramified k K := hu
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] K)
  letI : Field (L ⊗[k] K ⧸ m) := Ideal.Quotient.field m
  refine ⟨L ⊗[k] K ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : K →ₐ[k] L ⊗[k] K).toRingHom,
    algebraMap L (L ⊗[k] K ⧸ m), ?_, ?_, ?_⟩
  · ext a
    show Ideal.Quotient.mk m (1 ⊗ₜ (algebraMap k K a)) = Ideal.Quotient.mk m (algebraMap L (L ⊗[k] K) (algebraMap k L a))
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact (RingHom.formallyUnramified_algebraMap).mpr inferInstance

end GlobalTheory
