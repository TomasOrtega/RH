import Mathlib

open scoped TensorProduct

namespace GlobalTheory.FiniteExtensionEmbedding

/- English proof (translation)
Use `haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (K ⊗[ℚ] F)`. Use `letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m`. Use `⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap (Ideal.Quotient.mkₐ_surjective K m)`.

Conclude with `(Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom`.
-/
theorem exists_finite_extension_embedding (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ℚ] F)
  letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  · exact (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom

end GlobalTheory.FiniteExtensionEmbedding
