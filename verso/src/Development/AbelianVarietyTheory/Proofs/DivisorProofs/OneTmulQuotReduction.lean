import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

/- English proof (translation)
Introduce `O M _ _ _ I`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨b, hb⟩` from `Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M)) (TensorProduct.quotTensorEquivQuotSMul M I y)`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]`. Introduce `b`. Rewrite using `[← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]`. Introduce `a b`. Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, -, hz⟩`. Conclude with `⟨z, hz.symm⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z, Submodule.mem_top, rfl⟩`.
-/
theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
