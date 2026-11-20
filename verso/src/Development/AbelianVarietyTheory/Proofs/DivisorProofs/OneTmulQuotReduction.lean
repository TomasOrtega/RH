import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
