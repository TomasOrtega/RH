import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormEquationFromLocalAssociates
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealNormEquationFromLocalAssociates.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.ideal_norm_equation_from_local_associates : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  first | exact @GlobalTheory.CmIdealGlue.glue | exact GlobalTheory.CmIdealGlue.glue | (intros; apply GlobalTheory.CmIdealGlue.glue <;> assumption)
