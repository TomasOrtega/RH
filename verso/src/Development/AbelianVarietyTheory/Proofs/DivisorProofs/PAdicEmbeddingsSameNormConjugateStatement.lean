import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingsSameNormConjugate
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPAdicEmbeddingsSameNormConjugate.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.p_adic_embeddings_same_norm_conjugate : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι ι' : AlgebraicClosure F →+* ℂ_[p]), (∀ a, ‖ι a‖ = ‖ι' a‖) → ∃ σ : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖σ z‖ = ‖z‖) ∧ ∀ a, σ (ι' a) = ι a := by
  first | exact @GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv | exact GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv | (intros; apply GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv <;> assumption)
