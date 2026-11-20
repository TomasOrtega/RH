import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddings
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogCardQuotSpanEqFinsumLogNormEmbeddings.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B), b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧ Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | exact GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | (intros; apply GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm <;> assumption)
