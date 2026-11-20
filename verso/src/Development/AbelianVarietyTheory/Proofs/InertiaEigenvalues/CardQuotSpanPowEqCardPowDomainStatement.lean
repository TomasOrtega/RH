import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomain
import Mathlib
open Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.card_quot_span_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardQuotSpanPowEqCardPowDomain.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  first | exact @GlobalTheory.card_quot_span_pow | exact GlobalTheory.card_quot_span_pow | (intros; apply GlobalTheory.card_quot_span_pow <;> assumption)
