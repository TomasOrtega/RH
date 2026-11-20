import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLengthQuotientSpanPowLeMulLength.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.length_quotient_span_pow_le_mul_length : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ), Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  first | exact @GlobalTheory.main | exact GlobalTheory.main | (intros; apply GlobalTheory.main <;> assumption)
