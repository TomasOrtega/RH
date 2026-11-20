import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductIntegralFinite
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProductIntegralFinite.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.product_integral_finite : ∀ {e : ℕ} (r : ℝ) (f : Fin e → ℂ → ENNReal), (∀ k, Measurable (f k)) → (∀ k, ∫⁻ u in Metric.ball (0 : ℂ) r, f k u < ⊤) → ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) < ⊤ := by
  first | exact @GlobalTheory.setLIntegral_ball_pi_prod_lt_top' | exact GlobalTheory.setLIntegral_ball_pi_prod_lt_top' | (intros; apply GlobalTheory.setLIntegral_ball_pi_prod_lt_top' <;> assumption)
