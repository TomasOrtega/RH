import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLogarithmSpanning
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitLogarithmSpanning.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.unit_logarithm_spanning : ∀ (K : Type) [CommRing K] [IsDomain K] [CharZero K] [Module.Finite ℤ K] (c : (K →+* ℂ) → ℝ),
    (∀ τ, c ((starRingEnd ℂ).comp τ) = c τ) → ∑ᶠ τ, c τ = 0 →
    ∃ (m : ℕ) (a : Fin m → Kˣ) (r : Fin m → ℝ), ∀ τ, c τ = ∑ j, r j * Real.log (‖τ (a j : K)‖ ^ 2) := by
  first | exact @GlobalTheory.UnitSpan.span_log_units | exact GlobalTheory.UnitSpan.span_log_units | (intros; apply GlobalTheory.UnitSpan.span_log_units <;> assumption)
