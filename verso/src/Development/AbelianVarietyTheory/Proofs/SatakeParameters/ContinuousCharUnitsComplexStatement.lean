import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCharUnitsComplex
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FContinuousCharUnitsComplex.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.continuous_units_complex_hom_eq_exp_mul_arg_pow : ∀ ψ : ℂˣ →* ℂˣ, Continuous ψ → ∃ (s : ℂ) (n : ℤ), ∀ z : ℂˣ, (ψ z : ℂ) = Complex.exp (s * Real.log ‖(z : ℂ)‖) * ((z : ℂ) / ‖(z : ℂ)‖) ^ n := by
  first | exact @GlobalTheory.continuous_char_units_complex | exact GlobalTheory.continuous_char_units_complex | (intros; apply GlobalTheory.continuous_char_units_complex <;> assumption)
