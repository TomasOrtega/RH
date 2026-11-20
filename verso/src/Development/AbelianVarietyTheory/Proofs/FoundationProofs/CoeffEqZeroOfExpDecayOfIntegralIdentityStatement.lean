import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfExpDecayOfIntegralIdentity
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ode_coeff_zero_of_decay_ends` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCoeffEqZeroOfExpDecayOfIntegralIdentity.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  first | exact @GlobalTheory.ode_coeff_zero_of_decay_ends | exact GlobalTheory.ode_coeff_zero_of_decay_ends | (intros; apply GlobalTheory.ode_coeff_zero_of_decay_ends <;> assumption)
