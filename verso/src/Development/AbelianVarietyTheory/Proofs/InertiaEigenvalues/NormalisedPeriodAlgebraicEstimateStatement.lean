import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimate
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.normalisedPeriod_algebraic_estimate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormalisedPeriodAlgebraicEstimate.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t → (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z → (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) → ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  first | exact @GlobalTheory.normalisedPeriod_algebraic_estimate | exact GlobalTheory.normalisedPeriod_algebraic_estimate | (intros; apply GlobalTheory.normalisedPeriod_algebraic_estimate <;> assumption)
