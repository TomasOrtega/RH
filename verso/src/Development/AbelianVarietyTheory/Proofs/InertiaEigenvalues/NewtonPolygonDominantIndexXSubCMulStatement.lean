import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMul
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNewtonPolygonDominantIndexXSubCMul.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  first | exact @GlobalTheory.newton_step_root_outside_disc | exact GlobalTheory.newton_step_root_outside_disc | (intros; apply GlobalTheory.newton_step_root_outside_disc <;> assumption)
