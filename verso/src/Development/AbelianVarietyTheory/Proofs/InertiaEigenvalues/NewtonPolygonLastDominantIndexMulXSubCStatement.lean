import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubC
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.newton_step_root_in_disc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNewtonPolygonLastDominantIndexMulXSubC.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧ ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  first | exact @GlobalTheory.newton_step_root_in_disc | exact GlobalTheory.newton_step_root_in_disc | (intros; apply GlobalTheory.newton_step_root_in_disc <;> assumption)
