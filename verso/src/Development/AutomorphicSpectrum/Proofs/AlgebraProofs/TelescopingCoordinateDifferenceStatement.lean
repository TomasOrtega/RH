import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TelescopingCoordinateDifference

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FTelescopingCoordinateDifference.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.telescoping_coordinate_difference : ∀ (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α), F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  first | exact @GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | exact GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | (intros; apply GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions <;> assumption)
