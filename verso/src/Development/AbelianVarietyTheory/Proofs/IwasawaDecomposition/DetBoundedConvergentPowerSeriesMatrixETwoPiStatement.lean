import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDetBoundedConvergentPowerSeriesMatrixETwoPi.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  first | exact @GlobalTheory.det_bounded_eTwoPi | exact GlobalTheory.det_bounded_eTwoPi | (intros; apply GlobalTheory.det_bounded_eTwoPi <;> assumption)
