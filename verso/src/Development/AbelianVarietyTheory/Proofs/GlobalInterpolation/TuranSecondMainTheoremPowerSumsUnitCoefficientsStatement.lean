import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficients
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTuranSecondMainTheoremPowerSumsUnitCoefficients.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧ ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  first | exact @GlobalTheory.powerSum_second_main | exact GlobalTheory.powerSum_second_main | (intros; apply GlobalTheory.powerSum_second_main <;> assumption)
