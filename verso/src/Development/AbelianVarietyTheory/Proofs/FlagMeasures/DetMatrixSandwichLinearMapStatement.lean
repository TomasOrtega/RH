import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDetMatrixSandwichLinearMap.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.det_matrix_sandwich_linear_map : ∀ (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ) (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ)), (∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) → LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first | exact @GlobalTheory.MatMulDet.det_real_mul_mul | exact GlobalTheory.MatMulDet.det_real_mul_mul | (intros; apply GlobalTheory.MatMulDet.det_real_mul_mul <;> assumption)
