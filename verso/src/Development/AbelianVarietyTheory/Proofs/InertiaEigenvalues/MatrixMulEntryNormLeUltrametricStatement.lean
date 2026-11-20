import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametric
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.matrix_mul_entry_norm_le_ultrametric` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMatrixMulEntryNormLeUltrametric.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.norm_mul_apply_le_of_ultrametric : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) → ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  first | exact @GlobalTheory.matrix_mul_entry_norm_le_ultrametric | exact GlobalTheory.matrix_mul_entry_norm_le_ultrametric | (intros; apply GlobalTheory.matrix_mul_entry_norm_le_ultrametric <;> assumption)
