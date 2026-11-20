import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCompletionFirstColumn
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixCompletionFirstColumn.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.matrix_completion_first_column : ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  first | exact @GlobalTheory.frame_first_column_first_row | exact GlobalTheory.frame_first_column_first_row | (intros; apply GlobalTheory.frame_first_column_first_row <;> assumption)
