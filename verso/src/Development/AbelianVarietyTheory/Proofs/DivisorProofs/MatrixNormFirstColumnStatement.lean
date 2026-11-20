import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormFirstColumn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TriFrame.matNorm_zero_eq_sup'` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixNormFirstColumn.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.matrix_norm_first_column : ∀ {C : Type} [NontriviallyNormedField C] {r : ℕ} (N : Matrix (Fin (r+1)) (Fin (r+1)) C), matNorm N 0 = Finset.univ.sup' Finset.univ_nonempty (fun l => ‖N l 0‖) := by
  first | exact @GlobalTheory.TriFrame.matNorm_zero_eq_sup' | exact GlobalTheory.TriFrame.matNorm_zero_eq_sup' | (intros; apply GlobalTheory.TriFrame.matNorm_zero_eq_sup' <;> assumption)
