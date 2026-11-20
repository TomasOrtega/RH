import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixFieldStableRangeOneDetNeZero
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.matrix_stableRange_one'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMatrixFieldStableRangeOneDetNeZero.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ), c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  first | exact @GlobalTheory.matrix_stableRange_one' | exact GlobalTheory.matrix_stableRange_one' | (intros; apply GlobalTheory.matrix_stableRange_one' <;> assumption)
