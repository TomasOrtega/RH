import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentMatrixPowDimEqZero
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNilpotentMatrixPowDimEqZero.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.nilpotent_matrix_pow_dim_eq_zero : ∀ (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ), IsNilpotent X → X ^ d = 0 := by
  first | exact @GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent | exact GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent <;> assumption)
