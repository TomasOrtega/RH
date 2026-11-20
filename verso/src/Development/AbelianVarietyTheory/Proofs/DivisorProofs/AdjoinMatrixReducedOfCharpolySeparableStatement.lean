import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparable
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdjoinMatrixReducedOfCharpolySeparable.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable : ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable → ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  first | exact @GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | exact GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | (intros; apply GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable <;> assumption)
