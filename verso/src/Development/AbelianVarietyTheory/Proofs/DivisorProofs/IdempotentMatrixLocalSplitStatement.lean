import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentMatrixLocalSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.idempotent_matrix_split_of_isLocalRing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdempotentMatrixLocalSplit.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.idempotent_matrix_local_split : ∀ (A : Type) [CommRing A] [IsLocalRing A] (h : ℕ) (X : Matrix (Fin h) (Fin h) A), X * X = X → ∃ (n : ℕ) (i : Matrix (Fin h) (Fin n) A) (q : Matrix (Fin n) (Fin h) A), q * i = 1 ∧ i * q = X ∧ X.trace = n := by
  first | exact @GlobalTheory.idempotent_matrix_split_of_isLocalRing | exact GlobalTheory.idempotent_matrix_split_of_isLocalRing | (intros; apply GlobalTheory.idempotent_matrix_split_of_isLocalRing <;> assumption)
