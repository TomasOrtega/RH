import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.cosetPrimeDet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIntMatrixPrimeDetCosetRepresentatives.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.intMatrix_prime_det_coset_representatives : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q → (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨ ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  first | exact @GlobalTheory.cosetPrimeDet | exact GlobalTheory.cosetPrimeDet | (intros; apply GlobalTheory.cosetPrimeDet <;> assumption)
