import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LUDecomp.lu` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLUDecompositionOfLeadingMinorsNeZero.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  first | exact @GlobalTheory.LUDecomp.lu | exact GlobalTheory.LUDecomp.lu | (intros; apply GlobalTheory.LUDecomp.lu <;> assumption)
