import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsUnitDetKrylovMatrixOfSeparable.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
