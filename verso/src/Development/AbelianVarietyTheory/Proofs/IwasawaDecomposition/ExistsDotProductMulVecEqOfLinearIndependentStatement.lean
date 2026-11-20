import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDotProductMulVecEqOfLinearIndependent
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsDotProductMulVecEqOfLinearIndependent.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_dotProduct_mulVec_eq_of_linearIndependent' : ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 → LinearIndependent ℚ ε → ∀ t : Fin k → ℚ, ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  first | exact @GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | exact GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | (intros; apply GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent <;> assumption)
