import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIte
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FReTraceHermitianOrthonormalBasisMulEqIte.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length), (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.pB_orthonormal | exact GlobalTheory.TypeSum.CasBasis.pB_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.pB_orthonormal <;> assumption)
