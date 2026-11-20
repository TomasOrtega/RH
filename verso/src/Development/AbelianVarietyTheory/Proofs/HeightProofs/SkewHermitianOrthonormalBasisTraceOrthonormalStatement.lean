import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FSkewHermitianOrthonormalBasisTraceOrthonormal.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length), (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | exact GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal <;> assumption)
