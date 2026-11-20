import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBases
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FSignatureLieSetExpandOrthonormalBases.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.signature_lieSet_expand_orthonormal_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε, U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  first | exact @GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | exact GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | (intros; apply GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases <;> assumption)
