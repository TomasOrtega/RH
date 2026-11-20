import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FOrthonormalBasesMemUnitaryLieAlgebra.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet <;> assumption)
