import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOneAddLowRankEmbeddingQuaternionMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.emb_qm_continuous` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousOneAddLowRankEmbeddingQuaternionMatrix.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  first | exact @GlobalTheory.emb_qm_continuous | exact GlobalTheory.emb_qm_continuous | (intros; apply GlobalTheory.emb_qm_continuous <;> assumption)
