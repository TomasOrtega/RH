import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulIndexSqsInvolution
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FTwoMulIndexSqsInvolution.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  first | exact @GlobalTheory.QNorm.two_mul_index_sqs_involution | exact GlobalTheory.QNorm.two_mul_index_sqs_involution | (intros; apply GlobalTheory.QNorm.two_mul_index_sqs_involution <;> assumption)
