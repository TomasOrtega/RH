import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionTensorQuotientRingEquiv
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adicCompletion_tensor_quotient_ringEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdicCompletionTensorQuotientRingEquiv.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective : ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R] [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K], Function.Surjective (algebraMap R₀ R) → Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+* AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  first | exact @GlobalTheory.adicCompletion_tensor_quotient_ringEquiv | exact GlobalTheory.adicCompletion_tensor_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_tensor_quotient_ringEquiv <;> assumption)
