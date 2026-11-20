import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedFieldTensorIntFiniteReduced
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsReducedFieldTensorIntFiniteReduced.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.isReduced_field_tensor_int_finite_reduced : ∀ (A : Type) [CommRing A] [Finite A] [IsReduced A] (k : Type) [Field k], IsReduced (k ⊗[ℤ] A) := by
  first | exact @GlobalTheory.FinRedTensor.isReduced_field_tensor_finite | exact GlobalTheory.FinRedTensor.isReduced_field_tensor_finite | (intros; apply GlobalTheory.FinRedTensor.isReduced_field_tensor_finite <;> assumption)
