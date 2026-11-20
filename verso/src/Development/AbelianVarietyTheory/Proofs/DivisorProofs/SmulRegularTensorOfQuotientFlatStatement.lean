import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulRegularTensorOfQuotientFlat
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSMulRegular_tensor_of_flat_quot` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmulRegularTensorOfQuotientFlat.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.smul_regular_tensor_of_quotient_flat : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  IsSMulRegular M f → Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M) →
  ∀ (N : Type) [AddCommGroup N] [Module A N], IsSMulRegular N f → IsSMulRegular (TensorProduct A N M) f := by
  first | exact @GlobalTheory.isSMulRegular_tensor_of_flat_quot | exact GlobalTheory.isSMulRegular_tensor_of_flat_quot | (intros; apply GlobalTheory.isSMulRegular_tensor_of_flat_quot <;> assumption)
