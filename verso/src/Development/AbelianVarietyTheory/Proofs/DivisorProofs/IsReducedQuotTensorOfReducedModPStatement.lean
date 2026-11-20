import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModP
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsReducedQuotTensorOfReducedModP.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p : ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 → IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) → IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  first | exact @GlobalTheory.reduced_quot_tensor_of_reduced_modp | exact GlobalTheory.reduced_quot_tensor_of_reduced_modp | (intros; apply GlobalTheory.reduced_quot_tensor_of_reduced_modp <;> assumption)
