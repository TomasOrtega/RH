import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTensorProductDeterminesFactorClasses.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.tensor_product_determines_factor_classes : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  first | exact @GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | exact GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | (intros; apply GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv <;> assumption)
