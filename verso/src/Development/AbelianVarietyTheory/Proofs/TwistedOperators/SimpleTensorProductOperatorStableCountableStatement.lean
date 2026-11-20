import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TensHead.simple_tensor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSimpleTensorProductOperatorStableCountable.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.simple_tensor_product_operatorStable_countable : ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.simple_tensor | exact GlobalTheory.TensHead.simple_tensor | (intros; apply GlobalTheory.TensHead.simple_tensor <;> assumption)
