import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorLeftFactor
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzTensorLeftFactor.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.schwartz_tensor_left_factor : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ κ' : Type) [Fintype κ] [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ), ∃ T : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ f x, T f x = f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr) := by
  first | exact @GlobalTheory.SchwartzBox.exists_boxCLM | exact GlobalTheory.SchwartzBox.exists_boxCLM | (intros; apply GlobalTheory.SchwartzBox.exists_boxCLM <;> assumption)
