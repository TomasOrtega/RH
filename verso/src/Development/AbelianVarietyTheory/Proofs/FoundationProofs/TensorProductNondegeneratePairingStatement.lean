import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorProductNondegeneratePairing
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTensorProductNondegeneratePairing.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.tensor_product_nondegenerate_pairing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type) [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)] [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ), (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) → ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)), (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧ ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  first | exact @GlobalTheory.tensor_pairing_separating | exact GlobalTheory.tensor_pairing_separating | (intros; apply GlobalTheory.tensor_pairing_separating <;> assumption)
