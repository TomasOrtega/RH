import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TensorDecomp.tensor_decomp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsTensorDecompositionCommutingFamilies.lean&line=233#L233)
-/
theorem _root_.GlobalTheory.T.exists_tensorDecomposition_commutingFamilies : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  first | exact @GlobalTheory.TensorDecomp.tensor_decomp | exact GlobalTheory.TensorDecomp.tensor_decomp | (intros; apply GlobalTheory.TensorDecomp.tensor_decomp <;> assumption)
