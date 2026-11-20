import Mathlib

namespace GlobalTheory.CompanionTheory.PiTensor

/- English proof (translation)
Establish `hg : ∀ i, ∃ g : N i →ₗ[K] M i, g ∘ₗ f i = LinearMap.id` using `fun i => LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.2 (hf i))`. Use `choose g hg using hg`. Establish `hcomp : PiTensorProduct.map g ∘ₗ PiTensorProduct.map f = LinearMap.id`. Rewrite using `[← PiTensorProduct.map_comp]`. Simplify using `only [hg]`.

Conclude with `PiTensorProduct.map_id`. Use `Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun hcomp x`.
-/
theorem map_injective_of_injective
    (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (f : ∀ i, M i →ₗ[K] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  have hg : ∀ i, ∃ g : N i →ₗ[K] M i, g ∘ₗ f i = LinearMap.id := fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.2 (hf i))
  choose g hg using hg
  have hcomp : PiTensorProduct.map g ∘ₗ PiTensorProduct.map f = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  exact LinearMap.congr_fun hcomp x

end GlobalTheory.CompanionTheory.PiTensor
