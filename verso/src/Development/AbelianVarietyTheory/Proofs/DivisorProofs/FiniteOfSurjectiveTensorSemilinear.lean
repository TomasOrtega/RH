import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `Λ _ k _ π O _ M _ _ _ _ hM N _ _ f hf`. Take `⟨s, hs⟩` from `hM.fg_top`. Use `⟨⟨s.image f, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, eq_top_iff]`. Introduce and unpack `n -`.

Take `⟨m, rfl⟩` from `hf n`. Establish `hm : m ∈ Submodule.span Λ (s : Set M)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `h : a • x = (algebraMap Λ (Λ ⊗[ℤ] O) a) • x` using `(algebraMap_smul (Λ ⊗[ℤ] O) a x).symm`.

Rewrite using `[h, LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem finite_of_surjective_tensor_semilinear : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  intro Λ _ k _ π O _ M _ _ _ _ hM N _ _ f hf
  classical
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro n -
  obtain ⟨m, rfl⟩ := hf n
  have hm : m ∈ Submodule.span Λ (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : a • x = (algebraMap Λ (Λ ⊗[ℤ] O) a) • x := (algebraMap_smul (Λ ⊗[ℤ] O) a x).symm
    rw [h, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory
