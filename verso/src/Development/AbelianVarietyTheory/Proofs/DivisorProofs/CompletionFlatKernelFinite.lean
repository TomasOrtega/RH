import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ f M _ _ hflat hproj n π hπ`. Use `set B := AdicCompletion (Ideal.span {f}) A`. Set `φ : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] M` to `AlgebraTensorModule.lTensor B B π`. Set `ψ : B ⊗[A] (LinearMap.ker π) →ₗ[B] B ⊗[A] (Fin n → A)` to `AlgebraTensorModule.lTensor B B (LinearMap.ker π).subtype`. Establish `hexact : Function.Exact (LinearMap.ker π).subtype π`.

Introduce `x`. Simplify using the standard rewrite rules. Establish `hψinj : Function.Injective ψ` using `LinearMap.lTensor_injective_of_exact_of_flat π hπ _ (LinearMap.ker π).injective_subtype hexact B`. Establish `hψex : Function.Exact ψ φ` using `lTensor_exact B hexact hπ`. Establish `hφsurj : Function.Surjective φ` using `LinearMap.lTensor_surjective B hπ`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property φ LinearMap.id hφsurj`. Set `p : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] (Fin n → A)` to `LinearMap.id - s ∘ₗ φ`. Establish `hp : ∀ x, p x ∈ LinearMap.ker φ`. Introduce `x`. Use `LinearMap.congr_fun hs (φ x)` as an intermediate fact.

Simplify using `only [LinearMap.mem_ker, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite using `[this, sub_self]`. Establish `hker : Module.Finite B (LinearMap.ker φ)`. Use `Module.Finite.of_surjective (p.codRestrict (LinearMap.ker φ) hp) ?_` and prove the remaining obligations.

Introduce and unpack `⟨y, hy⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [LinearMap.codRestrict_apply, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]`. Rewrite using `[LinearMap.mem_ker.mp hy, map_zero, sub_zero]`.

Establish `hrange : LinearMap.range ψ = LinearMap.ker φ`. Use extensionality with `y`. Rewrite using `[LinearMap.mem_range, LinearMap.mem_ker]`. Conclude with `(hψex y).symm`. Set `e : B ⊗[A] (LinearMap.ker π) ≃ₗ[B] LinearMap.ker φ` to `(LinearEquiv.ofInjective ψ hψinj).trans (LinearEquiv.ofEq _ _ hrange)`.

Conclude with `Module.Finite.equiv e.symm`.
-/
theorem adicCompletion_tensor_ker_finite : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat A M →
  Module.Projective (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  ∀ (n : ℕ) (π : (Fin n → A) →ₗ[A] M), Function.Surjective π →
  Module.Finite (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) (LinearMap.ker π)) := by
  intro A _ f M _ _ hflat hproj n π hπ
  set B := AdicCompletion (Ideal.span {f}) A
  let φ : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] M := AlgebraTensorModule.lTensor B B π
  let ψ : B ⊗[A] (LinearMap.ker π) →ₗ[B] B ⊗[A] (Fin n → A) :=
    AlgebraTensorModule.lTensor B B (LinearMap.ker π).subtype
  have hexact : Function.Exact (LinearMap.ker π).subtype π := by
    intro x; simp
  have hψinj : Function.Injective ψ :=
    LinearMap.lTensor_injective_of_exact_of_flat π hπ _ (LinearMap.ker π).injective_subtype hexact B
  have hψex : Function.Exact ψ φ := lTensor_exact B hexact hπ
  have hφsurj : Function.Surjective φ := LinearMap.lTensor_surjective B hπ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφsurj
  let p : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] (Fin n → A) := LinearMap.id - s ∘ₗ φ
  have hp : ∀ x, p x ∈ LinearMap.ker φ := by
    intro x
    have := LinearMap.congr_fun hs (φ x)
    simp only [LinearMap.mem_ker, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  have hker : Module.Finite B (LinearMap.ker φ) := by
    refine Module.Finite.of_surjective (p.codRestrict (LinearMap.ker φ) hp) ?_
    rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    ext
    simp only [LinearMap.codRestrict_apply, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [LinearMap.mem_ker.mp hy, map_zero, sub_zero]
  have hrange : LinearMap.range ψ = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hψex y).symm
  let e : B ⊗[A] (LinearMap.ker π) ≃ₗ[B] LinearMap.ker φ :=
    (LinearEquiv.ofInjective ψ hψinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact Module.Finite.equiv e.symm

end GlobalTheory
