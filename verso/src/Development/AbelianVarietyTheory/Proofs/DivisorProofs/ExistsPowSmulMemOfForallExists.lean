import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `S _ I M _ _ _ N h`. Use `choose f hf using h`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := S) (M := M)`. Use `⟨s.sup f, fun a ha y => ?_⟩` and prove the remaining obligations. Establish `key : _root_.Submodule.span S (s : Set M) ≤ N.comap (a • LinearMap.id)`.

Rewrite using `[_root_.Submodule.span_le]`. Introduce `x hx`. Use `show (a • LinearMap.id : M →ₗ[S] M) x ∈ N`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `hf x a (Ideal.pow_le_pow_right (Finset.le_sup (f := f) hx) ha)`.

Establish `hy : y ∈ _root_.Submodule.span S (s : Set M)` using `by rw [hs]; trivial`. Use `key hy` as an intermediate fact. Rewrite `this` using `[_root_.Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Then use the resulting hypothesis.
-/
theorem Submodule.exists_pow_smul_mem_of_forall_exists :
    ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M]
      [Module.Finite S M] (N : Submodule S M),
      (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  intro S _ I M _ _ _ N h
  choose f hf using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨s.sup f, fun a ha y => ?_⟩
  have key : _root_.Submodule.span S (s : Set M) ≤ N.comap (a • LinearMap.id) := by
    rw [_root_.Submodule.span_le]
    intro x hx
    show (a • LinearMap.id : M →ₗ[S] M) x ∈ N
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hf x a (Ideal.pow_le_pow_right (Finset.le_sup (f := f) hx) ha)
  have hy : y ∈ _root_.Submodule.span S (s : Set M) := by rw [hs]; trivial
  have := key hy
  rwa [_root_.Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at this

end GlobalTheory
