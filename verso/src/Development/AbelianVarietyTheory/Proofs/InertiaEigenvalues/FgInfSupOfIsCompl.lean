import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `hA h`. Set `p : V →ₗ[K] V` to `U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h`. Set `q : V →ₗ[𝓞 K] V` to `p.restrictScalars (𝓞 K)`. Establish `hpU : ∀ x, p x ∈ U` using `fun x => (Submodule.linearProjOfIsCompl U U' h x).2`. Establish `hpl : ∀ x ∈ U, p x = x` using `fun x hx => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)`.

Establish `hpr : ∀ x ∈ U', p x = 0` using `fun x hx => by`. Use `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx` as an intermediate fact. Use `show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0`. Conclude with `congrArg Subtype.val this`. Establish `hsub : ∀ x, x - p x ∈ U'` using `fun x => by`.

Rewrite using `[← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]`. Establish `h1 : p (x - p x) = 0` using `by rw [map_sub, hpl _ (hpU x), sub_self]`. Establish `h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0` using `h1`. Conclude with `h2` after adjusting the coercions. Establish `heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxU, hx⟩`. Take `⟨a, ha, u, hu, rfl⟩` from `Submodule.mem_sup.1 hx`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `p a = a + u`. Establish `e1 : p (a + u) = a + u` using `hpl _ hxU`. Rewrite `e1` using `[map_add, hpr u hu, add_zero]`. Conclude with `e1`. Introduce and unpack `⟨a, ha, rfl⟩`.

Use `⟨hpU a, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩` and prove the remaining obligations. Use `U'.neg_mem (hsub a)` as an intermediate fact. Simplify using `using this`. Rewrite using `[heq]`.

Conclude with `hA.map q`.
-/
theorem fg_inf_sup_of_isCompl (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V) :
    A.FG → IsCompl U U' →
      (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  intro hA h
  let p : V →ₗ[K] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h
  let q : V →ₗ[𝓞 K] V := p.restrictScalars (𝓞 K)
  have hpU : ∀ x, p x ∈ U := fun x => (Submodule.linearProjOfIsCompl U U' h x).2
  have hpl : ∀ x ∈ U, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)
  have hpr : ∀ x ∈ U', p x = 0 := fun x hx => by
    have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
    show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0
    exact congrArg Subtype.val this
  have hsub : ∀ x, x - p x ∈ U' := fun x => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]
    have h1 : p (x - p x) = 0 := by rw [map_sub, hpl _ (hpU x), sub_self]
    have h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0 := h1
    exact_mod_cast h2
  have heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨a, ha, ?_⟩
      change p a = a + u
      have e1 : p (a + u) = a + u := hpl _ hxU
      rw [map_add, hpr u hu, add_zero] at e1
      exact e1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpU a, ?_⟩
      refine Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩
      have := U'.neg_mem (hsub a)
      simpa using this
  rw [heq]
  exact hA.map q

end GlobalTheory
