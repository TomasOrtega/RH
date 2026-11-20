import Mathlib

open Module

namespace GlobalTheory

/- English proof (translation)
Set `E : Xt → Dual ℂ S` to `fun x => (LinearMap.proj x : (Xt → ℂ) →ₗ[ℂ] ℂ).comp S.subtype`. Establish `hE : ∀ x (f : S), E x f = (f : Xt → ℂ) x` using `fun _ _ => rfl`. Use `set W : Submodule ℂ (Dual ℂ S) := Submodule.span ℂ (Set.range E) with hWdef`. Establish `hco : W.dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `f hf`. Rewrite `hf` using `[Submodule.mem_dualCoannihilator]`. Rewrite using `[Submodule.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `hf (E x) (Submodule.subset_span ⟨x, rfl⟩)` as an intermediate fact. Simplify `this` using `[hE]`. Establish `hW : W = ⊤`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hco]`. Conclude with `Submodule.dualAnnihilator_bot`.

Establish `hl : l ∈ W` using `by rw [hW]; trivial`. Take `⟨n, c, g, hg⟩` from `Submodule.mem_span_set'.mp hl`. Use `choose x hx using fun i => (g i).2`. Use `⟨n, x, c, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hx i, hE]`.
-/
theorem exists_eval_combination (Xt : Type) (S : Submodule ℂ (Xt → ℂ)) [FiniteDimensional ℂ S]
    (l : S →ₗ[ℂ] ℂ) :
    ∃ (n : ℕ) (x : Fin n → Xt) (c : Fin n → ℂ), ∀ f : S, l f = ∑ i, c i * (f : Xt → ℂ) (x i) := by
  let E : Xt → Dual ℂ S := fun x => (LinearMap.proj x : (Xt → ℂ) →ₗ[ℂ] ℂ).comp S.subtype
  have hE : ∀ x (f : S), E x f = (f : Xt → ℂ) x := fun _ _ => rfl
  set W : Submodule ℂ (Dual ℂ S) := Submodule.span ℂ (Set.range E) with hWdef
  have hco : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_dualCoannihilator] at hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hf (E x) (Submodule.subset_span ⟨x, rfl⟩)
    simpa [hE] using this
  have hW : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hco]
    exact Submodule.dualAnnihilator_bot
  have hl : l ∈ W := by rw [hW]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hl
  choose x hx using fun i => (g i).2
  refine ⟨n, x, c, fun f => ?_⟩
  rw [← hg]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, hE]

end GlobalTheory
