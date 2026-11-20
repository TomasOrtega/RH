import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

namespace GlobalTheory.TraceOnInjectiveMap

/- English proof (translation)
Establish `hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Take `⟨y, hy, hyx⟩` from `h (j x) ⟨x, hx, rfl⟩`. Rewrite `hyx` using `[hL x hx]`.

Conclude with `hj hyx ▸ hy`. Introduce and unpack `h _ ⟨x, hx, rfl⟩`. Conclude with `⟨L' x, h x hx, (hL x hx).symm⟩`. Unfold `GlobalTheory.BCT.trOn`. Distinguish the cases in `h' : ∀ x ∈ M, L' x ∈ M`.

Rewrite using `[dif_pos (hpres.2 h'), dif_pos h']`. Set `e : M ≃ₗ[ℂ] Submodule.map j M` to `Submodule.equivMapOfInjective j hj M`. Establish `hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h')`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`.

Take `⟨x, rfl⟩` from `e.surjective w`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e, Submodule.coe_equivMapOfInjective_apply]`. Conclude with `hL x x.2`. Rewrite using `[hc, LinearMap.trace_conj']`.

Rewrite using `[dif_neg (mt hpres.1 h'), dif_neg h']`.
-/
theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dif_pos (hpres.2 h'), dif_pos h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dif_neg (mt hpres.1 h'), dif_neg h']

end GlobalTheory.TraceOnInjectiveMap
