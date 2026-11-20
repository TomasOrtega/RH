import Mathlib

namespace GlobalTheory

open Module

/- English proof (translation)
Take `⟨v, hv, hfv⟩` from `h`. Establish `hrange : LinearMap.range (f.domRestrict V) = ⊤`. Apply `LinearMap.range_eq_top.mpr` to reduce the goal to its premises. Introduce `c`. Use `⟨(c / f v) • ⟨v, hv⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[LinearMap.domRestrict_apply, div_mul_cancel₀ _ hfv]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (f.domRestrict V)`. Rewrite `h1` using `[hrange, finrank_top, Module.finrank_self]`. Establish `hker : LinearMap.ker (f.domRestrict V) = Submodule.comap V.subtype (LinearMap.ker f)`. Use extensionality with `x`.

Simplify using `[LinearMap.domRestrict_apply]`. Establish `h2 : Module.finrank K (LinearMap.ker (f.domRestrict V)) = Module.finrank K (V ⊓ LinearMap.ker f : Submodule K (Fin r → K))`. Rewrite using `[← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq, hker]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_inf_ker_add_one_of_ne_zero (K : Type) [Field K] (r : ℕ)
    (V : Submodule K (Fin r → K)) (f : (Fin r → K) →ₗ[K] K) (h : ∃ v ∈ V, f v ≠ 0) :
    Module.finrank K (V ⊓ LinearMap.ker f : Submodule K (Fin r → K)) + 1 =
      Module.finrank K V := by
  obtain ⟨v, hv, hfv⟩ := h
  have hrange : LinearMap.range (f.domRestrict V) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    refine ⟨(c / f v) • ⟨v, hv⟩, ?_⟩
    simp [LinearMap.domRestrict_apply, div_mul_cancel₀ _ hfv]
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict V)
  rw [hrange, finrank_top, Module.finrank_self] at h1
  have hker : LinearMap.ker (f.domRestrict V) = Submodule.comap V.subtype (LinearMap.ker f) := by
    ext x; simp [LinearMap.domRestrict_apply]
  have h2 : Module.finrank K (LinearMap.ker (f.domRestrict V)) =
      Module.finrank K (V ⊓ LinearMap.ker f : Submodule K (Fin r → K)) := by
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq, hker]
  omega

end GlobalTheory
