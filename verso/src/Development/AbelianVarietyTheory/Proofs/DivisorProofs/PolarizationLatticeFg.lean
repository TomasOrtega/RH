import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ L ⟨N, hN, hL⟩ hu`. Establish `hLfg : L.FG`. Apply `Submodule.FG.of_restrictScalars ℤ` to reduce the goal to its premises. Set `f : E →ₗ[ℤ] E` to `LinearMap.mulLeft ℤ (N : E)`. Establish `hf : Function.Injective f` using `mul_right_injective₀ (Nat.cast_ne_zero.2 hN.ne')`.

Set `g : 𝓞 E →ₗ[ℤ] E` to `(Algebra.linearMap (𝓞 E) E).restrictScalars ℤ`. Establish `hg : (LinearMap.range g).FG`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map _`. Use `Submodule.fg_of_fg_map_injective f hf (hg.of_le ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨⟨(N : E) * x, hL x hx⟩, rfl⟩`. Establish `hMfg : (polMod L).FG` using `Submodule.fg_of_isUnit hu`. Establish `hP : (polMod L * L).FG` using `hMfg.mul hLfg`. Conclude with `(Submodule.fg_iff_addSubgroup_fg ((polMod L * L).restrictScalars ℤ)).1 (hP.restrictScalars)`.
-/
theorem polMod_mul_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  intro E _ _ _ L ⟨N, hN, hL⟩ hu
  have hLfg : L.FG := by
    apply Submodule.FG.of_restrictScalars ℤ
    let f : E →ₗ[ℤ] E := LinearMap.mulLeft ℤ (N : E)
    have hf : Function.Injective f := mul_right_injective₀ (Nat.cast_ne_zero.2 hN.ne')
    let g : 𝓞 E →ₗ[ℤ] E := (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
    have hg : (LinearMap.range g).FG := by
      rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
    refine Submodule.fg_of_fg_map_injective f hf (hg.of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(N : E) * x, hL x hx⟩, rfl⟩
  have hMfg : (polMod L).FG := Submodule.fg_of_isUnit hu
  have hP : (polMod L * L).FG := hMfg.mul hLfg
  exact (Submodule.fg_iff_addSubgroup_fg ((polMod L * L).restrictScalars ℤ)).1 (hP.restrictScalars)

end GlobalTheory
