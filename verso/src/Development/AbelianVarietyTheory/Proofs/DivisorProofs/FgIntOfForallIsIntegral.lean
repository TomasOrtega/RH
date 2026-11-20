import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Set `f : 𝓞 K' →ₗ[ℤ] K'` to `(algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap`. Establish `hle : M ≤ LinearMap.range f` using `fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩`. Establish `hfg : (M.comap f).FG` using `IsNoetherian.noetherian _`. Establish `hmap` using `hfg.map f`. Rewrite `hmap` using `[Submodule.map_comap_eq, inf_eq_right.mpr hle]`. Then use the resulting hypothesis.
-/
theorem fg_int_of_forall_isIntegral (K' : Type) [Field K'] [NumberField K']
    (M : Submodule ℤ K') (hM : ∀ y ∈ M, IsIntegral ℤ y) : M.FG := by
  let f : 𝓞 K' →ₗ[ℤ] K' := (algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap
  have hle : M ≤ LinearMap.range f := fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩
  have hfg : (M.comap f).FG := IsNoetherian.noetherian _
  have hmap := hfg.map f
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at hmap

/- English proof (translation)
Apply `Submodule.FG.of_restrictScalars ℤ` to reduce the goal to its premises. It suffices to establish `H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by`. Simplify using `using H ⊤`. Introduce `W`. Proceed by induction on `W using WellFoundedLT.induction with`.

Consider the case `_ W ih`. Distinguish the cases in `hW : W = ⊥`. Substitute `hW` using the available equality. Establish `hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Rewrite using `[hbot]`. Conclude with `Submodule.fg_bot`. Take `⟨x, hxW, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Take `⟨K', _, _, _, φ, hφx, hφL⟩` from `h x hx0`.

Set `f : C →ₗ[ℤ] K'` to `φ.toAddMonoidHom.toIntLinearMap`. Establish `hlt : W ⊓ LinearMap.ker φ < W`. Use `lt_of_le_of_ne inf_le_left fun heq => hφx ?_` and prove the remaining obligations. Establish `hx : x ∈ W ⊓ LinearMap.ker φ` using `by rw [heq]; exact hxW`. Conclude with `LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2`.

Apply `Submodule.fg_of_fg_map_of_fg_inf_ker f` to reduce the goal to its premises. Apply `fg_int_of_forall_isIntegral K'` to reduce the goal to its premises. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hz`. Conclude with `hφL y (Submodule.mem_inf.mp hy).1`.

Establish `heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ`. Use extensionality with `y`. Simplify using `[f, and_assoc]`. Conclude with `fun _ _ => Iff.rfl`. Rewrite using `[heq]`.

Conclude with `ih _ hlt`.
-/
theorem fg_of_integral_functionals (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  suffices H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by
    simpa using H ⊤
  intro W
  induction W using WellFoundedLT.induction with
  | _ W ih =>
    by_cases hW : W = ⊥
    · subst hW
      have hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥ := by
        ext y
        simp
      rw [hbot]
      exact Submodule.fg_bot
    · obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨K', _, _, _, φ, hφx, hφL⟩ := h x hx0
      let f : C →ₗ[ℤ] K' := φ.toAddMonoidHom.toIntLinearMap
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => hφx ?_
        have hx : x ∈ W ⊓ LinearMap.ker φ := by rw [heq]; exact hxW
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
      apply Submodule.fg_of_fg_map_of_fg_inf_ker f
      · apply fg_int_of_forall_isIntegral K'
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact hφL y (Submodule.mem_inf.mp hy).1
      · have heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f
            = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ := by
          ext y
          simp [f, and_assoc]
          exact fun _ _ => Iff.rfl
        rw [heq]
        exact ih _ hlt

end GlobalTheory
