import Mathlib

/- English proof (translation)
Introduce `Γ A _ _ _ _ ψ h`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ), h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x⁻¹ * x ∈ ψ.ker`.

Simplify using the standard rewrite rules. Introduce `y hy`. Establish `hy' : ψ (x⁻¹ * y) = 1` using `MonoidHom.mem_ker.mp hy`. Rewrite `hy'` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `hy'.symm`.
-/
theorem UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
