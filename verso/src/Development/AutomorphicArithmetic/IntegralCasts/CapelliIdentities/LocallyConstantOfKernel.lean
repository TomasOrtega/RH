import Mathlib

/- English proof (translation)
Introduce `Γ C _ _ _ _ η h`. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ), h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x⁻¹ * x ∈ η.ker`. Simplify using `[MonoidHom.mem_ker]`.

Introduce `y hy`. Establish `hy' : η (x⁻¹ * y) = 1` using `hy`. Rewrite `hy'` using `[map_mul, map_inv]`. Conclude with `(inv_mul_eq_one.mp hy').symm`.
-/
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) := by
  intro Γ C _ _ _ _ η h
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ η.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : η (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
