import Mathlib

/- English proof (translation)
Introduce `G M _ _ _ _ χ h`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G), h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Simplify using `[MonoidHom.mem_ker]`.

Introduce `y hy`. Establish `hy' : χ (x⁻¹ * y) = 1` using `MonoidHom.mem_ker.mp hy`. Rewrite `hy'` using `[map_mul, map_inv]`. Conclude with `(inv_mul_eq_one.mp hy').symm`.
-/
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) := by
  intro G M _ _ _ _ χ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : χ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
