import Mathlib

/- English proof (translation)
Introduce `G H _ _ _ _ f hk`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hc : Continuous fun y : G => x⁻¹ * y` using `continuous_const.mul continuous_id`. Establish `ho : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G))` using `hk.preimage hc`.

Establish `hx : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G)`. Simplify using `[Set.mem_preimage, MonoidHom.mem_ker]`. Use `filter_upwards [ho.mem_nhds hx] with y hy`. Establish `h1 : f (x⁻¹ * y) = 1` using `MonoidHom.mem_ker.mp hy`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`.

Conclude with `h1.symm`.
-/
theorem UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open :
    ∀ {G H : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : Group H] (f : G →* H), IsOpen (↑f.ker : Set G) → IsLocallyConstant (⇑f : G → H) := by
  intro G H _ _ _ _ f hk
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : G => x⁻¹ * y := continuous_const.mul continuous_id
  have ho : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G)) := hk.preimage hc
  have hx : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G) := by
    simp [Set.mem_preimage, MonoidHom.mem_ker]
  filter_upwards [ho.mem_nhds hx] with y hy
  have h1 : f (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm
