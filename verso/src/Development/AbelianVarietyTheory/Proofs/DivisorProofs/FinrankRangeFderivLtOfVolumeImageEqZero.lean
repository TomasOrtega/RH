import Mathlib
open Set Filter Topology MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `n h W hW ha h0 y hy`. Assume the negation of the conclusion as `hlt`. Establish `hn : Module.finrank ℂ (Fin n → ℂ) = n` using `by simp`. Establish `hle` using `Submodule.finrank_le (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))`. Establish `htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤` using `Submodule.eq_top_of_finrank_eq (by omega)`.

Establish `hs : HasStrictFDerivAt h (fderiv ℂ h y) y` using `(ha y hy).hasStrictFDerivAt`. Establish `hmap` using `hs.map_nhds_eq_of_surj htop`. Establish `hmem : h '' W ∈ 𝓝 (h y)`. Rewrite using `[← hmap]`. Conclude with `image_mem_map (hW.mem_nhds hy)`.

Conclude with `(Measure.measure_pos_of_mem_nhds volume hmem).ne' h0`.
-/
theorem finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0

end GlobalTheory
