import Mathlib
open Filter Topology

namespace GlobalTheory.Mean4Cauchy

/- English proof (translation)
Introduce `F C R₀ d h`. Establish `h0 : Tendsto (fun R : ℝ => Real.log R ^ d / Real.sqrt R) atTop (𝓝 0)`. Establish `h1` using `(isLittleO_log_rpow_rpow_atTop (d : ℝ) (s := 1 / 2) (by norm_num)).tendsto_div_nhds_zero`. Use `h1.congr (fun x => ?_)` and prove the remaining obligations. Rewrite using `[Real.rpow_natCast, Real.sqrt_eq_rpow]`.

Establish `h2 : Tendsto (fun R : ℝ => C * Real.log R ^ d / Real.sqrt R) atTop (𝓝 0)`. Use `h0.const_mul C` as an intermediate fact. Simplify `this` using `[mul_div_assoc]`. Apply `cauchy_map_iff_exists_tendsto.mp` to reduce the goal to its premises. Rewrite using `[Metric.cauchy_iff]`.

Use `⟨inferInstance, fun ε hε => ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ᶠ R in atTop, C * Real.log R ^ d / Real.sqrt R < ε / 2` using `h2.eventually (gt_mem_nhds (by linarith))`. Take `⟨R, hR1, hR2⟩` from `(h3.and (eventually_ge_atTop R₀)).exists`. Use `⟨F '' Set.Ici R, image_mem_map (Ici_mem_atTop R), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩`.

Establish `a` using `h R x hR2 hx`. Establish `b` using `h R y hR2 hy`. Rewrite using `[Real.dist_eq]`. Use `abs_sub_le (F x) (F R) (F y)` as an intermediate fact. Rewrite `this` using `[abs_sub_comm (F x) (F R)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_tendsto_of_log_pow_div_sqrt :
    ∀ (F : ℝ → ℝ) (C R₀ : ℝ) (d : ℕ),
      (∀ R R' : ℝ, R₀ ≤ R → R ≤ R' → |F R - F R'| ≤ C * Real.log R ^ d / Real.sqrt R) →
      ∃ L, Tendsto F atTop (𝓝 L) := by
  intro F C R₀ d h
  have h0 : Tendsto (fun R : ℝ => Real.log R ^ d / Real.sqrt R) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_rpow_atTop (d : ℝ) (s := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
    refine h1.congr (fun x => ?_)
    rw [Real.rpow_natCast, Real.sqrt_eq_rpow]
  have h2 : Tendsto (fun R : ℝ => C * Real.log R ^ d / Real.sqrt R) atTop (𝓝 0) := by
    have := h0.const_mul C
    simpa [mul_div_assoc] using this
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  have h3 : ∀ᶠ R in atTop, C * Real.log R ^ d / Real.sqrt R < ε / 2 :=
    h2.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R, hR1, hR2⟩ := (h3.and (eventually_ge_atTop R₀)).exists
  refine ⟨F '' Set.Ici R, image_mem_map (Ici_mem_atTop R), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have a := h R x hR2 hx
  have b := h R y hR2 hy
  rw [Real.dist_eq]
  have := abs_sub_le (F x) (F R) (F y)
  rw [abs_sub_comm (F x) (F R)] at this
  linarith

end GlobalTheory.Mean4Cauchy
