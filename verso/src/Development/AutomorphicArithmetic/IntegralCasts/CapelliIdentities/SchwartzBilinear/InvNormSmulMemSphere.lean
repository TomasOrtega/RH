import Mathlib

namespace UpperTheory.Reformulated.B.P6.r24a

/- English proof (translation)
Simplify using `only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hn : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`.
-/
theorem inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

/- English proof (translation)
Introduce `V _ _ _ Q hQ`. Establish `hcont : Continuous fun x : V => (Q x x).re` using `Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)`. Distinguish the cases in `hne : (Metric.sphere (0 : V) 1).Nonempty`. Take `⟨x0, hx0, hmin⟩` from `(isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn`. Establish `hx0ne : x0 ≠ 0`.

Introduce `h`. Rewrite `hx0` using `[h, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hx0`. Use `⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Take `⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x` from `⟨_, rfl⟩`. Establish `hy : y ∈ Metric.sphere (0 : V) 1` using `hyd ▸ inv_norm_smul_mem_sphere x hx`.

Establish `h1 : (Q x0 x0).re ≤ (Q y y).re` using `hmin hy`. Establish `h2 : ‖x‖ • y = x`. Rewrite using `[hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`. Establish `h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re`. Use `quadratic_form_smul_re Q ‖x‖ y` as an intermediate fact.

Rewrite `this` using `[h2]`. Conclude with `this`. Rewrite using `[h3, mul_comm (‖x‖ ^ 2)]`. Conclude with `mul_le_mul_of_nonneg_right h1 (by positivity)`. Use `⟨1, one_pos, fun x => ?_⟩` and prove the remaining obligations.

Establish `hx : x = 0`. Assume the negation of the conclusion as `hx`. Conclude with `hne ⟨_, inv_norm_smul_mem_sphere x hx⟩`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.
-/
theorem PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos :
    ∀ {V : Type} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ), (∀ (x : V), x ≠ OfNat.ofNat (nat_lit 0) → OfNat.ofNat (nat_lit 0) < (DFunLike.coe (DFunLike.coe Q x) x).re) → ∃ (κ : ℝ), OfNat.ofNat (nat_lit 0) < κ ∧ ∀ (x : V), κ * ‖x‖ ^ OfNat.ofNat (nat_lit 2) ≤ (DFunLike.coe (DFunLike.coe Q x) x).re := by
  intro V _ _ _ Q hQ
  have hcont : Continuous fun x : V => (Q x x).re :=
    Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x := ⟨_, rfl⟩
      have hy : y ∈ Metric.sphere (0 : V) 1 := hyd ▸ inv_norm_smul_mem_sphere x hx
      have h1 : (Q x0 x0).re ≤ (Q y y).re := hmin hy
      have h2 : ‖x‖ • y = x := by
        rw [hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re := by
        have := quadratic_form_smul_re Q ‖x‖ y
        rw [h2] at this
        exact this
      rw [h3, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨_, inv_norm_smul_mem_sphere x hx⟩
    subst hx
    simp

end UpperTheory.Reformulated.B.P6.r24a
