import Mathlib

namespace GlobalTheory.IntegralPointNormSquareBound

/- English proof (translation)
Establish `hcont : Continuous fun v : V => om v (J v)`. Set `B : V →ₗ[ℝ] V →L[ℝ] ℝ` to `(LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om`. Establish `h1 : Continuous B` using `B.continuous_of_finiteDimensional`. Establish `h2 : Continuous J` using `J.continuous_of_finiteDimensional`. Conclude with `h1.clm_apply h2`.

Establish `hcomp : IsCompact (Metric.sphere (0 : V) 1)` using `by haveI : ProperSpace V := FiniteDimensional.proper_real V`. Conclude with `isCompact_sphere 0 1`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by`. Break down `(Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne` into its components or cases. Conclude with `⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩`.

Take `⟨x, hx, hmin⟩` from `hcomp.exists_isMinOn hne hcont.continuousOn`. Use `⟨om x (J x), h x ?_, fun u hu => hmin hu⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hx`. Use `⟨c, hc, fun v => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.mpr hv`. Establish `hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1`.

Simplify using `[norm_smul, hn.ne']`. Establish `h3` using `hle _ hu`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3`. Establish `h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v)`. Clear the denominators using the available nonvanishing facts.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pos_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  have hcont : Continuous fun v : V => om v (J v) := by
    let B : V →ₗ[ℝ] V →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om
    have h1 : Continuous B := B.continuous_of_finiteDimensional
    have h2 : Continuous J := J.continuous_of_finiteDimensional
    exact h1.clm_apply h2
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := by
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    exact isCompact_sphere 0 1
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      refine ⟨om x (J x), h x ?_, fun u hu => hmin hu⟩
      rintro rfl
      simp at hx
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hn.ne']
    have h3 := hle _ hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v) := by
      field_simp
    calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = om v (J v) := h4

end GlobalTheory.IntegralPointNormSquareBound
