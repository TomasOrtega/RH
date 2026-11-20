import ReciprocityTheory.SemistableReduction.SJCoreD

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real

/- English proof (translation)
Establish `hdim : Module.finrank ℝ ℂ = 2` using `Complex.finrank_real_complex`. Establish `h1` using `integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))`. Establish `h2` using `integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))`. Rewrite `h1`, `h2` using `[hdim]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2`.

Use `set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef`. Establish `hC : 0 < C` using `ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne`. Establish `hG : gaussOneC = 2 * C * radJ 1`. Unfold `gaussOneC radJ`. Rewrite using `[h1]`.

Simplify using `only [pow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) = log a * radJ 1 + radK 1`. Establish `heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2))) (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0)`. Introduce `y hy`.

Simplify using `only`. Rewrite using `[log_mul ha.ne' (ne_of_gt hy)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[setIntegral_congr_fun measurableSet_Ioi heq, integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl), integral_const_mul]`. Both sides reduce to the same expression.

Establish `hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1)`. Unfold `gaussLogC`. Rewrite using `[h2, hsplit]`. Expand and normalize the polynomial expressions, which then agree. Establish `hM` using `radJ_pos 1`.

Rewrite using `[hL, hG]`. Clear the denominators using the available nonvanishing facts.
-/
theorem gaussLogC_div {a : ℝ} (ha : 0 < a) :
    gaussLogC a / gaussOneC = log a + radK 1 / radJ 1 := by
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))
  rw [hdim] at h1 h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2
  set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef
  have hC : 0 < C :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne
  have hG : gaussOneC = 2 * C * radJ 1 := by
    unfold gaussOneC radJ
    rw [h1]
    simp only [pow_one]
    ring
  have hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) =
      log a * radJ 1 + radK 1 := by
    have heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2)))
        (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0) := by
      intro y hy
      simp only
      rw [log_mul ha.ne' (ne_of_gt hy)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl),
      integral_const_mul]
    rfl
  have hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1) := by
    unfold gaussLogC
    rw [h2, hsplit]
    ring
  have hM := radJ_pos 1
  rw [hL, hG]
  field_simp

/- English proof (translation)
Introduce `n c hc`. Establish `hn : 0 < n`. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Conclude with `absurd (Subsingleton.elim c 0) hc`. Conclude with `h`.

Take `⟨hi, he⟩` from `polar_mean hn c hc`. Use `⟨hi, ?_⟩` and prove the remaining obligations. Establish `hcn : 0 < ‖c‖` using `norm_pos_iff.mpr hc`. Establish `h2 : 2 * n - 1 = 2 * (n - 1) + 1` using `by omega`. Rewrite using `[he, gaussLogC_div hcn, h2, radRatio_odd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sjCore_holds : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring

end ReciprocityTheory.MultiplicativeHeights
