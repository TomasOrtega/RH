import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.TorusMeanD

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

/- English proof (translation)
Use `⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩, fun ι _ f i k hk hext => ?_⟩` and prove the remaining obligations. Use `show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) = ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)`. Rewrite using `[← integral_add (tm_int f) (tm_int g)]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2`.

Simplify using `only [tmLog, map_mul, norm_mul]`. Conclude with `Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)`. Establish `hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖`. Introduce `θ`. Simplify using `[tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow, norm_torusPoint]`.

Use `show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖`. Repeatedly rewrite using `[hm]`. Simplify using the standard rewrite rules. Use `show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)`. Establish `hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure)` using `(tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)`.

Rewrite using `[tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable, integral_prod (fun p => tmLog f (tmUpd i p)) hFi]`. Use `integral_mono_ae (tm_int _) hFi.integral_prod_left ?_` and prove the remaining obligations. Use `filter_upwards [tm_ae_ne _ hk] with θ hθ`. Use `show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure`. Repeatedly rewrite using `[tmLog_update]`.

Rewrite using `[integral_log_circ]`. Establish `hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f)` using `tmSlice_coeff i _ f k`. Establish `hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0` using `hc ▸ hθ`. Use `show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _`. Rewrite using `[← hc]`.

Break down `hext with htop | hbot` into its components or cases. Conclude with `log_norm_coeff_top_le _ k hk' fun k' hk'' => by`. Rewrite using `[tmSlice_coeff, htop k' hk'', map_zero]`. Conclude with `log_norm_coeff_bot_le _ k hk' fun k' hk'' => by`. Rewrite using `[tmSlice_coeff, hbot k' hk'', map_zero]`.
-/
theorem torusMean_holds : TorusMeanBasicStatement ∧ TorusCoeffStatement := by
  classical
  refine ⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩,
    fun ι _ f i k hk hext => ?_⟩
  · show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) =
      ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)
    rw [← integral_add (tm_int f) (tm_int g)]
    apply integral_congr_ae
    filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2
    simp only [tmLog, map_mul, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)
  · have hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖ := by
      intro θ
      simp [tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow,
        norm_torusPoint]
    show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖
    simp_rw [hm]
    simp
  · show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)
    have hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      (tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)
    rw [tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable,
      integral_prod (fun p => tmLog f (tmUpd i p)) hFi]
    refine integral_mono_ae (tm_int _) hFi.integral_prod_left ?_
    filter_upwards [tm_ae_ne _ hk] with θ hθ
    show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure
    simp_rw [tmLog_update]
    rw [integral_log_circ]
    have hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f) :=
      tmSlice_coeff i _ f k
    have hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0 := hc ▸ hθ
    show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _
    rw [← hc]
    rcases hext with htop | hbot
    · exact log_norm_coeff_top_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, htop k' hk'', map_zero]
    · exact log_norm_coeff_bot_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, hbot k' hk'', map_zero]

end ReciprocityTheory.MultiplicativeHeights
