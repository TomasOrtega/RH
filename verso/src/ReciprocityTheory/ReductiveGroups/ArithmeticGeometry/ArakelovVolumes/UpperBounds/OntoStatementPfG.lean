import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

/- English proof (translation)
Establish `h : 0 ≤ (x - k * y) ^ 2 / k` using `by positivity`. Establish `e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith

/- English proof (translation)
Establish `hWm : AEMeasurable (fun a => (w a).toReal) μ` using `hwm.ennreal_toReal`. Establish `hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ` using `(hkm.mul (hgm.norm.pow_const 2)).mul hWm`. Establish `hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ` using `((hum.norm.pow_const 2).div hkm).mul hWm`. Establish `hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal` using `by filter_upwards [hk] with a ha`. Conclude with `mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg`.

Establish `hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal` using `by filter_upwards [hk] with a ha`. Conclude with `mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg`. Establish `hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hk, hw] with a ha hwa`.

Rewrite using `[ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]`. Establish `hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ = ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hk, hw] with a ha hwa`. Rewrite using `[ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]`.

Rewrite `hI`, `hJ`, the goal using `[hA]`. Rewrite `hJ` using `[hB]`. Establish `hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤` using `lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)`. Establish `hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ` using `⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩`. Establish `hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ` using `⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩`.

Establish `hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal` using `integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable`. Establish `hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ = (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal` using `integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable`. Establish `hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ` using `((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable`. Establish `hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤ (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2` using `by filter_upwards [hk] with a ha`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]`.

Establish `h1` using `amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha`. Establish `hW0 : 0 ≤ (w a).toReal` using `ENNReal.toReal_nonneg`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 hW0]`. Establish `hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ` using `(hF2i.add hF1i).div_const 2`. Establish `hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ` using `Integrable.mono' hbdi hPm hPbd`.

Establish `hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ` using `hF1i.ofReal`. Establish `hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) = fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ)`. Use function extensionality and compare the values at `a`. Rewrite using `[sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero]`. Establish `hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ` using `integral_nonneg_of_ae hF1nn`. Establish `hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤ ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hn]`. Use `_ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]`. Use `_ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _`. Use `_ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ := integral_mono_ae hPi.norm hbdi hPbd`. Use `_ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by`.

Rewrite using `[integral_div, integral_add hF2i hF1i]`. Establish `hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ`. Rewrite using `[hint1, hint2]`. Use `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0]`. Then use the resulting hypothesis.

Establish `hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hq1.le) hn]`. Rewrite `hz` using `[hint1]`. Conclude with `((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne`.
-/
theorem I_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
