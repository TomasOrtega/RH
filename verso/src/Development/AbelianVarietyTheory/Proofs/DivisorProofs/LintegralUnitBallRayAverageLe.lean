import Mathlib
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Use `set f : E → ℝ≥0∞ := fun y => if ‖y‖ ≤ t then ENNReal.ofReal (t ^ m * (‖y‖ / t) ^ (m + 1)) * Ψ y else 0 with hfdef`. Establish `hf : Measurable f`. Use `Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const` and prove the remaining obligations. Conclude with `(ENNReal.measurable_ofReal.comp (by fun_prop)).mul hΨ`. Establish `h1 : ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ = ∫⁻ v, f (t • v) ∂μ`.

Rewrite using `[← lintegral_indicator measurableSet_closedBall]`. Use `congr 1`. Use extensionality with `v`. Establish `hiff : t * ‖v‖ ≤ t ↔ ‖v‖ ≤ 1` using `mul_le_iff_le_one_right ht`. Establish `hdiv : t * ‖v‖ / t = ‖v‖` using `by field_simp`.

Simplify using `only [indicator, Metric.mem_closedBall, dist_zero_right, hfdef, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hiff, hdiv]`. Rewrite using `[h1, ← lintegral_map hf (measurable_const_smul t), Measure.map_addHaar_smul μ ht.ne', lintegral_smul_measure, hd, smul_eq_mul, ← lintegral_const_mul _ hf]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [hfdef]`.

Use `split_ifs with hy`. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]`. Use `congr 2`. Rewrite using `[abs_of_pos (inv_pos.mpr (pow_pos ht _))]`. Establish `htne` using `ht.ne'`.

Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem rayAvg_inner {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ)
    (hΨ : Measurable Ψ) (hd : finrank ℝ E = m + 1) {t : ℝ} (ht : 0 < t) :
    ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ y, (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ := by
  set f : E → ℝ≥0∞ := fun y => if ‖y‖ ≤ t then ENNReal.ofReal (t ^ m * (‖y‖ / t) ^ (m + 1)) * Ψ y else 0
    with hfdef
  have hf : Measurable f := by
    refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hΨ
  have h1 : ∫⁻ v in Metric.closedBall (0:E) 1, ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ
      = ∫⁻ v, f (t • v) ∂μ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    congr 1; ext v
    have hiff : t * ‖v‖ ≤ t ↔ ‖v‖ ≤ 1 := mul_le_iff_le_one_right ht
    have hdiv : t * ‖v‖ / t = ‖v‖ := by field_simp
    simp only [indicator, Metric.mem_closedBall, dist_zero_right, hfdef, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hiff, hdiv]
  rw [h1, ← lintegral_map hf (measurable_const_smul t), Measure.map_addHaar_smul μ ht.ne',
    lintegral_smul_measure, hd, smul_eq_mul, ← lintegral_const_mul _ hf]
  congr 1; ext y
  simp only [hfdef]
  split_ifs with hy
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    rw [abs_of_pos (inv_pos.mpr (pow_pos ht _))]
    have htne := ht.ne'
    rw [div_pow]
    field_simp
    ring
  · simp

/- English proof (translation)
Break down `hr.eq_or_lt with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Use `set g : ℝ → ℝ := fun t => r ^ (m + 1) / t ^ (m + 2) with hgdef`. Establish `hrpow : ∀ t : ℝ, 0 < t → (t ^ (-(m:ℝ) - 2)) = (t ^ (m + 2))⁻¹`.

Introduce `t ht`. Rewrite using `[show (-(m:ℝ) - 2) = -(((m + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg ht.le, Real.rpow_natCast]`. Establish `hcongr : EqOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) g (Ioi r)`. Introduce `t ht`. Simplify using `only [hgdef, hrpow t (hpos.trans ht), div_eq_mul_inv]`.

Establish `hint : IntegrableOn g (Ioi r)` using `(show IntegrableOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) (Ioi r) volume from (integrableOn_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos).const_mul (r ^ (m + 1))).congr_fun hcongr measurableSet_Ioi`. Establish `hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] g` using `by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht`. Establish `: 0 < t` using `hpos.trans ht`. Simplify using `only [Pi.zero_apply, hgdef]`. Check the signs of the components of the expression.

Establish `hval : ∫ t in Ioi r, g t = 1 / ((m:ℝ) + 1)`. Rewrite using `[← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, integral_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos]`. Rewrite using `[show (-(m:ℝ) - 2 + 1) = -(((m + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le, Real.rpow_natCast]`. Establish `: 0 < r ^ (m + 1)` using `pow_pos hpos _`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hgm : Measurable fun t : ℝ => ENNReal.ofReal (g t)` using `ENNReal.measurable_ofReal.comp (by simp only [hgdef]; fun_prop)`. Combine the equalities or inequalities in the displayed calculation. Use `le_trans (setLIntegral_le_lintegral _ _) (le_of_eq ?_)` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `t`. Simplify using `only [indicator, mem_Ici, hgdef]`. Apply the tactic sequence `split_ifs <;> simp`. Use `_ = (∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t) * a := lintegral_mul_const _ (hgm.indicator measurableSet_Ici)`.

Use `_ = (∫⁻ t in Ioi r, ENNReal.ofReal (g t)) * a := by`. Rewrite using `[lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]`. Use `_ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]`.
-/
theorem rayAvg_radial (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0; simp
  set g : ℝ → ℝ := fun t => r ^ (m + 1) / t ^ (m + 2) with hgdef
  have hrpow : ∀ t : ℝ, 0 < t → (t ^ (-(m:ℝ) - 2)) = (t ^ (m + 2))⁻¹ := by
    intro t ht
    rw [show (-(m:ℝ) - 2) = -(((m + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
      Real.rpow_natCast]
  have hcongr : EqOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) g (Ioi r) := by
    intro t ht
    simp only [hgdef, hrpow t (hpos.trans ht), div_eq_mul_inv]
  have hint : IntegrableOn g (Ioi r) :=
    (show IntegrableOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) (Ioi r) volume from
      (integrableOn_Ioi_rpow_of_lt (a := -(m:ℝ) - 2)
        (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos).const_mul (r ^ (m + 1))).congr_fun
      hcongr measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := hpos.trans ht
    simp only [Pi.zero_apply, hgdef]; positivity
  have hval : ∫ t in Ioi r, g t = 1 / ((m:ℝ) + 1) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos]
    rw [show (-(m:ℝ) - 2 + 1) = -(((m + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    have : 0 < r ^ (m + 1) := pow_pos hpos _
    field_simp
    push_cast; ring
  have hgm : Measurable fun t : ℝ => ENNReal.ofReal (g t) :=
    ENNReal.measurable_ofReal.comp (by simp only [hgdef]; fun_prop)
  calc ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t * a := by
        refine le_trans (setLIntegral_le_lintegral _ _) (le_of_eq ?_)
        congr 1; ext t
        simp only [indicator, mem_Ici, hgdef]
        split_ifs <;> simp
    _ = (∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t) * a :=
        lintegral_mul_const _ (hgm.indicator measurableSet_Ici)
    _ = (∫⁻ t in Ioi r, ENNReal.ofReal (g t)) * a := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ Ψ m hΨ hd`. Establish `hF : Measurable fun p : E × ℝ => ENNReal.ofReal (p.2 ^ m * ‖p.1‖ ^ (m + 1)) * Ψ (p.2 • p.1)` using `(ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp (measurable_snd.smul measurable_fst))`. Establish `hK : Measurable fun p : ℝ × E => (if ‖p.2‖ ≤ p.1 then ENNReal.ofReal (‖p.2‖ ^ (m + 1) / p.1 ^ (m + 2)) * Ψ p.2 else 0)`. Use `Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_fst) ?_ measurable_const` and prove the remaining obligations. Conclude with `(ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp measurable_snd)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem rayAvg_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  intro E _ _ _ _ _ μ _ Ψ m hΨ hd
  have hF : Measurable fun p : E × ℝ => ENNReal.ofReal (p.2 ^ m * ‖p.1‖ ^ (m + 1)) * Ψ (p.2 • p.1) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp (measurable_snd.smul measurable_fst))
  have hK : Measurable fun p : ℝ × E =>
      (if ‖p.2‖ ≤ p.1 then ENNReal.ofReal (‖p.2‖ ^ (m + 1) / p.1 ^ (m + 2)) * Ψ p.2 else 0) := by
    refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_fst) ?_
      measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp measurable_snd)
  calc ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ
      = ∫⁻ t in Ioi (0:ℝ), (∫⁻ v in Metric.closedBall (0:E) 1,
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ t in Ioi (0:ℝ), (∫⁻ y,
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ) :=
        setLIntegral_congr_fun measurableSet_Ioi (fun t ht => rayAvg_inner μ Ψ m hΨ hd ht)
    _ = ∫⁻ y, (∫⁻ t in Ioi (0:ℝ),
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0)) ∂μ :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 / ((m : ℝ) + 1)) * Ψ y ∂μ :=
        lintegral_mono (fun y => rayAvg_radial m (norm_nonneg y) (Ψ y))
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := lintegral_const_mul _ hΨ

end GlobalTheory
