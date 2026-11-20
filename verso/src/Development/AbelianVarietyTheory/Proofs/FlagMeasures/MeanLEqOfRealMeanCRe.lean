import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

/- English proof (translation)
Use `set S : G → ℝ≥0∞ := fun h => ∑' i, ENNReal.ofReal (f i h) with hSdef`. Establish `hnorm : ∀ i h, ‖((f i h : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (f i h)`. Introduce `i h`. Rewrite using `[← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (h0 i h)]`. Establish `hS : ∫⁻ h in 𝓕, S h ∂μ < ⊤`.

Simplify `hI` using `only [hnorm]`. Establish `hSm : Measurable S` using `Measurable.ennreal_tsum (fun i => (hm i).ennreal_ofReal)`. Establish `hae : ∀ᵐ h ∂(μ.restrict 𝓕), S h < ⊤` using `ae_lt_top hSm hS.ne`. Establish `hint : ∫ h in 𝓕, (∑' i, ((f i h : ℝ) : ℂ)) ∂μ = (((∫⁻ h in 𝓕, S h ∂μ).toReal : ℝ) : ℂ)`. Establish `hcongr : (fun h => ∑' i, ((f i h : ℝ) : ℂ)) =ᵐ[μ.restrict 𝓕] fun h => (((S h).toReal : ℝ) : ℂ)` using `by filter_upwards [hae] with h hh`.

Establish `hsum : Summable (fun i => f i h)`. Use `ENNReal.summable_toReal hh.ne using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `(ENNReal.toReal_ofReal (h0 i h)).symm`. Use `show _ = (((∑' i, ENNReal.ofReal (f i h)).toReal : ℝ) : ℂ)`.

Rewrite using `[← Complex.ofReal_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i h) hsum, ENNReal.toReal_ofReal (tsum_nonneg (fun i => h0 i h))]`. Rewrite using `[integral_congr_ae hcongr, integral_complex_ofReal, integral_toReal hSm.aemeasurable hae]`. Unfold `meanL meanC`. Rewrite using `[hint, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]`. Distinguish the cases in `hz : μ 𝓕 = 0`.

Establish `hr : μ.restrict 𝓕 = 0` using `Measure.restrict_eq_zero.mpr hz`. Simplify using `[hr, hz]`. Rewrite using `[ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hS.ne, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hz)]`.
-/
theorem meanL_eq_ofReal_meanC_re (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G)
    (ι : Type) [Countable ι] (f : ι → G → ℝ) (hm : ∀ i, Measurable (f i))
    (h0 : ∀ i h, 0 ≤ f i h) (hF : μ 𝓕 < ⊤)
    (hI : ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤) :
    meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) =
      ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  set S : G → ℝ≥0∞ := fun h => ∑' i, ENNReal.ofReal (f i h) with hSdef
  have hnorm : ∀ i h, ‖((f i h : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (f i h) := by
    intro i h
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (h0 i h)]
  have hS : ∫⁻ h in 𝓕, S h ∂μ < ⊤ := by
    simpa only [hnorm] using hI
  have hSm : Measurable S := Measurable.ennreal_tsum (fun i => (hm i).ennreal_ofReal)
  have hae : ∀ᵐ h ∂(μ.restrict 𝓕), S h < ⊤ := ae_lt_top hSm hS.ne
  have hint : ∫ h in 𝓕, (∑' i, ((f i h : ℝ) : ℂ)) ∂μ = (((∫⁻ h in 𝓕, S h ∂μ).toReal : ℝ) : ℂ) := by
    have hcongr : (fun h => ∑' i, ((f i h : ℝ) : ℂ)) =ᵐ[μ.restrict 𝓕]
        fun h => (((S h).toReal : ℝ) : ℂ) := by
      filter_upwards [hae] with h hh
      have hsum : Summable (fun i => f i h) := by
        convert ENNReal.summable_toReal hh.ne using 1
        funext i
        exact (ENNReal.toReal_ofReal (h0 i h)).symm
      show _ = (((∑' i, ENNReal.ofReal (f i h)).toReal : ℝ) : ℂ)
      rw [← Complex.ofReal_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i h) hsum,
        ENNReal.toReal_ofReal (tsum_nonneg (fun i => h0 i h))]
    rw [integral_congr_ae hcongr, integral_complex_ofReal, integral_toReal hSm.aemeasurable hae]
  unfold meanL meanC
  rw [hint, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  by_cases hz : μ 𝓕 = 0
  · have hr : μ.restrict 𝓕 = 0 := Measure.restrict_eq_zero.mpr hz
    simp [hr, hz]
  · rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hS.ne,
      ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hz)]

end GlobalTheory
