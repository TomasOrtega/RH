import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `X ι _ _ m e he`. Establish `hL : ∀ u : X → ℝ≥0∞, Measurable u → ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m`. Introduce `u hu`. Establish `hm : ∀ i, AEMeasurable (fun x => u (e i x)) m` using `fun i => (hu.comp (he i)).aemeasurable`. Rewrite using `[lintegral_sum_measure, lintegral_tsum hm]`.

Conclude with `tsum_congr fun i => lintegral_map hu (he i)`. Use `⟨hL, fun u hu hint => ?_⟩` and prove the remaining obligations. Establish `hum : Measurable fun x => ‖u x‖ₑ` using `hu.enorm`. Establish `hfin : ∫⁻ x, ∑' i, ‖u (e i x)‖ₑ ∂m < ⊤`. Rewrite using `[← hL _ hum]`.

Conclude with `hint.2`. Establish `hmeas : Measurable fun x => ∑' i, ‖u (e i x)‖ₑ` using `Measurable.ennreal_tsum fun i => hum.comp (he i)`. Establish `hsum : ∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖` using `by filter_upwards [ae_lt_top hmeas hfin.ne] with x hx`. Establish `h1 : ∑' i, ((‖u (e i x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤` using `hx.ne`. Conclude with `NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)`.

Establish `hsm : ∀ i, AEStronglyMeasurable (fun x => u (e i x)) m` using `fun i => (hu.comp (he i)).aestronglyMeasurable`. Establish `hlim : ∀ᵐ x ∂m, Tendsto (fun s : Finset ι => ∑ i ∈ s, u (e i x)) atTop (𝓝 (∑' i, u (e i x)))` using `by filter_upwards [hsum] with x hx`. Conclude with `hx.of_norm.hasSum`. Establish `hae : AEStronglyMeasurable (fun x => ∑' i, u (e i x)) m` using `aestronglyMeasurable_of_tendsto_ae atTop (fun s : Finset ι => Finset.aestronglyMeasurable_fun_sum s fun i _ => hsm i) hlim`. Establish `hI : Integrable (fun x => ∑' i, u (e i x)) m`.

Use `⟨hae, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin⟩` and prove the remaining obligations. Conclude with `enorm_tsum_le_tsum_enorm`. Use `⟨hsum, hI, ?_⟩` and prove the remaining obligations. Establish `hne : ∑' i, ∫⁻ x, ‖u (e i x)‖ₑ ∂m ≠ ⊤`. Establish `hm : ∀ i, AEMeasurable (fun x => ‖u (e i x)‖ₑ) m` using `fun i => (hum.comp (he i)).aemeasurable`.

Rewrite using `[← lintegral_tsum hm]`. Conclude with `hfin.ne`. Rewrite using `[integral_tsum hsm hne, integral_sum_measure hint]`. Conclude with `tsum_congr fun i => (integral_map (he i).aemeasurable hu.aestronglyMeasurable).symm`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.sumSide :
    ∀ (X ι : Type) [MeasurableSpace X] [Countable ι] (m : Measure X) (e : ι → X → X), (∀ i, Measurable (e i)) → (∀ u : X → ℝ≥0∞, Measurable u → ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m) ∧ ∀ u : X → ℂ, Measurable u → Integrable u (Measure.sum fun i => m.map (e i)) → (∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m ∧ ∫ x, ∑' i, u (e i x) ∂m = ∫ x, u x ∂(Measure.sum fun i => m.map (e i)) := by
  intro X ι _ _ m e he
  have hL : ∀ u : X → ℝ≥0∞, Measurable u →
      ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m := by
    intro u hu
    have hm : ∀ i, AEMeasurable (fun x => u (e i x)) m := fun i => (hu.comp (he i)).aemeasurable
    rw [lintegral_sum_measure, lintegral_tsum hm]
    exact tsum_congr fun i => lintegral_map hu (he i)
  refine ⟨hL, fun u hu hint => ?_⟩
  have hum : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hfin : ∫⁻ x, ∑' i, ‖u (e i x)‖ₑ ∂m < ⊤ := by
    rw [← hL _ hum]
    exact hint.2
  have hmeas : Measurable fun x => ∑' i, ‖u (e i x)‖ₑ :=
    Measurable.ennreal_tsum fun i => hum.comp (he i)
  have hsum : ∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖ := by
    filter_upwards [ae_lt_top hmeas hfin.ne] with x hx
    have h1 : ∑' i, ((‖u (e i x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hsm : ∀ i, AEStronglyMeasurable (fun x => u (e i x)) m := fun i =>
    (hu.comp (he i)).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂m, Tendsto (fun s : Finset ι => ∑ i ∈ s, u (e i x)) atTop
      (𝓝 (∑' i, u (e i x))) := by
    filter_upwards [hsum] with x hx
    exact hx.of_norm.hasSum
  have hae : AEStronglyMeasurable (fun x => ∑' i, u (e i x)) m :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => Finset.aestronglyMeasurable_fun_sum s fun i _ => hsm i) hlim
  have hI : Integrable (fun x => ∑' i, u (e i x)) m := by
    refine ⟨hae, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin⟩
    exact enorm_tsum_le_tsum_enorm
  refine ⟨hsum, hI, ?_⟩
  have hne : ∑' i, ∫⁻ x, ‖u (e i x)‖ₑ ∂m ≠ ⊤ := by
    have hm : ∀ i, AEMeasurable (fun x => ‖u (e i x)‖ₑ) m := fun i =>
      (hum.comp (he i)).aemeasurable
    rw [← lintegral_tsum hm]
    exact hfin.ne
  rw [integral_tsum hsm hne, integral_sum_measure hint]
  exact tsum_congr fun i => (integral_map (he i).aemeasurable hu.aestronglyMeasurable).symm
