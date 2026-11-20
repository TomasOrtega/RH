import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal

/- English proof (translation)
Establish `hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y = (ball (0 : V n) ρ).indicator F (ρ • y)`. Introduce `y`. Establish `hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1`. Simplify using `only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]`. Conclude with `mul_lt_iff_lt_one_right hρ`.

Distinguish the cases in `h : y ∈ ball (0 : V n) 1`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]`. Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]`. Rewrite using `[← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]`. Repeatedly rewrite using `[hind]`.

Establish `hFm : Measurable ((ball (0 : V n) ρ).indicator F)` using `hF.indicator measurableSet_ball`. Rewrite using `[← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne', lintegral_smul_measure, smul_eq_mul]`.
-/
theorem vanish_lintegral_ball_smul (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by
  have hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y =
      (ball (0 : V n) ρ).indicator F (ρ • y) := by
    intro y
    have hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_lt_iff_lt_one_right hρ
    by_cases h : y ∈ ball (0 : V n) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  simp_rw [hind]
  have hFm : Measurable ((ball (0 : V n) ρ).indicator F) := hF.indicator measurableSet_ball
  rw [← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne',
    lintegral_smul_measure, smul_eq_mul]

/- English proof (translation)
Establish `hn0 : 0 < n` using `hn`. Establish `hcr : 0 < c * ρ ^ 2` using `by positivity`. Take `⟨hδ0, hδpos⟩` from `tendsto_nhdsWithin_iff.mp hδ`. Establish `hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `using hδ0.div_const (c * ρ ^ 2)`. Conclude with `hδpos.mono fun k hk => div_pos hk hcr`. Establish `hΦ` using `(hDiv n hn0).comp hη`. Use `set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) * ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK`. Establish `hK0 : K ≠ 0` using `mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'`.

Establish `hlim` using `ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)`. Rewrite `hlim` using `[ENNReal.mul_top hK0]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hδpos] with k hk`. Establish `hk' : 0 < δ k` using `hk`.

Establish `hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))` using `by fun_prop`. Establish `hs` using `vanish_lintegral_ball_smul n _ hG hρ`. Establish `hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) * ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]`. Establish `hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) = ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) * ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ)))`.

Rewrite using `[hs, ← mul_assoc, hd, one_mul]`. Use `show K * _ = _`. Rewrite using `[hrhs, hK, mul_assoc]`. Use `congr 1`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr (fun z => ?_)` and prove the remaining obligations. Establish `hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2)` using `by positivity`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]`. Use `congr 2`.

Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos hρ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem vanish_div (n : ℕ) (hn : 1 ≤ n) (hDiv : C.MVDivStatement) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))) atTop (𝓝 ∞) := by
  have hn0 : 0 < n := hn
  have hcr : 0 < c * ρ ^ 2 := by positivity
  obtain ⟨hδ0, hδpos⟩ := tendsto_nhdsWithin_iff.mp hδ
  have hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hδ0.div_const (c * ρ ^ 2)
    · exact hδpos.mono fun k hk => div_pos hk hcr
  have hΦ := (hDiv n hn0).comp hη
  set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
    ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK
  have hK0 : K ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hlim := ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hK0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hδpos] with k hk
  have hk' : 0 < δ k := hk
  have hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    fun_prop
  have hs := vanish_lintegral_ball_smul n _ hG hρ
  have hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  have hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
        ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    rw [hs, ← mul_assoc, hd, one_mul]
  show K * _ = _
  rw [hrhs, hK, mul_assoc]
  congr 1
  simp only [Function.comp_apply]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun z => ?_)
  have hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp

/- English proof (translation)
Introduce `hn ρ c C0 δ u hρ hc hδ hu hb`. Establish `hW` using `vanish_div n hn hDiv hρ hc hδ`. Use `set W : ℕ → ℝ≥0∞ := fun k => ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) with hWdef`. Establish `hmv : ∀ k, ‖u k 0‖ₑ ^ 2 * W k ≤ ENNReal.ofReal C0`. Introduce `k`.

Establish `hr : Measurable fun t : ℝ => ENNReal.ofReal ((c * t ^ 2 + δ k) ^ (-(n : ℝ)))` using `by fun_prop`. Establish `h1` using `hMV n 0 ρ (u k) _ (hu k) hr`. Simplify using `only [sub_zero] at h1`. Use `le_trans h1 (le_trans (le_of_eq ?_) (hb k))` and prove the remaining obligations. Use `lintegral_congr (fun y => ?_)` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Establish `hbd : ∀ᶠ k in atTop, ‖u k 0‖ₑ ^ 2 ≤ ENNReal.ofReal C0 / W k` using `by filter_upwards [hW.eventually (lt_mem_nhds ENNReal.one_lt_top)] with k hk`. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (lt_trans zero_lt_one hk))) (Or.inr ENNReal.ofReal_ne_top)]`. Conclude with `hmv k`. Establish `hq : Tendsto (fun k => ENNReal.ofReal C0 / W k) atTop (𝓝 0)`.

Use `ENNReal.Tendsto.const_div (a := ENNReal.ofReal C0) hW (Or.inr ENNReal.ofReal_ne_top)` as an intermediate fact. Simplify using `using this`. Establish `hsq : Tendsto (fun k => ‖u k 0‖ₑ ^ 2) atTop (𝓝 0)` using `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq (Filter.Eventually.of_forall fun _ => bot_le) hbd`. Establish `hr : Tendsto (fun k => ‖u k 0‖ ^ 2) atTop (𝓝 0)`. Use `(ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq` as an intermediate fact.

Simplify `this` using `[Function.comp_def, ENNReal.toReal_pow]`. Establish `hn' : Tendsto (fun k => ‖u k 0‖) atTop (𝓝 0)`. Use `(Real.continuous_sqrt.tendsto 0).comp hr` as an intermediate fact. Simplify `this` using `[Function.comp_def, Real.sqrt_sq (norm_nonneg _)]`. Conclude with `tendsto_zero_iff_norm_tendsto_zero.mpr hn'`.
-/
theorem vanish (n : ℕ) (hMV : C.MVStatement) (hDiv : C.MVDivStatement) : VanishStatement n := by
  intro hn ρ c C0 δ u hρ hc hδ hu hb
  have hW := vanish_div n hn hDiv hρ hc hδ
  set W : ℕ → ℝ≥0∞ := fun k => ∫⁻ y in ball (0 : V n) ρ,
    ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) with hWdef
  have hmv : ∀ k, ‖u k 0‖ₑ ^ 2 * W k ≤ ENNReal.ofReal C0 := by
    intro k
    have hr : Measurable fun t : ℝ => ENNReal.ofReal ((c * t ^ 2 + δ k) ^ (-(n : ℝ))) := by
      fun_prop
    have h1 := hMV n 0 ρ (u k) _ (hu k) hr
    simp only [sub_zero] at h1
    refine le_trans h1 (le_trans (le_of_eq ?_) (hb k))
    refine lintegral_congr (fun y => ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbd : ∀ᶠ k in atTop, ‖u k 0‖ₑ ^ 2 ≤ ENNReal.ofReal C0 / W k := by
    filter_upwards [hW.eventually (lt_mem_nhds ENNReal.one_lt_top)] with k hk
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (lt_trans zero_lt_one hk)))
      (Or.inr ENNReal.ofReal_ne_top)]
    exact hmv k
  have hq : Tendsto (fun k => ENNReal.ofReal C0 / W k) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_div (a := ENNReal.ofReal C0) hW (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hsq : Tendsto (fun k => ‖u k 0‖ₑ ^ 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (Filter.Eventually.of_forall fun _ => bot_le) hbd
  have hr : Tendsto (fun k => ‖u k 0‖ ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def, ENNReal.toReal_pow] using this
  have hn' : Tendsto (fun k => ‖u k 0‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hr
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end ReciprocityTheory.L2DbarEstimates.I
