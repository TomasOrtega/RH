import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

/- English proof (translation)
The claim follows from `Classical.choose_spec (A.cover x)`.
-/
lemma mem_source_chartIdx (A : FinHolAtlas D X) (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

/- English proof (translation)
The claim follows from `inter_eq_left.2 fun _ hy => (A.chart j).map_target hy`.
-/
lemma target_inter_symm_source (A : FinHolAtlas D X) (j : Fin A.n) :
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
  inter_eq_left.2 fun _ hy => (A.chart j).map_target hy

/- English proof (translation)
Introduce `D X _ _ _ _ _ A L W dV hW V _ hV x ε hε`. Use `dV.isProb` as an intermediate fact. Use `set k := chartIdx A x with hk`. Use `set e := A.chart k with he`. Establish `hx : x ∈ e.source` using `mem_source_chartIdx A x`.

Establish `hy0 : e x ∈ e.target` using `e.map_source hx`. Establish `hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target`. Use `W.smooth k k` as an intermediate fact. Rewrite `this` using `[target_inter_symm_source]`. Then use the resulting hypothesis. Establish `hmain` using `hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0 (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0) (fun w => hW k (e x) hy0 w) ε hε`.

Establish `hb : bergmanDens W dV x = (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x)`. Establish `hD : (D.factorial : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)`. Conclude with `mul_div_mul_left _ _ hD`. Use `filter_upwards [hmain] with n hn`. Rewrite `hn` using `[← hb]`.

Use `set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK`. Establish `hKpos : 0 < K`. Assume the negation of the conclusion as `hle`. Establish `h1` using `hn (fun _ => 1) analyticOnNhd_const`. Rewrite `h1` using `[ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]`.

Establish `: 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x))`. Simplify using `[Real.exp_pos]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `ciSup_le fun s => ?_` and prove the remaining obligations. Establish `hs : (s : Fin A.n → X → ℂ) ∈ L.sections n` using `hV n s.2`.

Establish `hcont` using `continuous_ptNormSq W hs`. Establish `hnn : ∀ z, 0 ≤ ptNormSq W n s z` using `ptNormSq_nonneg W n s`. Establish `hint : Integrable (ptNormSq W n s) dV.μ` using `integrable_ptNormSq W dV hs`. Establish `hl2 : 0 ≤ sectionL2NormSq W dV n s` using `sectionL2NormSq_nonneg W dV n s`. Establish `hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target`.

Use `hs.1 k k` as an intermediate fact. Rewrite `this` using `[target_inter_symm_source]`. Then use the resulting hypothesis. Establish `h1` using `hn _ hF`. Establish `hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x`. Simplify using `only [Function.comp, e.left_inv hx]`.

Both sides reduce to the same expression. Establish `hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤ ENNReal.ofReal (sectionL2NormSq W dV n s)`. Establish `hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z)` using `hcont.measurable.ennreal_ofReal`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]`. Both sides reduce to the same expression. Use `_ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := (dV.chart_lintegral k _ hmeas).symm`. Use `_ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _`. Use `_ = ENNReal.ofReal (sectionL2NormSq W dV n s) := (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm`.

Rewrite `h1` using `[hleft]`. Establish `h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s)`. Rewrite using `[ENNReal.ofReal_mul hKpos.le]`. Conclude with `h1.trans (by gcongr)`. Establish `h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s` using `(ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2`.

Break down `hl2.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, div_zero]`. Conclude with `hKpos.le`. Conclude with `(div_le_iff₀ hpos).2 h3`.
-/
theorem LocalBergmanBound.proof (hC : ChartBergmanBound.Statement) :
    LocalBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV x ε hε
  have := dV.isProb
  set k := chartIdx A x with hk
  set e := A.chart k with he
  have hx : x ∈ e.source := mem_source_chartIdx A x
  have hy0 : e x ∈ e.target := e.map_source hx
  have hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target := by
    have := W.smooth k k
    rwa [target_inter_symm_source] at this
  have hmain := hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0
    (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0)
    (fun w => hW k (e x) hy0 w) ε hε
  have hb : bergmanDens W dV x =
      (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x) := by
    have hD : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
    exact mul_div_mul_left _ _ hD
  filter_upwards [hmain] with n hn
  rw [← hb] at hn
  set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK

  have hKpos : 0 < K := by
    by_contra hle
    have h1 := hn (fun _ => 1) analyticOnNhd_const
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h1
    have : 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) := by
      simp [Real.exp_pos]
    linarith
  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV n s.2
  have hcont := continuous_ptNormSq W hs
  have hnn : ∀ z, 0 ≤ ptNormSq W n s z := ptNormSq_nonneg W n s
  have hint : Integrable (ptNormSq W n s) dV.μ := integrable_ptNormSq W dV hs
  have hl2 : 0 ≤ sectionL2NormSq W dV n s := sectionL2NormSq_nonneg W dV n s

  have hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target := by
    have := hs.1 k k
    rwa [target_inter_symm_source] at this
  have h1 := hn _ hF
  have hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x := by
    simp only [Function.comp, e.left_inv hx]
    rfl
  have hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤
        ENNReal.ofReal (sectionL2NormSq W dV n s) := by
    have hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z) :=
      hcont.measurable.ennreal_ofReal
    calc _ = ∫⁻ y in e.target, ENNReal.ofReal (ptNormSq W n s (e.symm y)) *
          ENNReal.ofReal (dV.dens k y) := by
          refine setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]
          rfl
      _ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ :=
          (dV.chart_lintegral k _ hmeas).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sectionL2NormSq W dV n s) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
  rw [hleft] at h1
  have h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s) := by
    rw [ENNReal.ofReal_mul hKpos.le]
    exact h1.trans (by gcongr)
  have h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2
  rcases hl2.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hKpos.le
  · exact (div_le_iff₀ hpos).2 h3

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
