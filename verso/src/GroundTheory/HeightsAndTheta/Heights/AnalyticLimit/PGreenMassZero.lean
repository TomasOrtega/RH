import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh IsPosPot IsSection logNormSec mInt
  MIntegrable maMeasure maMeasure_thm logNormIntegrable mIntegrableCont)

noncomputable section

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover y`. Use `set c := A.chart j`. Establish `hopen : IsOpen (c.target ∩ c.symm ⁻¹' U)` using `c.isOpen_inter_preimage_symm hU`. Establish `hmem : c y ∈ c.target ∩ c.symm ⁻¹' U` using `⟨c.map_source hj, by show c.symm (c y) ∈ U`. Rewrite using `[c.left_inv hj]`.

Conclude with `hy⟩`. Establish `h1 : ContinuousAt (g ∘ c.symm) (c y)` using `(hg j).continuousAt (hopen.mem_nhds hmem)`. Establish `h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y` using `h1.comp (c.continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [c.open_source.mem_nhds hj] with z hz`.

Simplify using `[Function.comp, c.left_inv hz]`.
-/
theorem continuousAt_of_charts {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type}
    [TopologicalSpace E] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) (g : X → E)
    (hg : ∀ j, ContinuousOn (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hj, by
    show c.symm (c y) ∈ U
    rw [c.left_inv hj]
    exact hy⟩
  have h1 : ContinuousAt (g ∘ c.symm) (c y) := (hg j).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y := h1.comp (c.continuousAt hj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with z hz
  simp [Function.comp, c.left_inv hz]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`. Establish `hsc : ContinuousAt (s x₀) x₀` using `continuousAt_of_charts A (L.isOpen_U x₀) (s x₀) (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)`. Establish `hφc : ContinuousAt (L.φ x₀) x₀` using `continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀) (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)`. Establish `hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀` using `hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)`.

Use `hf.congr ?_` and prove the remaining obligations. Use `filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy`. Conclude with `hs.2 x₀ y y ⟨hy, L.mem_U y⟩`.
-/
theorem continuous_secNorm {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (secNorm L s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsc : ContinuousAt (s x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (s x₀)
    (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hφc : ContinuousAt (L.φ x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀)
    (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀ :=
    hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)
  refine hf.congr ?_
  filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy
  exact hs.2 x₀ y y ⟨hy, L.mem_U y⟩

/- English proof (translation)
Introduce `x j y hy w`. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Simplify using `[levi]`. Conclude with `(hP x j y hy w hw).le`.
-/
theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (hP x j y hy w hw).le

/- English proof (translation)
Unfold `greenEp`. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `: 0 ≤ ε / secNorm L s x ^ 2` using `div_nonneg hε (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem greenEp_nonneg {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : W) : 0 ≤ greenEp L s ε x := by
  unfold greenEp
  apply Real.log_nonneg
  have : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  linarith

/- English proof (translation)
Unfold `greenEp`. Establish `h0 : 0 ≤ ε / secNorm L s x ^ 2` using `div_nonneg hε (sq_nonneg _)`. Apply `Real.log_le_log (by linarith)` to reduce the goal to its premises. Establish `: ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2` using `div_le_div_of_nonneg_right hε1 (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem greenEp_le_one {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) : greenEp L s ε x ≤ greenEp L s 1 x := by
  unfold greenEp
  have h0 : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  apply Real.log_le_log (by linarith)
  have : ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2 :=
    div_le_div_of_nonneg_right hε1 (sq_nonneg _)
  linarith

/- English proof (translation)
Establish `hl : logNormSec L s x = Real.log (secNorm L s x)` using `rfl`. Unfold `greenEp`. Rewrite using `[hl]`. Distinguish the cases in `hN : secNorm L s x = 0`. Simplify using `[hN]`.

Establish `h2 : secNorm L s x ^ 2 ≠ 0` using `pow_ne_zero 2 hN`. Establish `h3 : secNorm L s x ^ 2 + 1 ≠ 0` using `by positivity`. Rewrite using `[show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by field_simp, Real.log_div h3 h2, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem greenEp_one_eq {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) (x : W) :
    greenEp L s 1 x = Real.log (secNorm L s x ^ 2 + 1) - 2 * logNormSec L s x := by
  have hl : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp
  rw [hl]
  by_cases hN : secNorm L s x = 0
  · simp [hN]
  · have h2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h3 : secNorm L s x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by
      field_simp, Real.log_div h3 h2, Real.log_pow]
    push_cast
    ring

/- English proof (translation)
Unfold `greenEp`. Use `set c := secNorm L s x ^ 2`. Establish `hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0` using `(continuous_const.add (continuous_id.div_const c)).continuousAt`. Establish `hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0` using `hc.log (by simp)`. Establish `ht` using `hlog.tendsto`.

Simplify using `only [zero_div, add_zero, Real.log_one] at ht`. Conclude with `tendsto_nhdsWithin_of_tendsto_nhds ht`.
-/
theorem greenEp_tendsto_zero {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ)
    (x : W) : Tendsto (fun ε => greenEp L s ε x) (𝓝[>] 0) (𝓝 0) := by
  unfold greenEp
  set c := secNorm L s x ^ 2
  have hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0 :=
    (continuous_const.add (continuous_id.div_const c)).continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0 := hc.log (by simp)
  have ht := hlog.tendsto
  simp only [zero_div, add_zero, Real.log_one] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

/- English proof (translation)
Introduce `D W _ _ _ S η hη`. Set `: MeasurableSpace W` to `borel W`. Establish `: BorelSpace W` using `⟨rfl⟩`. Use `set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef`. Establish `hΦ : ∀ i, IsPotential S.A (Φ i)` using `fun _ => S.Om.isPot`.

Establish `hΦpsh : ∀ i, IsPsh S.A (Φ i)` using `fun _ => isPsh_of_isPosPot S.A _ S.Om.pos`. Take `⟨hfin, hμ⟩` from `maMeasure_thm S.A Φ hΦ hΦpsh`. Use `set μ := maMeasure S.A Φ`. Establish `hN : Continuous (secNorm S.L S.s)` using `continuous_secNorm S.A S.L S.s S.L_pot S.s_sec`. Establish `hmeas : ∀ ε, Measurable (greenEp S.L S.s ε)` using `fun ε => ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log`.

Establish `hlogN : Integrable (logNormSec S.L S.s) μ`. Establish `hm : Measurable (logNormSec S.L S.s)` using `hN.measurable.log`. Conclude with `((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)`. Establish `hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ`. Establish `hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)` using `((hN.pow 2).add continuous_const).log fun x => (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'`.

Conclude with `((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)`. Establish `hG1 : Integrable (greenEp S.L S.s 1) μ`. Establish `: greenEp S.L S.s 1 = fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x`. Use function extensionality and compare the values at `(greenEp_one_eq S.L S.s)`. Rewrite using `[this]`.

Conclude with `hh.sub (hlogN.const_mul 2)`. Establish `hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x` using `fun ε hε hε1 x => by`. Rewrite using `[Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]`. Conclude with `greenEp_le_one S.L S.s hε.le hε1 x`. Establish `hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ`.

Introduce `ε hε hε1 t`. Establish `hmix : mixedForms S.Om.pot (S.T t) 0 = Φ`. Use function extensionality and compare the values at `i`. Simplify using `[mixedForms, hΦdef]`. Establish `hint : Integrable (greenEp S.L S.s ε) μ` using `hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))`.

Establish `hmi : MIntegrable S.A Φ (greenEp S.L S.s ε)` using `((hμ _ (hmeas ε)).1).2 hint`. Use `show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _`. Rewrite using `[hmix]`. Conclude with `(hμ _ (hmeas ε)).2 hmi`. Establish `hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0)`.

Use `tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ)) (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1) (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable) (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε …` as an intermediate fact. Simplify using `using this`. Establish `hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η` using `(tendsto_order.1 hT).2 η hη`. Take `⟨u, hu, hsub⟩` from `mem_nhdsGT_iff_exists_Ioo_subset.1 hev`. Establish `hu0 : (0 : ℝ) < u` using `hu`.

Use `⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩` and prove the remaining obligations. Establish `hε1 : ε ≤ 1` using `hεle.trans (min_le_right _ _)`. Establish `hεu : ε < u` using `lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)`. Rewrite using `[hJ ε hε hε1 t]`. Conclude with `(hsub ⟨hε, hεu⟩).le`.
-/
theorem GreenMassZero.proof : GreenMassZero.Statement := by
  intro D W _ _ _ S η hη
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef
  have hΦ : ∀ i, IsPotential S.A (Φ i) := fun _ => S.Om.isPot
  have hΦpsh : ∀ i, IsPsh S.A (Φ i) := fun _ => isPsh_of_isPosPot S.A _ S.Om.pos
  obtain ⟨hfin, hμ⟩ := maMeasure_thm S.A Φ hΦ hΦpsh
  set μ := maMeasure S.A Φ
  have hN : Continuous (secNorm S.L S.s) := continuous_secNorm S.A S.L S.s S.L_pot S.s_sec
  have hmeas : ∀ ε, Measurable (greenEp S.L S.s ε) := fun ε =>
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log

  have hlogN : Integrable (logNormSec S.L S.s) μ := by
    have hm : Measurable (logNormSec S.L S.s) := hN.measurable.log
    exact ((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)
  have hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ := by
    have hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) :=
      ((hN.pow 2).add continuous_const).log fun x =>
        (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'
    exact ((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp S.L S.s 1) μ := by
    have : greenEp S.L S.s 1 = fun x =>
        Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x :=
      funext (greenEp_one_eq S.L S.s)
    rw [this]
    exact hh.sub (hlogN.const_mul 2)
  have hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x :=
    fun ε hε hε1 x => by
      rw [Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]
      exact greenEp_le_one S.L S.s hε.le hε1 x

  have hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ := by
    intro ε hε hε1 t
    have hmix : mixedForms S.Om.pot (S.T t) 0 = Φ := by
      funext i
      simp [mixedForms, hΦdef]
    have hint : Integrable (greenEp S.L S.s ε) μ :=
      hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))
    have hmi : MIntegrable S.A Φ (greenEp S.L S.s ε) := ((hμ _ (hmeas ε)).1).2 hint
    show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _
    rw [hmix]
    exact (hμ _ (hmeas ε)).2 hmi

  have hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε => ae_of_all _ (hnorm ε hε.1 hε.2))
      hG1 (ae_of_all _ fun x => greenEp_tendsto_zero S.L S.s x)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η := (tendsto_order.1 hT).2 η hη
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hεu : ε < u := lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)
  rw [hJ ε hε hε1 t]
  exact (hsub ⟨hε, hεu⟩).le

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
