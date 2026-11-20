import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrincipleStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PuncturedDisc

/- English proof (translation)
Introduce `w hw0 hwρ`. Establish `hlogw : Real.log ‖w‖ < Real.log ρ` using `Real.log_lt_log hw0 hwρ`. Establish `hD : 0 < Real.log ρ - Real.log ‖w‖` using `sub_pos.mpr hlogw`. Establish `key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖)`. Introduce `ε hε`.

Establish `hexp_pos : 0 < Real.exp (-(|C| / ε))` using `Real.exp_pos _`. Establish `hexp_le : Real.exp (-(|C| / ε)) ≤ 1`. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 ≤ |C| / ε` using `div_nonneg (abs_nonneg C) hε.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2` from `⟨_, rfl⟩`. Establish `hr0 : 0 < r`. Rewrite using `[hr_def]`. Conclude with `div_pos (mul_pos hw0 hexp_pos) two_pos`. Establish `hrw : r < ‖w‖`.

Use `mul_le_mul_of_nonneg_left hexp_le hw0.le` as an intermediate fact. Rewrite using `[hr_def]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrρ : r < ρ` using `lt_trans hrw hwρ`. Establish `hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2`.

Rewrite using `[hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero, Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree. Set `h : ℂ → ℝ` to `fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)`. Establish `hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ}`. Establish `hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ}` using `fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩`.

Use `(hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))` and prove the remaining obligations. Use `ContinuousOn.log continuous_norm.continuousOn ?_` and prove the remaining obligations. Introduce `z hz`. Conclude with `(lt_of_lt_of_le hr0 hz.1).ne'`. Establish `hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z`.

Introduce `z hz1 hz2`. Establish `hz0 : 0 < ‖z‖` using `lt_trans hr0 hz1`. Establish `hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z` using `analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)`. Establish `hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z` using `InnerProductSpace.harmonicAt_const _`. Establish `h2 : InnerProductSpace.HarmonicAt (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z`.

Apply `InnerProductSpace.HarmonicAt.const_smul` to reduce the goal to its premises. Conclude with `hcst.sub hlog`. Conclude with `(hh z hz0 hz2).sub h2`. Establish `hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0`. Introduce `z hz`.

Break down `hz with hz | hz` into its components or cases. Establish `hgz : g z ≤ C` using `hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)`. Establish `hCabs : C ≤ |C|` using `le_abs_self C`. Establish `hlog2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Use `show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0`.

Rewrite using `[hz, hlogr]`. Establish `e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) = ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2` using `by ring`. Establish `e2 : ε * (|C| / ε) = |C|` using `by field_simp`. Rewrite using `[e1, e2]`. Combine the linear relations using `[mul_pos hε hD, mul_pos hε hlog2]`.

Use `show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0`. Rewrite using `[hz, sub_self, mul_zero, sub_zero]`. Conclude with `h0 z hz`. Establish `hmax` using `GlobalTheory.T.harmonic_annulus_maximum_principle h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le`. Simplify using `only [h] at hmax`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hneg`. Establish `hpos` using `not_le.mp hneg`. Establish `hk` using `key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))`. Establish `e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2`.

Rewrite using `[div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_zero_of_bddAbove_punctured (g : ℂ → ℝ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hc : ContinuousOn g {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hh : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt g z)
    (h0 : ∀ z : ℂ, ‖z‖ = ρ → g z ≤ 0)
    (hC : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → g z ≤ C) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → g w ≤ 0 := by
  intro w hw0 hwρ
  have hlogw : Real.log ‖w‖ < Real.log ρ := Real.log_lt_log hw0 hwρ
  have hD : 0 < Real.log ρ - Real.log ‖w‖ := sub_pos.mpr hlogw
  have key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖) := by
    intro ε hε
    have hexp_pos : 0 < Real.exp (-(|C| / ε)) := Real.exp_pos _
    have hexp_le : Real.exp (-(|C| / ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
      linarith
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2 := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr_def]
      exact div_pos (mul_pos hw0 hexp_pos) two_pos
    have hrw : r < ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp_le hw0.le
      rw [hr_def]
      linarith
    have hrρ : r < ρ := lt_trans hrw hwρ
    have hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2 := by
      rw [hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero,
        Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]
      ring
    let h : ℂ → ℝ := fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)
    have hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} :=
        fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩
      refine (hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))
      refine ContinuousOn.log continuous_norm.continuousOn ?_
      intro z hz
      exact (lt_of_lt_of_le hr0 hz.1).ne'
    have hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr0 hz1
      have hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)
      have hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z :=
        InnerProductSpace.harmonicAt_const _
      have h2 : InnerProductSpace.HarmonicAt
          (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z := by
        apply InnerProductSpace.HarmonicAt.const_smul
        exact hcst.sub hlog
      exact (hh z hz0 hz2).sub h2
    have hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hgz : g z ≤ C := hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)
        have hCabs : C ≤ |C| := le_abs_self C
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, hlogr]
        have e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) =
            ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2 := by ring
        have e2 : ε * (|C| / ε) = |C| := by field_simp
        rw [e1, e2]
        linarith [mul_pos hε hD, mul_pos hε hlog2]
      · show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, sub_self, mul_zero, sub_zero]
        exact h0 z hz
    have hmax := GlobalTheory.T.harmonic_annulus_maximum_principle h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le
    simp only [h] at hmax
    linarith
  by_contra hneg
  have hpos := not_le.mp hneg
  have hk := key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))
  have e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
  linarith

/- English proof (translation)
Establish `hρabs : |ρ| = ρ` using `abs_of_pos hρ`. Establish `hfc : ContinuousOn f (Metric.sphere 0 ρ)`. Introduce `z hz`. Establish `hz' : ‖z‖ = ρ` using `by simpa using hz`. Establish `hz0 : z ≠ 0`.

Introduce `h`. Rewrite `hz'` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt`. Establish `hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M`.

Introduce `z hz`. Establish `hzb : z ∈ Metric.ball (0 : ℂ) ρ` using `by simpa using hz`. Establish `hup` using `ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M`. Establish `hlo` using `ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)`. Establish `hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x`.

Introduce `x hx`. Rewrite `hx` using `[hρabs]`. Establish `hx' : ‖x‖ = ρ` using `by simpa using hx`. Establish `hx0 : x ≠ 0`. Introduce `h`.

Rewrite `hx'` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩`. Establish `h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ` using `Real.circleAverage_nonneg_of_nonneg fun x hx => by`. Take `⟨hb, hk⟩` from `hsph x hx`.

Use `(abs_le.mp hb).2` as an intermediate fact. Establish `: 0 ≤ poissonKernel 0 z x * (M - f x)` using `mul_nonneg hk (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ = -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ`. Simplify using `only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]`.

Establish `h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ` using `Real.circleAverage_nonneg_of_nonneg fun x hx => by`. Take `⟨hb, hk⟩` from `hsph x hx`. Use `(abs_le.mp hb).1` as an intermediate fact. Conclude with `mul_nonneg hk (by linarith)`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith`. Set `Φ : ℂ → ℝ` to `fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z`. Establish `hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z`. Introduce `z hz`. Establish `hzb : z ∈ Metric.ball (0 : ℂ) ρ` using `by simpa using hz`.

Establish `hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ` using `by filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy`. Establish `: ‖y‖ < ρ` using `by simpa using hy`. Simplify using `only [Φ, if_pos this]`. Conclude with `(InnerProductSpace.harmonicAt_congr_nhds hev).mpr (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)`. Establish `hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ)`.

Introduce `z hz`. Distinguish the cases in `hzl : ‖z‖ < ρ`. Conclude with `(hPharm z hzl).1.continuousAt.continuousWithinAt`. Establish `hzle : ‖z‖ ≤ ρ` using `by simpa using hz`. Establish `hzeq : ‖z‖ = ρ` using `le_antisymm hzle (not_lt.mp hzl)`.

Establish `hzs : z ∈ Metric.sphere (0 : ℂ) ρ` using `by simpa using hzeq`. Establish `hΦz : Φ z = f z` using `by simp only [Φ, if_neg hzl]`. Rewrite using `[← Metric.ball_union_sphere]`. Apply `ContinuousWithinAt.union` to reduce the goal to its premises. Rewrite using `[ContinuousWithinAt, hΦz]`.

Use `Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with y hy`. Establish `: ‖y‖ < ρ` using `by simpa using hy`. Simplify using `only [Φ, if_pos this]`. Rewrite using `[ContinuousWithinAt, hΦz]`.

Use `Filter.Tendsto.congr' ?_ (hfc z hzs)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with y hy`. Establish `hy' : ‖y‖ = ρ` using `by simpa using hy`. Simplify using `only [Φ, if_neg (not_lt.mpr hy'.ge)]`. Establish `hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z`.

Introduce `z hz`. Simplify using `only [Φ, if_neg (not_lt.mpr hz.ge)]`. Establish `hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ` using `fun z hz => by`. Simplify using `using hz.2`. Establish `hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ}` using `fun z hz => (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt`.

Establish `hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M`. Introduce `z hz0 hzρ`. Distinguish the cases in `hzl : ‖z‖ < ρ`. Simplify using `only [Φ, if_pos hzl]`. Conclude with `hPbd z hzl`.

Simplify using `only [Φ, if_neg hzl]`. Conclude with `hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)`. Establish `hA` using `le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ (hfS.sub (hΦcont.mono hS)) (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ)) (fun z hz => by simp only [hΦb z hz, sub_self, le_refl]) (fun z hz0 hzρ => by`. Establish `h1` using `abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))`. Establish `h2` using `abs_le.mp (hΦbd z hz0 hzρ)`.

Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2])`. Use `w (norm_pos_iff.mpr hw0) hwρ`. Establish `hA'` using `le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ ((hΦcont.mono hS).sub hfS) (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR))) (fun z hz => by simp only [hΦb z hz, sub_self, le_refl]) (fun z hz0 hzρ => by`. Establish `h1` using `abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))`. Establish `h2` using `abs_le.mp (hΦbd z hz0 hzρ)`.

Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2])`. Use `w (norm_pos_iff.mpr hw0) hwρ`. Establish `hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w` using `by simp only [Φ, if_pos hwρ]`. Establish `hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w` using `by linarith`. Rewrite using `[hfw]`.

Establish `hint` using `GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ`. Conclude with `hint`.
-/
theorem poisson_formula_punctured (f : ℂ → ℝ) (ρ R M : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → InnerProductSpace.HarmonicAt f z)
    (hB : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → |f z| ≤ M) (w : ℂ) (hw0 : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    ∫ t, pker ρ w t * f (circleMap 0 ρ t) ∂angMeas = f w := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  have hfc : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      linarith
    exact (hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt
  have hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hup := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M
    have hlo := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)
    have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x := by
      intro x hx
      rw [hρabs] at hx
      have hx' : ‖x‖ = ρ := by simpa using hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx'
        linarith
      exact ⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩
    have h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).2
        have : 0 ≤ poissonKernel 0 z x * (M - f x) := mul_nonneg hk (by linarith)
        linarith
    have h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ =
        -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ := by
      simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
    have h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).1
        exact mul_nonneg hk (by linarith)
    rw [abs_le]
    constructor <;> linarith
  let Φ : ℂ → ℝ := fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z
  have hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      have : ‖y‖ < ρ := by simpa using hy
      simp only [Φ, if_pos this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr
      (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)
  have hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ) := by
    intro z hz
    by_cases hzl : ‖z‖ < ρ
    · exact (hPharm z hzl).1.continuousAt.continuousWithinAt
    · have hzle : ‖z‖ ≤ ρ := by simpa using hz
      have hzeq : ‖z‖ = ρ := le_antisymm hzle (not_lt.mp hzl)
      have hzs : z ∈ Metric.sphere (0 : ℂ) ρ := by simpa using hzeq
      have hΦz : Φ z = f z := by simp only [Φ, if_neg hzl]
      rw [← Metric.ball_union_sphere]
      apply ContinuousWithinAt.union
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have : ‖y‖ < ρ := by simpa using hy
        simp only [Φ, if_pos this]
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (hfc z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : ‖y‖ = ρ := by simpa using hy
        simp only [Φ, if_neg (not_lt.mpr hy'.ge)]
  have hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z := by
    intro z hz
    simp only [Φ, if_neg (not_lt.mpr hz.ge)]
  have hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ := fun z hz => by
    simpa using hz.2
  have hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} := fun z hz =>
    (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt
  have hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M := by
    intro z hz0 hzρ
    by_cases hzl : ‖z‖ < ρ
    · simp only [Φ, if_pos hzl]
      exact hPbd z hzl
    · simp only [Φ, if_neg hzl]
      exact hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)
  have hA := le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ
    (hfS.sub (hΦcont.mono hS))
    (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hA' := le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ
    ((hΦcont.mono hS).sub hfS)
    (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by simp only [Φ, if_pos hwρ]
  have hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by linarith
  rw [hfw]
  have hint := GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ
  exact hint

end GlobalTheory.CompanionTheory.Ar.PuncturedDisc
