import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

noncomputable section

namespace GlobalTheory.LogExt

open Filter Topology Asymptotics Metric Set Complex
open scoped Real

/- English proof (translation)
Take `⟨m, h, hh, hh0, hgh⟩` from `hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne`. Establish `hT : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝[≠] c) (𝓝[>] 0)` using `tendsto_norm_sub_self_nhdsNE c`. Establish `hlog : Tendsto (fun z : ℂ => |Real.log ‖z - c‖|) (𝓝[≠] c) atTop` using `tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hT)`. Establish `hhc : ContinuousAt (fun z => |Real.log ‖h z‖|) c` using `(hh.continuousAt.norm.log (norm_ne_zero_iff.mpr hh0)).abs`. Establish `hhb : ∀ᶠ z in 𝓝 c, |Real.log ‖h z‖| < |Real.log ‖h c‖| + 1` using `hhc.eventually (gt_mem_nhds (lt_add_one _))`.

Establish `hhne : ∀ᶠ z in 𝓝 c, h z ≠ 0` using `hh.continuousAt.eventually_ne hh0`. Establish `h1 : f =O[𝓝[≠] c] fun z => |Real.log ‖z - c‖| ^ k`. Use `IsBigO.of_bound (|C| * (1 + m) ^ k) ?_` and prove the remaining obligations. Use `filter_upwards [nhdsWithin_le_nhds hb, nhdsWithin_le_nhds hgh, nhdsWithin_le_nhds hhb, nhdsWithin_le_nhds hhne, self_mem_nhdsWithin, hlog.eventually (eventually_ge_atTop (|Real.log ‖h c‖| + 2))] with z hz1 hz2 hz3 hz4 hz5 hz6`. Establish `hzc : z - c ≠ 0` using `sub_ne_zero.mpr hz5`.

Establish `hgz : g z ≠ 0`. Rewrite using `[hz2]`. Conclude with `smul_ne_zero (pow_ne_zero _ hzc) hz4`. Establish `hl : Real.log ‖g z‖ = m * Real.log ‖z - c‖ + Real.log ‖h z‖`. Rewrite using `[hz2, smul_eq_mul, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hzc)) (norm_ne_zero_iff.mpr hz4), Real.log_pow]`.

Establish `hle : 1 + |Real.log ‖g z‖| ≤ (1 + m) * |Real.log ‖z - c‖|`. Rewrite using `[hl]`. Use `abs_add_le (m * Real.log ‖z - c‖) (Real.log ‖h z‖)` as an intermediate fact. Rewrite `this` using `[abs_mul, Nat.abs_cast]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, Real.norm_eq_abs, abs_pow, abs_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (fun z : ℂ => |Real.log ‖z - c‖| ^ k) =o[𝓝[≠] c] fun z => (z - c)⁻¹`. Use `(isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) (s := -1) (by norm_num)).comp_tendsto hT` as an intermediate fact.

Use `IsLittleO.of_norm_right ?_` and prove the remaining obligations. Use `this.congr (fun z => ?_) (fun z => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[Real.rpow_neg_one]`. Establish `h3 : (fun _ : ℂ => f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹`.

Use `isLittleO_const_left.mpr (Or.inr ?_)` and prove the remaining obligations. Use `tendsto_inv_nhdsGT_zero.comp hT` as an intermediate fact. Use `this.congr fun z => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `(h1.trans_isLittleO h2).sub h3`.
-/
theorem isLittleO_inv_of_log_growth {f g : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c)
    (hne : ¬ ∀ᶠ z in 𝓝 c, g z = 0) {C : ℝ} {k : ℕ}
    (hb : ∀ᶠ z in 𝓝 c, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
  obtain ⟨m, h, hh, hh0, hgh⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hT : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝[≠] c) (𝓝[>] 0) := tendsto_norm_sub_self_nhdsNE c
  have hlog : Tendsto (fun z : ℂ => |Real.log ‖z - c‖|) (𝓝[≠] c) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hT)
  have hhc : ContinuousAt (fun z => |Real.log ‖h z‖|) c :=
    (hh.continuousAt.norm.log (norm_ne_zero_iff.mpr hh0)).abs
  have hhb : ∀ᶠ z in 𝓝 c, |Real.log ‖h z‖| < |Real.log ‖h c‖| + 1 :=
    hhc.eventually (gt_mem_nhds (lt_add_one _))
  have hhne : ∀ᶠ z in 𝓝 c, h z ≠ 0 := hh.continuousAt.eventually_ne hh0
  have h1 : f =O[𝓝[≠] c] fun z => |Real.log ‖z - c‖| ^ k := by
    refine IsBigO.of_bound (|C| * (1 + m) ^ k) ?_
    filter_upwards [nhdsWithin_le_nhds hb, nhdsWithin_le_nhds hgh, nhdsWithin_le_nhds hhb,
      nhdsWithin_le_nhds hhne, self_mem_nhdsWithin,
      hlog.eventually (eventually_ge_atTop (|Real.log ‖h c‖| + 2))] with z hz1 hz2 hz3 hz4 hz5 hz6
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz5
    have hgz : g z ≠ 0 := by
      rw [hz2]; exact smul_ne_zero (pow_ne_zero _ hzc) hz4
    have hl : Real.log ‖g z‖ = m * Real.log ‖z - c‖ + Real.log ‖h z‖ := by
      rw [hz2, smul_eq_mul, norm_mul, norm_pow,
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hzc)) (norm_ne_zero_iff.mpr hz4),
        Real.log_pow]
    have hle : 1 + |Real.log ‖g z‖| ≤ (1 + m) * |Real.log ‖z - c‖| := by
      rw [hl]
      have := abs_add_le (m * Real.log ‖z - c‖) (Real.log ‖h z‖)
      rw [abs_mul, Nat.abs_cast] at this
      nlinarith
    calc ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k := hz1 hgz
      _ ≤ |C| * (1 + |Real.log ‖g z‖|) ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + m) * |Real.log ‖z - c‖|) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle k) (abs_nonneg C)
      _ = |C| * (1 + m) ^ k * ‖|Real.log ‖z - c‖| ^ k‖ := by
          rw [mul_pow, Real.norm_eq_abs, abs_pow, abs_abs]; ring
  have h2 : (fun z : ℂ => |Real.log ‖z - c‖| ^ k) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) (s := -1) (by norm_num)).comp_tendsto hT
    refine IsLittleO.of_norm_right ?_
    refine this.congr (fun z => ?_) (fun z => ?_)
    · simp
    · simp [Real.rpow_neg_one]
  have h3 : (fun _ : ℂ => f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
    refine isLittleO_const_left.mpr (Or.inr ?_)
    have := tendsto_inv_nhdsGT_zero.comp hT
    refine this.congr fun z => ?_
    simp
  exact (h1.trans_isLittleO h2).sub h3

/- English proof (translation)
Use `set F : ℂ → ℂ := fun t => if g t = 0 then limUnder (𝓝[≠] t) f else f t with hF`. Establish `hFf : ∀ t, g t ≠ 0 → F t = f t` using `fun t ht => by simp [hF, ht]`. Establish `hd : DifferentiableOn ℂ F (closedBall 0 R)`. Introduce `t ht`. Use `DifferentiableAt.differentiableWithinAt ?_` and prove the remaining obligations.

Distinguish the cases in `hgt : g t = 0`. Establish `hne : ¬ ∀ᶠ z in 𝓝 t, g z = 0` using `fun h => hg0 (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall (0 : ℂ) R).isPreconnected ht h (mem_closedBall_self hR.le))`. Establish `hev : ∀ᶠ z in 𝓝[≠] t, g z ≠ 0` using `(hg t ht).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne`. Rewrite `hev` using `[eventually_nhdsWithin_iff]`. Take `⟨C, k, hCk⟩` from `hb t ht`.

Establish `hs` using `hev.and (hf t ht)`. Establish `hD` using `Complex.differentiableOn_update_limUnder_of_isLittleO (f := f) hs (fun z hz => (hz.1.2 (hz.1.1 hz.2)).differentiableWithinAt) (isLittleO_inv_of_log_growth (hg t ht) hne hCk)`. Use `(hD.differentiableAt hs).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with z hz`. Distinguish the cases in `hzt : z = t`.

Substitute `hzt` using the available equality. Simplify using `[hF, hgt]`. Rewrite using `[Function.update_of_ne hzt, hFf z (hz hzt)]`. Use `((hf t ht).self_of_nhds hgt).congr_of_eventuallyEq ?_ filter_upwards [(hg t ht).continuousAt.eventually_ne hgt] with z hz using hFf z hz` and prove the remaining obligations. Establish `h` using `hd.circleIntegral_sub_inv_smul (mem_ball_self hR)`.

Rewrite `h` using `[hFf 0 hg0]`. Rewrite using `[← h]`. Use `circleIntegral.integral_congr hR.le fun t ht => ?_` and prove the remaining obligations. Simplify using `[hFf t (hgs t ht)]`.
-/
theorem cauchy_of_log_growth {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hg0 : g 0 ≠ 0) (hgs : ∀ t ∈ sphere (0 : ℂ) R, g t ≠ 0)
    (hf : ∀ t ∈ closedBall (0 : ℂ) R, ∀ᶠ z in 𝓝 t, g z ≠ 0 → DifferentiableAt ℂ f z)
    (hb : ∀ t ∈ closedBall (0 : ℂ) R, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ z in 𝓝 t, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (∮ t in C(0, R), t⁻¹ • f t) = (2 * π * I : ℂ) • f 0 := by
  classical
  set F : ℂ → ℂ := fun t => if g t = 0 then limUnder (𝓝[≠] t) f else f t with hF
  have hFf : ∀ t, g t ≠ 0 → F t = f t := fun t ht => by simp [hF, ht]
  have hd : DifferentiableOn ℂ F (closedBall 0 R) := by
    intro t ht
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hgt : g t = 0
    · have hne : ¬ ∀ᶠ z in 𝓝 t, g z = 0 := fun h =>
        hg0 (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_closedBall (0 : ℂ) R).isPreconnected ht h (mem_closedBall_self hR.le))
      have hev : ∀ᶠ z in 𝓝[≠] t, g z ≠ 0 :=
        (hg t ht).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨C, k, hCk⟩ := hb t ht
      have hs := hev.and (hf t ht)
      have hD := Complex.differentiableOn_update_limUnder_of_isLittleO (f := f) hs
        (fun z hz => (hz.1.2 (hz.1.1 hz.2)).differentiableWithinAt)
        (isLittleO_inv_of_log_growth (hg t ht) hne hCk)
      refine (hD.differentiableAt hs).congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      by_cases hzt : z = t
      · subst hzt; simp [hF, hgt]
      · rw [Function.update_of_ne hzt, hFf z (hz hzt)]
    · refine ((hf t ht).self_of_nhds hgt).congr_of_eventuallyEq ?_
      filter_upwards [(hg t ht).continuousAt.eventually_ne hgt] with z hz using hFf z hz
  have h := hd.circleIntegral_sub_inv_smul (mem_ball_self hR)
  rw [hFf 0 hg0] at h
  rw [← h]
  refine circleIntegral.integral_congr hR.le fun t ht => ?_
  simp [hFf t (hgs t ht)]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hf`.
-/
theorem _root_.GlobalTheory.LogExt.analyticOnNhd_of_differentiableOn [FiniteDimensional ℂ V] {U : Set V}
    {f : V → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U :=
  _root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hf

/- English proof (translation)
Establish `hcf : ContinuousOn (fun t : ℂ => fderiv ℂ u (b₀ + t • v)) (sphere 0 R)` using `hu.fderiv.continuousOn.comp (by fun_prop) hs`. Take `⟨M, hM⟩` from `(isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcf`. Establish `hev : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R, AnalyticAt ℂ u (b + t • v) ∧ ‖fderiv ℂ u (b + t • v)‖ < M + 1`. Use `(isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht => ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t)` using `by fun_prop`.

Establish `ha` using `hu _ (hs t ht)`. Establish `h1 : ∀ᶠ x in 𝓝 (b₀ + t • v), ‖fderiv ℂ u x‖ < M + 1` using `ha.fderiv.continuousAt.norm.eventually (gt_mem_nhds (lt_add_of_le_of_pos (hM t ht) one_pos))`. Conclude with `hc.eventually (ha.eventually_analyticAt.and h1)`. Establish `hm : ∀ θ : ℝ, circleMap 0 R θ ∈ sphere (0 : ℂ) R` using `fun θ => circleMap_mem_sphere 0 hR.le θ`. Establish `hw : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹`.

Simplify using `only [deriv_circleMap]`. Conclude with `((continuous_circleMap 0 R).mul continuous_const).mul ((continuous_circleMap 0 R).inv₀ fun θ => circleMap_ne_center hR.ne')`. Establish `hwn : ∀ θ : ℝ, ‖deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹‖ = 1` using `fun θ => by`. Simplify using `[deriv_circleMap, abs_of_pos hR, hR.ne']`. Establish `hcont : ∀ b, (∀ t ∈ sphere (0 : ℂ) R, AnalyticAt ℂ u (b + t • v)) → Continuous fun θ : ℝ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) • u (b + circleMap 0 R θ • v)` using `fun b hb => by`.

Use `hw.smul (continuous_iff_continuousAt.mpr fun θ => ?_)` and prove the remaining obligations. Conclude with `ContinuousAt.comp (f := fun θ : ℝ => b + circleMap 0 R θ • v) (hb _ (hm θ)).continuousAt (by fun_prop)`. Establish `key` using `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := MeasureTheory.volume) (a := 0) (b := 2 * π) (bound := fun _ => M + 1) (F := fun b θ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) • u (b + circleMap 0 R θ • v)) (F' := fun b θ => (deriv (circleMap …`. Rewrite using `[norm_smul, hwn, one_mul]`. Conclude with `(hb _ (hm θ)).2.le)`.

Use `intervalIntegrable_const`. Use the proof step `(Eventually.of_forall fun θ _ b hb => by`. Establish `h1` using `(hb _ (hm θ)).1.differentiableAt.hasFDerivAt`. Conclude with `((hasFDerivAt_comp_add_right _).mpr h1).fun_const_smul _)`. Use `key.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun b => ?_)` and prove the remaining obligations.

Simplify using `only [circleIntegral, smul_eq_mul, mul_assoc]`.
-/
theorem differentiableAt_lineIntegral {Ω : Set V} {u : V → ℂ}
    (hu : AnalyticOnNhd ℂ u Ω) {b₀ v : V} {R : ℝ} (hR : 0 < R)
    (hs : ∀ t ∈ sphere (0 : ℂ) R, b₀ + t • v ∈ Ω) :
    DifferentiableAt ℂ (fun b => ∮ t in C(0, R), t⁻¹ • u (b + t • v)) b₀ := by
  have hcf : ContinuousOn (fun t : ℂ => fderiv ℂ u (b₀ + t • v)) (sphere 0 R) :=
    hu.fderiv.continuousOn.comp (by fun_prop) hs
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcf
  have hev : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R,
      AnalyticAt ℂ u (b + t • v) ∧ ‖fderiv ℂ u (b + t • v)‖ < M + 1 := by
    refine (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht => ?_
    have hc : ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t) := by fun_prop
    have ha := hu _ (hs t ht)
    have h1 : ∀ᶠ x in 𝓝 (b₀ + t • v), ‖fderiv ℂ u x‖ < M + 1 :=
      ha.fderiv.continuousAt.norm.eventually (gt_mem_nhds (lt_add_of_le_of_pos (hM t ht) one_pos))
    exact hc.eventually (ha.eventually_analyticAt.and h1)
  have hm : ∀ θ : ℝ, circleMap 0 R θ ∈ sphere (0 : ℂ) R := fun θ => circleMap_mem_sphere 0 hR.le θ
  have hw : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹ := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).mul
      ((continuous_circleMap 0 R).inv₀ fun θ => circleMap_ne_center hR.ne')
  have hwn : ∀ θ : ℝ, ‖deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹‖ = 1 := fun θ => by
    simp [deriv_circleMap, abs_of_pos hR, hR.ne']
  have hcont : ∀ b, (∀ t ∈ sphere (0 : ℂ) R, AnalyticAt ℂ u (b + t • v)) →
      Continuous fun θ : ℝ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) •
        u (b + circleMap 0 R θ • v) := fun b hb => by
    refine hw.smul (continuous_iff_continuousAt.mpr fun θ => ?_)
    exact ContinuousAt.comp (f := fun θ : ℝ => b + circleMap 0 R θ • v)
      (hb _ (hm θ)).continuousAt (by fun_prop)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π) (bound := fun _ => M + 1)
    (F := fun b θ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) • u (b + circleMap 0 R θ • v))
    (F' := fun b θ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) •
      fderiv ℂ u (b + circleMap 0 R θ • v)) hev
    (hev.mono fun b hb => (hcont b fun t ht => (hb t ht).1).aestronglyMeasurable)
    ((hcont b₀ fun t ht => hu _ (hs t ht)).intervalIntegrable _ _)
    ((hw.smul (hcf.comp_continuous (continuous_circleMap 0 R) hm)).aestronglyMeasurable)
    (Eventually.of_forall fun θ _ b hb => by
      rw [norm_smul, hwn, one_mul]; exact (hb _ (hm θ)).2.le)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ b hb => by
      have h1 := (hb _ (hm θ)).1.differentiableAt.hasFDerivAt
      exact ((hasFDerivAt_comp_add_right _).mpr h1).fun_const_smul _)
  refine key.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun b => ?_)
  simp only [circleIntegral, smul_eq_mul, mul_assoc]

/- English proof (translation)
Establish `hΩ : IsOpen {b ∈ U | φ b ≠ 0}` using `hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton`. Establish `hφa` using `analyticOnNhd_of_differentiableOn hU hφ`. Establish `hua` using `analyticOnNhd_of_differentiableOn hΩ hu`. Establish `hline : ∀ (b v : V) (t : ℂ), AnalyticAt ℂ (fun s : ℂ => b + s • v) t` using `fun b v t => analyticAt_const.add (analyticAt_id.smul analyticAt_const)`. Establish `hgan : ∀ (b v : V) (t : ℂ), b + t • v ∈ U → AnalyticAt ℂ (fun s : ℂ => φ (b + s • v)) t` using `fun b v t h => AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hφa _ h) (hline b v t)`.

Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.mp hU b₀ hb₀`. Take `⟨b₁, hb₁, hb₁r⟩` from `Metric.mem_closure_iff.mp (hd hb₀) r hr`. Use `set v := b₁ - b₀ with hv`. Establish `hvr : ‖v‖ < r` using `by rwa [dist_comm, dist_eq_norm] at hb₁r`. Establish `hin : ∀ t ∈ closedBall (0 : ℂ) 1, b₀ + t • v ∈ U` using `fun t ht => by`.

Use `hrU ?_` and prove the remaining obligations. Rewrite `ht` using `[mem_closedBall_zero_iff]`. Rewrite using `[mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) ht).trans_lt hvr`. Establish `hg : AnalyticOnNhd ℂ (fun s : ℂ => φ (b₀ + s • v)) (closedBall 0 1)` using `fun t ht => hgan _ _ _ (hin t ht)`.

Establish `hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), φ (b₀ + z • v) = 0` using `fun h => by`. Use `hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall (0 : ℂ) 1).isPreconnected (mem_closedBall_self zero_le_one) h (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)` as an intermediate fact. Conclude with `hb₁.2 (by simpa [hv] using this)`. Establish `hev` using `(hg 0 (mem_closedBall_self zero_le_one)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne`. Rewrite `hev` using `[eventually_nhdsWithin_iff]`.

Take `⟨ε, hε, hεs⟩` from `Metric.nhds_basis_closedBall.mem_iff.mp hev`. Use `set R := min ε 1 with hR`. Establish `hR0 : 0 < R` using `lt_min hε one_pos`. Establish `hc : ∀ t : ℂ, ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t)` using `fun t => by fun_prop`. Establish `h1 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ closedBall (0 : ℂ) R, b + t • v ∈ U` using `(isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht => (hc t).eventually (hU.mem_nhds (hin t (closedBall_subset_closedBall (min_le_right _ _) ht)))`.

Establish `h2 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R, b + t • v ∈ {b ∈ U | φ b ≠ 0}` using `(isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht => (hc t).eventually (hΩ.mem_nhds ⟨hin t (closedBall_subset_closedBall (min_le_right _ _) (sphere_subset_closedBall ht)), hεs (closedBall_subset_closedBall (min_le_left _ _) (sphere_subset_closedBall ht) …`. Use `⟨fun b => (2 * π * I : ℂ)⁻¹ • ∮ t in C(0, R), t⁻¹ • u (b + t • v), ?_⟩` and prove the remaining obligations. Use `filter_upwards [h1, h2] with b hb1 hb2`. Use `⟨(differentiableAt_lineIntegral hua hR0 hb2).fun_const_smul _, fun hφb => ?_⟩` and prove the remaining obligations. Use `cauchy_of_log_growth (f := fun s : ℂ => u (b + s • v)) (g := fun s : ℂ => φ (b + s • v)) hR0 (fun t ht => hgan _ _ _ (hb1 t ht)) (by simpa using hφb) (fun t ht => (hb2 t ht).2) (fun t ht => by filter_upwards [(hline b v t).continuousAt.eventually (hU.mem_nhds (hb1 t ht))] with z …` as an intermediate fact.

Conclude with `(AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hua _ ⟨hz, hz0⟩) (hline b v z)).differentiableAt)`. Use the proof step `(fun t ht => by`. Take `⟨C, k, h⟩` from `hb _ (hb1 t ht)`. Conclude with `⟨C, k, (hline b v t).continuousAt.eventually h⟩)`. Simplify using `only [this, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul, zero_smul, add_zero]`.
-/
theorem exists_local_extension [FiniteDimensional ℂ V] {U : Set V} {φ u : V → ℂ} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) {b₀ : V} (hb₀ : b₀ ∈ U) :
    ∃ w : V → ℂ, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ w b ∧ (φ b ≠ 0 → w b = u b) := by
  have hΩ : IsOpen {b ∈ U | φ b ≠ 0} :=
    hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hφa := analyticOnNhd_of_differentiableOn hU hφ
  have hua := analyticOnNhd_of_differentiableOn hΩ hu
  have hline : ∀ (b v : V) (t : ℂ), AnalyticAt ℂ (fun s : ℂ => b + s • v) t := fun b v t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hgan : ∀ (b v : V) (t : ℂ), b + t • v ∈ U → AnalyticAt ℂ (fun s : ℂ => φ (b + s • v)) t :=
    fun b v t h => AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hφa _ h) (hline b v t)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU b₀ hb₀
  obtain ⟨b₁, hb₁, hb₁r⟩ := Metric.mem_closure_iff.mp (hd hb₀) r hr
  set v := b₁ - b₀ with hv
  have hvr : ‖v‖ < r := by rwa [dist_comm, dist_eq_norm] at hb₁r
  have hin : ∀ t ∈ closedBall (0 : ℂ) 1, b₀ + t • v ∈ U := fun t ht => by
    refine hrU ?_
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans_lt hvr
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => φ (b₀ + s • v)) (closedBall 0 1) :=
    fun t ht => hgan _ _ _ (hin t ht)
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), φ (b₀ + z • v) = 0 := fun h => by
    have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) 1).isPreconnected (mem_closedBall_self zero_le_one) h
      (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)
    exact hb₁.2 (by simpa [hv] using this)
  have hev := (hg 0 (mem_closedBall_self zero_le_one)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hev
  set R := min ε 1 with hR
  have hR0 : 0 < R := lt_min hε one_pos
  have hc : ∀ t : ℂ, ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t) := fun t => by fun_prop
  have h1 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ closedBall (0 : ℂ) R, b + t • v ∈ U :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht =>
      (hc t).eventually (hU.mem_nhds (hin t (closedBall_subset_closedBall (min_le_right _ _) ht)))
  have h2 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R, b + t • v ∈ {b ∈ U | φ b ≠ 0} :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht =>
      (hc t).eventually (hΩ.mem_nhds ⟨hin t (closedBall_subset_closedBall (min_le_right _ _)
        (sphere_subset_closedBall ht)), hεs (closedBall_subset_closedBall (min_le_left _ _)
        (sphere_subset_closedBall ht)) (ne_of_mem_sphere ht hR0.ne')⟩)
  refine ⟨fun b => (2 * π * I : ℂ)⁻¹ • ∮ t in C(0, R), t⁻¹ • u (b + t • v), ?_⟩
  filter_upwards [h1, h2] with b hb1 hb2
  refine ⟨(differentiableAt_lineIntegral hua hR0 hb2).fun_const_smul _, fun hφb => ?_⟩
  have := cauchy_of_log_growth (f := fun s : ℂ => u (b + s • v)) (g := fun s : ℂ => φ (b + s • v)) hR0
    (fun t ht => hgan _ _ _ (hb1 t ht)) (by simpa using hφb) (fun t ht => (hb2 t ht).2)
    (fun t ht => by
      filter_upwards [(hline b v t).continuousAt.eventually (hU.mem_nhds (hb1 t ht))] with z hz hz0
      exact (AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hua _ ⟨hz, hz0⟩)
        (hline b v z)).differentiableAt)
    (fun t ht => by
      obtain ⟨C, k, h⟩ := hb _ (hb1 t ht)
      exact ⟨C, k, (hline b v t).continuousAt.eventually h⟩)
  simp only [this, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul, zero_smul, add_zero]

open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
/- English proof (translation)
Establish `key : ∀ b ∈ U, ∀ N ∈ 𝓝 b, ∀ G : V → ℂ, DifferentiableOn ℂ G N → EqOn G u (N ∩ S) → limUnder (𝓝[S] b) u = G b`. Introduce `b hbU N hN G hG hGu`. Use `haveI : (𝓝[S] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd hbU)`. Apply `Tendsto.limUnder_eq` to reduce the goal to its premises. Establish `hc : ContinuousAt G b` using `(hG.differentiableAt hN).continuousAt`.

Use `(hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_` and prove the remaining obligations. Use `filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with x hxN hxS`. Conclude with `hGu ⟨hxN, hxS⟩`. Use `⟨fun b => limUnder (𝓝[S] b) u, ?_, ?_⟩` and prove the remaining obligations. Introduce `b₀ hb₀`.

Take `⟨N, hN, G, hG, hGu⟩` from `hloc b₀ hb₀`. Establish `h : (fun b => limUnder (𝓝[S] b) u) =ᶠ[𝓝 b₀] G` using `by filter_upwards [hU.mem_nhds hb₀, eventually_mem_nhds_iff.mpr hN] with b hbU hbN`. Conclude with `key b hbU N hbN G hG hGu`. Conclude with `((hG.differentiableAt hN).congr_of_eventuallyEq h).differentiableWithinAt`. Introduce `b hb`.

Take `⟨N, hN, G, hG, hGu⟩` from `hloc b (hS hb)`. Use `show limUnder (𝓝[S] b) u = u b`. Rewrite using `[key b (hS hb) N hN G hG hGu]`. Conclude with `hGu ⟨mem_of_mem_nhds hN, hb⟩`.
-/
private theorem exists_differentiableOn_of_locally_extends {U S : Set V} (hU : IsOpen U) (hS : S ⊆ U)
    (hd : U ⊆ closure S) (u : V → ℂ)
    (hloc : ∀ b₀ ∈ U, ∃ N ∈ 𝓝 b₀, ∃ G : V → ℂ, DifferentiableOn ℂ G N ∧ EqOn G u (N ∩ S)) :
    ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ EqOn u' u S := by
  have key : ∀ b ∈ U, ∀ N ∈ 𝓝 b, ∀ G : V → ℂ, DifferentiableOn ℂ G N → EqOn G u (N ∩ S) →
      limUnder (𝓝[S] b) u = G b := by
    intro b hbU N hN G hG hGu
    haveI : (𝓝[S] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd hbU)
    apply Tendsto.limUnder_eq
    have hc : ContinuousAt G b := (hG.differentiableAt hN).continuousAt
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with x hxN hxS
    exact hGu ⟨hxN, hxS⟩
  refine ⟨fun b => limUnder (𝓝[S] b) u, ?_, ?_⟩
  · intro b₀ hb₀
    obtain ⟨N, hN, G, hG, hGu⟩ := hloc b₀ hb₀
    have h : (fun b => limUnder (𝓝[S] b) u) =ᶠ[𝓝 b₀] G := by
      filter_upwards [hU.mem_nhds hb₀, eventually_mem_nhds_iff.mpr hN] with b hbU hbN
      exact key b hbU N hbN G hG hGu
    exact ((hG.differentiableAt hN).congr_of_eventuallyEq h).differentiableWithinAt
  · intro b hb
    obtain ⟨N, hN, G, hG, hGu⟩ := hloc b (hS hb)
    show limUnder (𝓝[S] b) u = u b
    rw [key b (hS hb) N hN G hG hGu]
    exact hGu ⟨mem_of_mem_nhds hN, hb⟩

open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
/- English proof (translation)
Establish `hnz : ¬ ∀ᶠ z in 𝓝 s₀, ψ z = 0`. Introduce `h0`. Establish `h0' : ∀ᶠ z in 𝓝[≠] s₀, ψ z = 0` using `nhdsWithin_le_nhds h0`. Take `⟨s, hs1, hs2⟩` from `(h0'.and hne).exists`. Conclude with `hs2 hs1`.

Take `⟨n, g, hg, hg0, hfg⟩` from `hψ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz`. Use `set A := |Real.log ‖g s₀‖| + 1 with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hglog : ∀ᶠ s in 𝓝 s₀, |Real.log ‖g s‖| ≤ A` using `((hg.continuousAt.norm.log (norm_ne_zero_iff.mpr hg0)).abs).eventually (ge_mem_nhds (lt_add_one _))`. Establish `hdist : Tendsto (fun s => ‖s - s₀‖) (𝓝 s₀) (𝓝 0)`.

Simplify using `using ((continuous_id.sub continuous_const).norm.tendsto s₀ : Tendsto (fun s : ℂ => ‖s - s₀‖) (𝓝 s₀) (𝓝 ‖s₀ - s₀‖))`. Establish `hsmall : ∀ᶠ s in 𝓝 s₀, ‖s - s₀‖ < Real.exp (-1)` using `hdist.eventually (gt_mem_nhds (Real.exp_pos _))`. Establish `hbound : ∀ᶠ s in 𝓝[≠] s₀, ‖h s * (s - s₀)‖ ≤ |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖)` using `by filter_upwards [nhdsWithin_le_nhds (hb.and (hfg.and (hglog.and hsmall))), hne, self_mem_nhdsWithin] with s ⟨hbs, hfs, hgs, hxs⟩ hψs hss`. Establish `hx : 0 < ‖s - s₀‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hss)`. Establish `hgs0 : g s ≠ 0`.

Introduce `h0`. Apply `hψs` to reduce the goal to its premises. Rewrite using `[hfs, h0, smul_zero]`. Establish `hlogx : 1 ≤ |Real.log ‖s - s₀‖|`. Establish `: Real.log ‖s - s₀‖ < -1` using `(Real.log_lt_iff_lt_exp hx).mpr hxs`.

Rewrite using `[abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogψ : |Real.log ‖ψ s‖| ≤ n * |Real.log ‖s - s₀‖| + A`. Rewrite using `[hfs, norm_smul, norm_pow, Real.log_mul (pow_ne_zero _ hx.ne') (norm_ne_zero_iff.mpr hgs0), Real.log_pow]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_mul, Nat.abs_cast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `h1 : 1 + |Real.log ‖ψ s‖| ≤ (1 + A + n) * |Real.log ‖s - s₀‖|` using `by nlinarith`. Establish `h2 : ‖h s‖ ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hreal : Tendsto (fun x : ℝ => |Real.log x| ^ k * x) (𝓝[>] 0) (𝓝 0)`. Establish `h1` using `(Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero`. Establish `h2` using `(h1.comp tendsto_inv_nhdsGT_zero).norm`. Rewrite `h2` using `[norm_zero]`. Use `h2.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Establish `hx0 : (0 : ℝ) < x` using `hx`. Simplify using `[Real.log_inv, abs_pow, abs_of_pos hx0, div_inv_eq_mul]`. Establish `hx : Tendsto (fun s => ‖s - s₀‖) (𝓝[≠] s₀) (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.mpr ⟨hdist.mono_left nhdsWithin_le_nhds, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with s hs using norm_pos_iff.mpr (sub_ne_zero.mpr hs)`. Establish `hlim : Tendsto (fun s => |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖)) (𝓝[≠] s₀) (𝓝 0)`. Simplify using `using (hreal.comp hx).const_mul (|C| * (1 + A + n) ^ k)`. Establish `hmain : Tendsto (fun s => h s * (s - s₀)) (𝓝[≠] s₀) (𝓝 0)` using `squeeze_zero_norm' hbound hlim`. Establish `hlin : Tendsto (fun s => h s₀ * (s - s₀)) (𝓝[≠] s₀) (𝓝 0)`.

Establish `: Tendsto (fun s => h s₀ * (s - s₀)) (𝓝 s₀) (𝓝 (h s₀ * (s₀ - s₀)))` using `(continuous_const.mul (continuous_id.sub continuous_const)).tendsto s₀`. Simplify using `using this.mono_left nhdsWithin_le_nhds`. Rewrite using `[isLittleO_iff_tendsto']`. Use `hmain.sub hlin` as an intermediate fact. Rewrite `this` using `[sub_zero]`.

Use `this.congr' (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `[div_inv_eq_mul, sub_mul]`. Use `filter_upwards [self_mem_nhdsWithin] with s hs h0`. Conclude with `absurd h0 (inv_ne_zero (sub_ne_zero.mpr hs))`.
-/
private theorem isLittleO_sub_inv_sub_of_log_bound {ψ h : ℂ → ℂ} {s₀ : ℂ} (hψ : AnalyticAt ℂ ψ s₀)
    (hz : ψ s₀ = 0) (hne : ∀ᶠ s in 𝓝[≠] s₀, ψ s ≠ 0) {C : ℝ} {k : ℕ}
    (hb : ∀ᶠ s in 𝓝 s₀, ψ s ≠ 0 → ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k) :
    (fun s => h s - h s₀) =o[𝓝[≠] s₀] fun s => (s - s₀)⁻¹ := by
  have hnz : ¬ ∀ᶠ z in 𝓝 s₀, ψ z = 0 := by
    intro h0
    have h0' : ∀ᶠ z in 𝓝[≠] s₀, ψ z = 0 := nhdsWithin_le_nhds h0
    obtain ⟨s, hs1, hs2⟩ := (h0'.and hne).exists
    exact hs2 hs1
  obtain ⟨n, g, hg, hg0, hfg⟩ := hψ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  set A := |Real.log ‖g s₀‖| + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hglog : ∀ᶠ s in 𝓝 s₀, |Real.log ‖g s‖| ≤ A :=
    ((hg.continuousAt.norm.log (norm_ne_zero_iff.mpr hg0)).abs).eventually
      (ge_mem_nhds (lt_add_one _))
  have hdist : Tendsto (fun s => ‖s - s₀‖) (𝓝 s₀) (𝓝 0) := by
    simpa using ((continuous_id.sub continuous_const).norm.tendsto s₀ : Tendsto
      (fun s : ℂ => ‖s - s₀‖) (𝓝 s₀) (𝓝 ‖s₀ - s₀‖))
  have hsmall : ∀ᶠ s in 𝓝 s₀, ‖s - s₀‖ < Real.exp (-1) :=
    hdist.eventually (gt_mem_nhds (Real.exp_pos _))
  have hbound : ∀ᶠ s in 𝓝[≠] s₀, ‖h s * (s - s₀)‖ ≤
      |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖) := by
    filter_upwards [nhdsWithin_le_nhds (hb.and (hfg.and (hglog.and hsmall))), hne,
      self_mem_nhdsWithin] with s ⟨hbs, hfs, hgs, hxs⟩ hψs hss
    have hx : 0 < ‖s - s₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hss)
    have hgs0 : g s ≠ 0 := by
      intro h0
      apply hψs
      rw [hfs, h0, smul_zero]
    have hlogx : 1 ≤ |Real.log ‖s - s₀‖| := by
      have : Real.log ‖s - s₀‖ < -1 := (Real.log_lt_iff_lt_exp hx).mpr hxs
      rw [abs_of_neg (by linarith)]
      linarith
    have hlogψ : |Real.log ‖ψ s‖| ≤ n * |Real.log ‖s - s₀‖| + A := by
      rw [hfs, norm_smul, norm_pow, Real.log_mul (pow_ne_zero _ hx.ne')
        (norm_ne_zero_iff.mpr hgs0), Real.log_pow]
      calc |n * Real.log ‖s - s₀‖ + Real.log ‖g s‖|
          ≤ |n * Real.log ‖s - s₀‖| + |Real.log ‖g s‖| := abs_add_le _ _
        _ ≤ n * |Real.log ‖s - s₀‖| + A := by
          rw [abs_mul, Nat.abs_cast]
          linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 + |Real.log ‖ψ s‖| ≤ (1 + A + n) * |Real.log ‖s - s₀‖| := by nlinarith
    have h2 : ‖h s‖ ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k := by
      calc ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k := hbs hψs
        _ ≤ |C| * (1 + |Real.log ‖ψ s‖|) ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k := by gcongr
    rw [norm_mul]
    calc ‖h s‖ * ‖s - s₀‖
        ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k * ‖s - s₀‖ := by gcongr
      _ = |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖) := by
        rw [mul_pow]
        ring
  have hreal : Tendsto (fun x : ℝ => |Real.log x| ^ k * x) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero
    have h2 := (h1.comp tendsto_inv_nhdsGT_zero).norm
    rw [norm_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    simp [Real.log_inv, abs_pow, abs_of_pos hx0, div_inv_eq_mul]
  have hx : Tendsto (fun s => ‖s - s₀‖) (𝓝[≠] s₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hdist.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs using norm_pos_iff.mpr (sub_ne_zero.mpr hs)
  have hlim : Tendsto (fun s => |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖))
      (𝓝[≠] s₀) (𝓝 0) := by
    simpa using (hreal.comp hx).const_mul (|C| * (1 + A + n) ^ k)
  have hmain : Tendsto (fun s => h s * (s - s₀)) (𝓝[≠] s₀) (𝓝 0) := squeeze_zero_norm' hbound hlim
  have hlin : Tendsto (fun s => h s₀ * (s - s₀)) (𝓝[≠] s₀) (𝓝 0) := by
    have : Tendsto (fun s => h s₀ * (s - s₀)) (𝓝 s₀) (𝓝 (h s₀ * (s₀ - s₀))) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).tendsto s₀
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [isLittleO_iff_tendsto']
  · have := hmain.sub hlin
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun s => ?_)
    simp [div_inv_eq_mul, sub_mul]
  · filter_upwards [self_mem_nhdsWithin] with s hs h0
    exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hs))

open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
/- English proof (translation)
Establish `han : AnalyticOnNhd ℂ ψ (ball 0 ρ)` using `hψ.analyticOnNhd isOpen_ball`. Establish `hiso : ∀ s₀ ∈ ball (0 : ℂ) ρ, ∀ᶠ s in 𝓝[≠] s₀, ψ s ≠ 0`. Introduce `s₀ hs₀`. Break down `(han s₀ hs₀).eventually_eq_zero_or_eventually_ne_zero with hz | hz` into its components or cases. It suffices to derive a contradiction.

Use `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected hs₀ hz (mem_ball_self hρ)` as an intermediate fact. Conclude with `h0 (by simpa using this)`. Conclude with `hz`. Use `exists_differentiableOn_of_locally_extends isOpen_ball (fun s hs => hs.1) ?_ h ?_` and prove the remaining obligations. Introduce `s₀ hs₀`.

Rewrite using `[mem_closure_iff_frequently]`. Establish `hev : ∀ᶠ s in 𝓝[≠] s₀, s ∈ {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0}` using `((hiso s₀ hs₀).and (nhdsWithin_le_nhds (isOpen_ball.mem_nhds hs₀))).mono fun s hs => ⟨hs.2, hs.1⟩`. Conclude with `hev.frequently.filter_mono nhdsWithin_le_nhds`. Introduce `s₀ hs₀`. Distinguish the cases in `hz : ψ s₀ ≠ 0`.

Conclude with `⟨_, (hψ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds ⟨hs₀, hz⟩, h, hh, fun x _ => rfl⟩`. Use `push_neg at hz`. Take `⟨C, k, hCk⟩` from `hb s₀ hs₀`. Establish `hN : {s | s ∈ ball (0 : ℂ) ρ ∧ (s ≠ s₀ → ψ s ≠ 0)} ∈ 𝓝 s₀`. Use `eventually_nhdsWithin_iff.mp (hiso s₀ hs₀)` as an intermediate fact.

Use `filter_upwards [this, isOpen_ball.mem_nhds hs₀] with s h1 h2 using ⟨h2, h1⟩`. Use `⟨_, hN, Function.update h s₀ (limUnder (𝓝[≠] s₀) h), ?_, ?_⟩` and prove the remaining obligations. Apply `differentiableOn_update_limUnder_of_isLittleO hN` to reduce the goal to its premises. Conclude with `hh.mono fun s hs => ⟨hs.1.1, hs.1.2 hs.2⟩`. Conclude with `isLittleO_sub_inv_sub_of_log_bound (han s₀ hs₀) hz (hiso s₀ hs₀) hCk`.

Introduce `s hs`. Establish `hne : s ≠ s₀` using `fun h' => hs.2.2 (by rw [h']; exact hz)`. Simplify using `[Function.update_of_ne hne]`.
-/
private theorem exists_differentiableOn_ball_of_log_bound {ψ h : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hψ : DifferentiableOn ℂ ψ (ball 0 ρ)) (h0 : ψ 0 ≠ 0)
    (hh : DifferentiableOn ℂ h {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0})
    (hb : ∀ s₀ ∈ ball (0 : ℂ) ρ, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ s in 𝓝 s₀, ψ s ≠ 0 → ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 ρ) ∧ EqOn H h {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0} := by
  have han : AnalyticOnNhd ℂ ψ (ball 0 ρ) := hψ.analyticOnNhd isOpen_ball
  have hiso : ∀ s₀ ∈ ball (0 : ℂ) ρ, ∀ᶠ s in 𝓝[≠] s₀, ψ s ≠ 0 := by
    intro s₀ hs₀
    rcases (han s₀ hs₀).eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · exfalso
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected
        hs₀ hz (mem_ball_self hρ)
      exact h0 (by simpa using this)
    · exact hz
  refine exists_differentiableOn_of_locally_extends isOpen_ball (fun s hs => hs.1) ?_ h ?_
  · intro s₀ hs₀
    rw [mem_closure_iff_frequently]
    have hev : ∀ᶠ s in 𝓝[≠] s₀, s ∈ {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0} :=
      ((hiso s₀ hs₀).and (nhdsWithin_le_nhds (isOpen_ball.mem_nhds hs₀))).mono
        fun s hs => ⟨hs.2, hs.1⟩
    exact hev.frequently.filter_mono nhdsWithin_le_nhds
  · intro s₀ hs₀
    by_cases hz : ψ s₀ ≠ 0
    · exact ⟨_, (hψ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
        ⟨hs₀, hz⟩, h, hh, fun x _ => rfl⟩
    push_neg at hz
    obtain ⟨C, k, hCk⟩ := hb s₀ hs₀
    have hN : {s | s ∈ ball (0 : ℂ) ρ ∧ (s ≠ s₀ → ψ s ≠ 0)} ∈ 𝓝 s₀ := by
      have := eventually_nhdsWithin_iff.mp (hiso s₀ hs₀)
      filter_upwards [this, isOpen_ball.mem_nhds hs₀] with s h1 h2 using ⟨h2, h1⟩
    refine ⟨_, hN, Function.update h s₀ (limUnder (𝓝[≠] s₀) h), ?_, ?_⟩
    · apply differentiableOn_update_limUnder_of_isLittleO hN
      · exact hh.mono fun s hs => ⟨hs.1.1, hs.1.2 hs.2⟩
      · exact isLittleO_sub_inv_sub_of_log_bound (han s₀ hs₀) hz (hiso s₀ hs₀) hCk
    · intro s hs
      have hne : s ≠ s₀ := fun h' => hs.2.2 (by rw [h']; exact hz)
      simp [Function.update_of_ne hne]

open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in

/- English proof (translation)
Establish `hSo : IsOpen {b ∈ U | φ b ≠ 0}` using `hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton`. Use `exists_differentiableOn_of_locally_extends hU (fun b hb => hb.1) hd u ?_` and prove the remaining obligations. Introduce `b₀ hb₀`. Distinguish the cases in `h0 : φ b₀ ≠ 0`. Conclude with `⟨_, hSo.mem_nhds ⟨hb₀, h0⟩, u, hu, fun x hx => rfl⟩`.

Use `push_neg at h0`. Take `⟨ε, hε, hεU⟩` from `Metric.isOpen_iff.mp hU b₀ hb₀`. Take `⟨b₁, hb₁S, hb₁⟩` from `Metric.mem_closure_iff.mp (hd hb₀) ε hε`. Use `set v := b₁ - b₀ with hv`. Establish `hv0 : v ≠ 0`.

Introduce `h`. Apply `hb₁S.2` to reduce the goal to its premises. Rewrite using `[show b₁ = b₀ from sub_eq_zero.mp h]`. Conclude with `h0`. Establish `hvpos : 0 < ‖v‖` using `norm_pos_iff.mpr hv0`.

Establish `hvε : ‖v‖ < ε` using `by rw [hv, ← dist_eq_norm, dist_comm]; exact hb₁`. Use `set R := ε / ‖v‖ with hRdef`. Establish `hR1 : 1 < R` using `(one_lt_div hvpos).mpr hvε`. Establish `hRv : R * ‖v‖ = ε` using `div_mul_cancel₀ _ hvpos.ne'`. Establish `hline : ∀ t : ℂ, ‖t‖ < R → b₀ + t • v ∈ U`.

Introduce `t ht`. Apply `hεU` to reduce the goal to its premises. Rewrite using `[mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgd : DifferentiableOn ℂ (fun t : ℂ => φ (b₀ + t • v)) (ball 0 R)` using `hφ.comp (by fun_prop) (fun t ht => hline t (by simpa using ht))`.

Establish `hg1 : (fun t : ℂ => φ (b₀ + t • v)) 1 ≠ 0` using `by simpa [hv] using hb₁S.2`. Establish `hgiso : ∀ᶠ t in 𝓝[≠] (0 : ℂ), φ (b₀ + t • v) ≠ 0`. Establish `han` using `hgd.analyticOnNhd isOpen_ball`. Break down `(han 0 (mem_ball_self (by linarith))).eventually_eq_zero_or_eventually_ne_zero with hz | hz` into its components or cases. Conclude with `absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 R).isPreconnected (mem_ball_self (by linarith)) hz (by simpa using hR1)) hg1`.

Conclude with `hz`. Choose the witnesses or unpack the hypotheses as in `⟨r₀, hr₀, hr₀g⟩ : ∃ r₀ > 0, ∀ t : ℂ, t ∈ ball (0 : ℂ) r₀ → t ≠ 0 → φ (b₀ + t • v) ≠ 0 := by`. Break down `Metric.mem_nhdsWithin_iff.mp hgiso with ⟨r₀, hr₀, h⟩` into its components or cases. Conclude with `⟨r₀, hr₀, fun t ht ht0 => h ⟨ht, ht0⟩⟩`. Use `set r := min r₀ R / 2 with hrdef`.

Establish `hr : 0 < r` using `by have := lt_min hr₀ (by linarith : (0 : ℝ) < R); positivity`. Establish `hrr₀ : r < r₀` using `by have := min_le_left r₀ R; linarith`. Establish `hrR : r ≤ R / 2` using `by have := min_le_right r₀ R; linarith`. Establish `hKS : (fun t : ℂ => b₀ + t • v) '' sphere 0 r ⊆ {b ∈ U | φ b ≠ 0}`. Introduce and unpack `_ ⟨t, ht, rfl⟩`.

Establish `htn : ‖t‖ = r` using `by simpa using ht`. Use `⟨hline t (by linarith), hr₀g t (by rw [mem_ball_zero_iff]; linarith) ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at htn`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK : IsCompact ((fun t : ℂ => b₀ + t • v) '' sphere 0 r)` using `(isCompact_sphere 0 r).image (by fun_prop)`. Take `⟨δ₁, hδ₁, hthick⟩` from `hK.exists_thickening_subset_open hSo hKS`. Use `set δ := min δ₁ (ε / 4) with hδdef`. Establish `hδ : 0 < δ` using `lt_min hδ₁ (by linarith)`. Establish `hcirc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ = r → b + t • v ∈ {x ∈ U | φ x ≠ 0}`.

Introduce `b hb t ht`. Apply `hthick` to reduce the goal to its premises. Rewrite using `[Metric.mem_thickening_iff]`. Use `⟨b₀ + t • v, ⟨t, by simpa using ht, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, show b + t • v - (b₀ + t • v) = b - b₀ by abel, ← dist_eq_norm]`.

Conclude with `lt_of_lt_of_le hb (min_le_left _ _)`. Establish `hdisc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ < 3 / 2 * r → b + t • v ∈ U`. Introduce `b hb t ht`. Apply `hεU` to reduce the goal to its premises. Rewrite using `[mem_ball, dist_eq_norm, show b + t • v - b₀ = (b - b₀) + t • v by abel]`.

Establish `h1 : ‖b - b₀‖ < ε / 4`. Rewrite using `[← dist_eq_norm]`. Conclude with `lt_of_lt_of_le hb (min_le_right _ _)`. Establish `h2 : ‖t • v‖ ≤ 3 / 4 * ε`. Rewrite using `[norm_smul]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `⟨ball b₀ δ, ball_mem_nhds b₀ hδ, fun b => (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v), ?_, ?_⟩` and prove the remaining obligations. Establish `hI` using `(_root_.GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn (F := fun θ b => u (b + circleMap 0 r θ • v)) (U := ball b₀ δ) isOpen_ball (a := 0) (b := 2 * π) ?_ ?_).1`. Conclude with `(differentiableOn_const _).mul hI`.

Establish `hc : Continuous fun p : ℝ × V => p.2 + circleMap 0 r p.1 • v` using `continuous_snd.add (((continuous_circleMap 0 r).comp continuous_fst).smul continuous_const)`. Use `hu.continuousOn.comp hc.continuousOn ?_` and prove the remaining obligations. Introduce and unpack `⟨θ, b⟩ ⟨_, hb⟩`. Conclude with `hcirc b hb _ (by simp [abs_of_pos hr])`. Introduce `θ _`.

Use `hu.comp (differentiable_id.add_const _).differentiableOn ?_` and prove the remaining obligations. Introduce `b hb`. Conclude with `hcirc b hb _ (by simp [abs_of_pos hr])`. Introduce and unpack `b ⟨hbδ, hbS⟩`. Take `⟨H, hHd, hHe⟩` from `exists_differentiableOn_ball_of_log_bound (ψ := fun s => φ (b + s • v)) (h := fun s => u (b + s • v)) (ρ := 3 / 2 * r) (by positivity) (hφ.comp (by fun_prop) (fun s hs => hdisc b hbδ s (by simpa using hs))) (by simpa using hbS.2) (hu.comp (by fun_prop) (fun s hs => ⟨hdisc b hbδ s …`.

Introduce `s₀ hs₀`. Take `⟨C, k, hCk⟩` from `hb _ (hdisc b hbδ s₀ (by simpa using hs₀))`. Conclude with `⟨C, k, ((by fun_prop : Continuous fun s : ℂ => b + s • v).tendsto s₀).eventually hCk⟩)`. Establish `hC` using `(hHd.mono (closedBall_subset_ball (by linarith : r < 3 / 2 * r))).circleIntegral_sub_inv_smul (mem_ball_self hr)`. Establish `hH0 : H 0 = u b`.

Use `hHe ⟨mem_ball_self (by positivity), by simpa using hbS.2⟩` as an intermediate fact. Simplify using `using this`. Establish `hint : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((circleMap 0 r θ - 0)⁻¹ • H (circleMap 0 r θ)) = I * u (b + circleMap 0 r θ • v)`. Introduce `θ`. Establish `hne : circleMap 0 r θ ≠ 0` using `circleMap_ne_center hr.ne'`.

Establish `hn : ‖circleMap 0 r θ‖ = r` using `by simp [abs_of_pos hr]`. Establish `hH : H (circleMap 0 r θ) = u (b + circleMap 0 r θ • v)` using `hHe ⟨by rw [mem_ball_zero_iff, hn]; linarith, (hcirc b hbδ _ hn).2⟩`. Rewrite using `[deriv_circleMap, hH, sub_zero, smul_eq_mul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite `hC` using `[circleIntegral, intervalIntegral.integral_congr (fun θ _ => hint θ), intervalIntegral.integral_const_mul, hH0]`.

Use `show (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = u b`. Establish `hI : I ≠ 0` using `I_ne_zero`. Establish `hπ : (π : ℂ) ≠ 0` using `ofReal_ne_zero.mpr Real.pi_ne_zero`. Establish `: ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = 2 * π * u b`. Apply `mul_left_cancel₀ hI` to reduce the goal to its premises.

Rewrite using `[hC, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem _root_.GlobalTheory.LogExt.riemann_extension_log (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) :
    ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  have hSo : IsOpen {b ∈ U | φ b ≠ 0} :=
    hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  refine exists_differentiableOn_of_locally_extends hU (fun b hb => hb.1) hd u ?_
  intro b₀ hb₀
  by_cases h0 : φ b₀ ≠ 0
  · exact ⟨_, hSo.mem_nhds ⟨hb₀, h0⟩, u, hu, fun x hx => rfl⟩
  push_neg at h0
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU b₀ hb₀
  obtain ⟨b₁, hb₁S, hb₁⟩ := Metric.mem_closure_iff.mp (hd hb₀) ε hε
  set v := b₁ - b₀ with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply hb₁S.2
    rw [show b₁ = b₀ from sub_eq_zero.mp h]
    exact h0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvε : ‖v‖ < ε := by rw [hv, ← dist_eq_norm, dist_comm]; exact hb₁
  set R := ε / ‖v‖ with hRdef
  have hR1 : 1 < R := (one_lt_div hvpos).mpr hvε
  have hRv : R * ‖v‖ = ε := div_mul_cancel₀ _ hvpos.ne'
  have hline : ∀ t : ℂ, ‖t‖ < R → b₀ + t • v ∈ U := by
    intro t ht
    apply hεU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ < R * ‖v‖ := by gcongr
      _ = ε := hRv
  have hgd : DifferentiableOn ℂ (fun t : ℂ => φ (b₀ + t • v)) (ball 0 R) :=
    hφ.comp (by fun_prop) (fun t ht => hline t (by simpa using ht))
  have hg1 : (fun t : ℂ => φ (b₀ + t • v)) 1 ≠ 0 := by simpa [hv] using hb₁S.2
  have hgiso : ∀ᶠ t in 𝓝[≠] (0 : ℂ), φ (b₀ + t • v) ≠ 0 := by
    have han := hgd.analyticOnNhd isOpen_ball
    rcases (han 0 (mem_ball_self (by linarith))).eventually_eq_zero_or_eventually_ne_zero with
      hz | hz
    · exact absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball 0 R).isPreconnected (mem_ball_self (by linarith)) hz
        (by simpa using hR1)) hg1
    · exact hz
  obtain ⟨r₀, hr₀, hr₀g⟩ : ∃ r₀ > 0, ∀ t : ℂ, t ∈ ball (0 : ℂ) r₀ → t ≠ 0 →
      φ (b₀ + t • v) ≠ 0 := by
    rcases Metric.mem_nhdsWithin_iff.mp hgiso with ⟨r₀, hr₀, h⟩
    exact ⟨r₀, hr₀, fun t ht ht0 => h ⟨ht, ht0⟩⟩
  set r := min r₀ R / 2 with hrdef
  have hr : 0 < r := by have := lt_min hr₀ (by linarith : (0 : ℝ) < R); positivity
  have hrr₀ : r < r₀ := by have := min_le_left r₀ R; linarith
  have hrR : r ≤ R / 2 := by have := min_le_right r₀ R; linarith
  have hKS : (fun t : ℂ => b₀ + t • v) '' sphere 0 r ⊆ {b ∈ U | φ b ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    have htn : ‖t‖ = r := by simpa using ht
    refine ⟨hline t (by linarith), hr₀g t (by rw [mem_ball_zero_iff]; linarith) ?_⟩
    rintro rfl
    simp at htn
    linarith
  have hK : IsCompact ((fun t : ℂ => b₀ + t • v) '' sphere 0 r) :=
    (isCompact_sphere 0 r).image (by fun_prop)
  obtain ⟨δ₁, hδ₁, hthick⟩ := hK.exists_thickening_subset_open hSo hKS
  set δ := min δ₁ (ε / 4) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (by linarith)
  have hcirc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ = r → b + t • v ∈ {x ∈ U | φ x ≠ 0} := by
    intro b hb t ht
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨b₀ + t • v, ⟨t, by simpa using ht, rfl⟩, ?_⟩
    rw [dist_eq_norm, show b + t • v - (b₀ + t • v) = b - b₀ by abel, ← dist_eq_norm]
    exact lt_of_lt_of_le hb (min_le_left _ _)
  have hdisc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ < 3 / 2 * r → b + t • v ∈ U := by
    intro b hb t ht
    apply hεU
    rw [mem_ball, dist_eq_norm, show b + t • v - b₀ = (b - b₀) + t • v by abel]
    have h1 : ‖b - b₀‖ < ε / 4 := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hb (min_le_right _ _)
    have h2 : ‖t • v‖ ≤ 3 / 4 * ε := by
      rw [norm_smul]
      calc ‖t‖ * ‖v‖ ≤ (3 / 2 * r) * ‖v‖ := by gcongr
        _ ≤ (3 / 2 * (R / 2)) * ‖v‖ := by gcongr
        _ = 3 / 4 * ε := by rw [← hRv]; ring
    calc ‖(b - b₀) + t • v‖ ≤ ‖b - b₀‖ + ‖t • v‖ := norm_add_le _ _
      _ < ε := by linarith
  refine ⟨ball b₀ δ, ball_mem_nhds b₀ hδ,
    fun b => (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v), ?_, ?_⟩
  · have hI := (_root_.GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
      (F := fun θ b => u (b + circleMap 0 r θ • v)) (U := ball b₀ δ) isOpen_ball
      (a := 0) (b := 2 * π) ?_ ?_).1
    · exact (differentiableOn_const _).mul hI
    · have hc : Continuous fun p : ℝ × V => p.2 + circleMap 0 r p.1 • v :=
        continuous_snd.add (((continuous_circleMap 0 r).comp continuous_fst).smul continuous_const)
      refine hu.continuousOn.comp hc.continuousOn ?_
      rintro ⟨θ, b⟩ ⟨_, hb⟩
      exact hcirc b hb _ (by simp [abs_of_pos hr])
    · intro θ _
      refine hu.comp (differentiable_id.add_const _).differentiableOn ?_
      intro b hb
      exact hcirc b hb _ (by simp [abs_of_pos hr])
  · rintro b ⟨hbδ, hbS⟩
    obtain ⟨H, hHd, hHe⟩ := exists_differentiableOn_ball_of_log_bound (ψ := fun s => φ (b + s • v))
      (h := fun s => u (b + s • v)) (ρ := 3 / 2 * r) (by positivity)
      (hφ.comp (by fun_prop) (fun s hs => hdisc b hbδ s (by simpa using hs)))
      (by simpa using hbS.2)
      (hu.comp (by fun_prop) (fun s hs => ⟨hdisc b hbδ s (by simpa using hs.1), hs.2⟩))
      (by
        intro s₀ hs₀
        obtain ⟨C, k, hCk⟩ := hb _ (hdisc b hbδ s₀ (by simpa using hs₀))
        exact ⟨C, k, ((by fun_prop : Continuous fun s : ℂ => b + s • v).tendsto s₀).eventually hCk⟩)
    have hC := (hHd.mono (closedBall_subset_ball (by linarith : r < 3 / 2 * r))).circleIntegral_sub_inv_smul
      (mem_ball_self hr)
    have hH0 : H 0 = u b := by
      have := hHe ⟨mem_ball_self (by positivity), by simpa using hbS.2⟩
      simpa using this
    have hint : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((circleMap 0 r θ - 0)⁻¹ • H (circleMap 0 r θ))
        = I * u (b + circleMap 0 r θ • v) := by
      intro θ
      have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
      have hn : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr]
      have hH : H (circleMap 0 r θ) = u (b + circleMap 0 r θ • v) :=
        hHe ⟨by rw [mem_ball_zero_iff, hn]; linarith, (hcirc b hbδ _ hn).2⟩
      rw [deriv_circleMap, hH, sub_zero, smul_eq_mul, smul_eq_mul]
      field_simp
    rw [circleIntegral, intervalIntegral.integral_congr (fun θ _ => hint θ),
      intervalIntegral.integral_const_mul, hH0] at hC
    show (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = u b
    have hI : I ≠ 0 := I_ne_zero
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have : ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = 2 * π * u b := by
      apply mul_left_cancel₀ hI
      rw [hC, smul_eq_mul]
      ring
    rw [this]
    field_simp

end GlobalTheory.LogExt
