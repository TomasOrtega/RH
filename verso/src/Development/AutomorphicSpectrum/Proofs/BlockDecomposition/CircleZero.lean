import Mathlib

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace GlobalTheory.CompanionTheory.CfFJ

structure Fam {X : Type*} [TopologicalSpace X] (U : Set ℂ) (f : ℂ → X → ℂ) : Prop where
  cont : ContinuousOn (fun q : ℂ × X => f q.1 q.2) (U ×ˢ univ)
  hol : ∀ x, DifferentiableOn ℂ (f · x) U
  bd : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ B : ℝ, ∀ w ∈ K, ∀ x, ‖f w x‖ ≤ B

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {U : Set ℂ}

/- English proof (translation)
The claim follows from `continuous_fst.continuousOn hol _ := differentiableOn_id bd K _ hc := by obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn continuousOn_id exact ⟨B, fun w hw _ => hB w hw⟩`.
-/
theorem fam_id : Fam (X := X) univ (fun w _ => w) where
  cont := continuous_fst.continuousOn
  hol _ := differentiableOn_id
  bd K _ hc := by
    obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn continuousOn_id
    exact ⟨B, fun w hw _ => hB w hw⟩

/- English proof (translation)
The claim follows from `h.cont.comp (continuous_fst.prodMk (hφ.comp continuous_snd)).continuousOn (fun q hq => ⟨hq.1, mem_univ _⟩) hol z := h.hol (φ z) bd K hK hc := by obtain ⟨B, hB⟩ := h.bd K hK hc exact ⟨B, fun w hw z => hB w hw _⟩`.
-/
theorem Fam.comp {f : ℂ → X → ℂ} (h : Fam U f) {φ : Z → X} (hφ : Continuous φ) : Fam U (fun w z => f w (φ z)) where
  cont := h.cont.comp (continuous_fst.prodMk (hφ.comp continuous_snd)).continuousOn (fun q hq => ⟨hq.1, mem_univ _⟩)
  hol z := h.hol (φ z)
  bd K hK hc := by
    obtain ⟨B, hB⟩ := h.bd K hK hc
    exact ⟨B, fun w hw z => hB w hw _⟩

/- English proof (translation)
The claim follows from `h.cont.comp_continuous (f := fun x => (w, x)) (by fun_prop) (fun _ => ⟨hw, mem_univ _⟩)`.
-/
theorem Fam.slice {f : ℂ → X → ℂ} (h : Fam U f) {w : ℂ} (hw : w ∈ U) : Continuous (f w) :=
  h.cont.comp_continuous (f := fun x => (w, x)) (by fun_prop) (fun _ => ⟨hw, mem_univ _⟩)

variable [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y} {κ : Y → ℂ}

/- English proof (translation)
Establish `cm : ∀ θ, circleMap c R θ ∈ sphere c R` using `circleMap_mem_sphere c hR.le`. Establish `hcm : Continuous (circleMap c R)` using `continuous_circleMap c R`. Take `⟨A, hA⟩` from `(isCompact_sphere c R).exists_bound_of_continuousOn ha`. Take `⟨B, hB⟩` from `h.bd _ hS (isCompact_sphere c R)`. Use `set Φ : ℝ → Y → ℂ := fun θ y => deriv (circleMap c R) θ • (a (circleMap c R θ) * g (circleMap c R θ) y) with hΦ`.

Establish `hΦc : Continuous fun q : Y × ℝ => Φ q.2 q.1`. Establish `h1 : Continuous fun q : Y × ℝ => g (circleMap c R q.2) q.1` using `h.cont.comp_continuous (f := fun q : Y × ℝ => (circleMap c R q.2, q.1)) ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)`. Establish `h2 : Continuous fun θ => a (circleMap c R θ)` using `ha.comp_continuous hcm cm`. Establish `h3 : Continuous fun θ => deriv (circleMap c R) θ`. Simplify using `only [deriv_circleMap]`.

Conclude with `(continuous_circleMap 0 R).mul continuous_const`. Simplify using `only [hΦ, smul_eq_mul]`. Conclude with `(h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)`. Establish `hΦb : ∀ θ y, ‖Φ θ y‖ ≤ |R| * (A * B)`. Introduce `θ y`.

Simplify using `only [hΦ, smul_eq_mul, norm_mul, deriv_circleMap, norm_circleMap_zero, Complex.norm_I, mul_one]`. Establish `hb` using `hB _ (cm θ) y`. Use `gcongr`. Conclude with `(norm_nonneg _).trans (hA _ (cm θ))`. Conclude with `hA _ (cm θ)`.

Establish `hint : Integrable (Function.uncurry fun (y : Y) (θ : ℝ) => Φ θ y * κ y) (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi))))`. Establish `h0 : Integrable (fun q : Y × ℝ => κ q.1 * (1 : ℂ)) (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi))))` using `hκ.mul_prod (integrable_const (1 : ℂ))`. Establish `h1` using `h0.bdd_mul (f := fun q : Y × ℝ => Φ q.2 q.1) (c := |R| * (A * B)) hΦc.aestronglyMeasurable (Eventually.of_forall fun q => hΦb _ _)`. Use `h1.congr (Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Simplify using `[Function.uncurry]`.

Establish `hpos : (0 : ℝ) ≤ 2 * Real.pi` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [circleIntegral, intervalIntegral.integral_of_le hpos, integral_mul_const, hΦ]`. Use `_ = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, Φ θ y * κ y ∂ν := integral_integral_swap hint`.

Use `_ = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by`. Simplify using `only [circleIntegral, intervalIntegral.integral_of_le hpos]`. Use `integral_congr_ae (Eventually.of_forall fun θ => ?_)` and prove the remaining obligations. Simplify using `only [hΦ, smul_eq_mul, mul_assoc, integral_const_mul]`.
-/
theorem Fam.swap [SFinite ν] {g : ℂ → Y → ℂ} (h : Fam U g) (hκ : Integrable κ ν) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  obtain ⟨A, hA⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn ha
  obtain ⟨B, hB⟩ := h.bd _ hS (isCompact_sphere c R)
  set Φ : ℝ → Y → ℂ := fun θ y => deriv (circleMap c R) θ • (a (circleMap c R θ) * g (circleMap c R θ) y) with hΦ
  have hΦc : Continuous fun q : Y × ℝ => Φ q.2 q.1 := by
    have h1 : Continuous fun q : Y × ℝ => g (circleMap c R q.2) q.1 :=
      h.cont.comp_continuous (f := fun q : Y × ℝ => (circleMap c R q.2, q.1))
        ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
    have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
    have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    simp only [hΦ, smul_eq_mul]
    exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)
  have hΦb : ∀ θ y, ‖Φ θ y‖ ≤ |R| * (A * B) := by
    intro θ y
    simp only [hΦ, smul_eq_mul, norm_mul, deriv_circleMap, norm_circleMap_zero, Complex.norm_I, mul_one]
    have hb := hB _ (cm θ) y
    gcongr
    · exact (norm_nonneg _).trans (hA _ (cm θ))
    · exact hA _ (cm θ)
  have hint : Integrable (Function.uncurry fun (y : Y) (θ : ℝ) => Φ θ y * κ y)
      (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    have h0 : Integrable (fun q : Y × ℝ => κ q.1 * (1 : ℂ)) (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
      hκ.mul_prod (integrable_const (1 : ℂ))
    have h1 := h0.bdd_mul (f := fun q : Y × ℝ => Φ q.2 q.1) (c := |R| * (A * B)) hΦc.aestronglyMeasurable
      (Eventually.of_forall fun q => hΦb _ _)
    refine h1.congr (Eventually.of_forall fun q => ?_)
    simp [Function.uncurry]
  have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν
      = ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), Φ θ y * κ y ∂volume ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos, integral_mul_const, hΦ]
    _ = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, Φ θ y * κ y ∂ν := integral_integral_swap hint
    _ = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos]
        refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only [hΦ, smul_eq_mul, mul_assoc, integral_const_mul]

/- English proof (translation)
Establish `hsl : ∀ {w : ℂ}, w ∈ U → ∀ x, Continuous fun y => f w (x, y)` using `fun hw x => (h.slice hw).comp (by fun_prop)`. Establish `hcont : ContinuousOn (fun q : ℂ × X => ∫ y, f q.1 (q.2, y) * κ y ∂ν) (U ×ˢ univ)`. Introduce `q hq`. Establish `hqU : q.1 ∈ U` using `hq.1`. Take `⟨r, hr, hrU⟩` from `nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hqU)`.

Take `⟨B, hB⟩` from `h.bd _ hrU (isCompact_closedBall _ _)`. Establish `hnear : ∀ᶠ u : ℂ × X in 𝓝 q, u.1 ∈ ball q.1 r` using `continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))`. Use `ContinuousAt.continuousWithinAt (continuousAt_of_dominated (bound := fun y => B * ‖κ y‖) ?_ ?_ ?_ ?_)` and prove the remaining obligations. Use `filter_upwards [hnear] with u hu`. Conclude with `(hsl (hrU (ball_subset_closedBall hu)) u.2).aestronglyMeasurable.mul hκ.aestronglyMeasurable`.

Use `filter_upwards [hnear] with u hu`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB _ (ball_subset_closedBall hu) _) (norm_nonneg _)`. Conclude with `hκ.norm.const_mul B`.

Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Establish `h1 : ContinuousAt (fun q : ℂ × (X × Y) => f q.1 q.2) (q.1, (q.2, y))` using `h.cont.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hqU, mem_univ _⟩)`. Establish `h2 : ContinuousAt (fun u : ℂ × X => (u.1, (u.2, y))) q` using `by fun_prop`. Conclude with `(ContinuousAt.comp (f := fun u : ℂ × X => (u.1, (u.2, y))) h1 h2).mul continuousAt_const`. Use `⟨hcont, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x w₀ hw₀`. Use `DifferentiableAt.differentiableWithinAt ?_` and prove the remaining obligations. Take `⟨r, hr, hrU⟩` from `nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)`. Establish `hg : Fam U fun w y => f w (x, y)` using `h.comp (φ := fun y => (x, y)) (by fun_prop)`. Establish `hS : sphere w₀ r ⊆ U` using `sphere_subset_closedBall.trans hrU`.

Establish `hQc : ContinuousOn (fun w => ∫ y, f w (x, y) * κ y ∂ν) U` using `hcont.comp (Continuous.continuousOn (f := fun w : ℂ => (w, x)) (by fun_prop)) (fun w hw => ⟨hw, mem_univ _⟩)`. Use `set Q : ℂ → ℂ := fun w => ∫ y, f w (x, y) * κ y ∂ν with hQ`. Establish `hci : CircleIntegrable Q w₀ ((⟨r, hr.le⟩ : NNReal) : ℝ)` using `(hQc.mono hS).circleIntegrable hr.le`. Establish `hps` using `hasFPowerSeriesOn_cauchy_integral hci (show (0 : NNReal) < ⟨r, hr.le⟩ from hr)`. Use `hps.analyticAt.differentiableAt.congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw`. Establish `hwS : ∀ v ∈ sphere w₀ r, v ≠ w`. Introduce and unpack `v hv rfl`. Conclude with `(ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 hv)`. Establish `hcauchy : ∀ y, ∮ v in C(w₀, r), ((2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹) * f v (x, y) = f w (x, y)`.

Introduce `y`. Establish `h1` using `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := ∅) countable_empty hw (f := fun v => f v (x, y)) ((hg.hol y).continuousOn.mono hrU) (fun v hv => (hg.hol y).differentiableAt (hU.mem_nhds (hrU (ball_subset_closedBall hv.1))))`. Simplify using `only [smul_eq_mul] at h1`. Simplify using `only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]`. Rewrite using `[h1, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]`.

Establish `hsw` using `hg.swap hκ hr hS (a := fun v => (2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹) (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun v hv => sub_ne_zero.2 (hwS v hv)))`. Simplify using `only [hcauchy] at hsw`. Simplify using `only [smul_eq_mul]`. Express the relevant statement in the definitionally equal form `Q w = _`. Rewrite using `[hQ]`.

Simplify using `only`. Rewrite using `[hsw]`. Simplify using `only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]`. Both sides reduce to the same expression. Introduce `K hK hc`.

Take `⟨B, hB⟩` from `h.bd K hK hc`. Use `⟨∫ y, B * ‖κ y‖ ∂ν, fun w hw x => ?_⟩` and prove the remaining obligations. Use `norm_integral_le_of_norm_le (hκ.norm.const_mul B) (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB w hw _) (norm_nonneg _)`.
-/
theorem Fam.stage [FirstCountableTopology X] [SFinite ν] (hU : IsOpen U) {f : ℂ → X × Y → ℂ} (h : Fam U f)
    (hκ : Integrable κ ν) : Fam U (fun w x => ∫ y, f w (x, y) * κ y ∂ν) := by
  have hsl : ∀ {w : ℂ}, w ∈ U → ∀ x, Continuous fun y => f w (x, y) := fun hw x =>
    (h.slice hw).comp (by fun_prop)
  have hcont : ContinuousOn (fun q : ℂ × X => ∫ y, f q.1 (q.2, y) * κ y ∂ν) (U ×ˢ univ) := by
    intro q hq
    have hqU : q.1 ∈ U := hq.1
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hqU)
    obtain ⟨B, hB⟩ := h.bd _ hrU (isCompact_closedBall _ _)
    have hnear : ∀ᶠ u : ℂ × X in 𝓝 q, u.1 ∈ ball q.1 r :=
      continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated (bound := fun y => B * ‖κ y‖) ?_ ?_ ?_ ?_)
    · filter_upwards [hnear] with u hu
      exact (hsl (hrU (ball_subset_closedBall hu)) u.2).aestronglyMeasurable.mul hκ.aestronglyMeasurable
    · filter_upwards [hnear] with u hu
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (ball_subset_closedBall hu) _) (norm_nonneg _)
    · exact hκ.norm.const_mul B
    · refine Eventually.of_forall fun y => ?_
      have h1 : ContinuousAt (fun q : ℂ × (X × Y) => f q.1 q.2) (q.1, (q.2, y)) :=
        h.cont.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hqU, mem_univ _⟩)
      have h2 : ContinuousAt (fun u : ℂ × X => (u.1, (u.2, y))) q := by fun_prop
      exact (ContinuousAt.comp (f := fun u : ℂ × X => (u.1, (u.2, y))) h1 h2).mul continuousAt_const
  refine ⟨hcont, ?_, ?_⟩
  · intro x w₀ hw₀
    refine DifferentiableAt.differentiableWithinAt ?_
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)
    have hg : Fam U fun w y => f w (x, y) := h.comp (φ := fun y => (x, y)) (by fun_prop)
    have hS : sphere w₀ r ⊆ U := sphere_subset_closedBall.trans hrU
    have hQc : ContinuousOn (fun w => ∫ y, f w (x, y) * κ y ∂ν) U :=
      hcont.comp (Continuous.continuousOn (f := fun w : ℂ => (w, x)) (by fun_prop)) (fun w hw => ⟨hw, mem_univ _⟩)
    set Q : ℂ → ℂ := fun w => ∫ y, f w (x, y) * κ y ∂ν with hQ
    have hci : CircleIntegrable Q w₀ ((⟨r, hr.le⟩ : NNReal) : ℝ) := (hQc.mono hS).circleIntegrable hr.le
    have hps := hasFPowerSeriesOn_cauchy_integral hci (show (0 : NNReal) < ⟨r, hr.le⟩ from hr)
    refine hps.analyticAt.differentiableAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    have hwS : ∀ v ∈ sphere w₀ r, v ≠ w := by
      rintro v hv rfl
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 hv)
    have hcauchy : ∀ y, ∮ v in C(w₀, r), ((2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹) * f v (x, y) = f w (x, y) := by
      intro y
      have h1 := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := ∅) countable_empty hw
        (f := fun v => f v (x, y)) ((hg.hol y).continuousOn.mono hrU)
        (fun v hv => (hg.hol y).differentiableAt (hU.mem_nhds (hrU (ball_subset_closedBall hv.1))))
      simp only [smul_eq_mul] at h1
      simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
      rw [h1, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
    have hsw := hg.swap hκ hr hS (a := fun v => (2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹)
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun v hv => sub_ne_zero.2 (hwS v hv)))
    simp only [hcauchy] at hsw
    simp only [smul_eq_mul]
    change Q w = _
    rw [hQ]
    simp only
    rw [hsw]
    simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
    rfl
  · intro K hK hc
    obtain ⟨B, hB⟩ := h.bd K hK hc
    refine ⟨∫ y, B * ‖κ y‖ ∂ν, fun w hw x => ?_⟩
    refine norm_integral_le_of_norm_le (hκ.norm.const_mul B) (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB w hw _) (norm_nonneg _)

/- English proof (translation)
Establish `cm : ∀ θ, circleMap c R θ ∈ sphere c R` using `circleMap_mem_sphere c hR`. Establish `hcm : Continuous (circleMap c R)` using `continuous_circleMap c R`. Establish `h1 : Continuous fun q : Z × ℝ => e (circleMap c R q.2) q.1` using `hc.comp_continuous (f := fun q : Z × ℝ => (circleMap c R q.2, q.1)) ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)`. Establish `h2 : Continuous fun θ => a (circleMap c R θ)` using `ha.comp_continuous hcm cm`. Establish `h3 : Continuous fun θ => deriv (circleMap c R) θ`.

Simplify using `only [deriv_circleMap]`. Conclude with `(continuous_circleMap 0 R).mul continuous_const`. Simplify using `only [circleIntegral]`. Use `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _` and prove the remaining obligations. Simplify using `only [Function.uncurry_def, smul_eq_mul]`.

Conclude with `(h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)`.
-/
theorem circle_cont {e : ℂ → Z → ℂ} (hc : ContinuousOn (fun q : ℂ × Z => e q.1 q.2) (U ×ˢ univ)) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    Continuous fun z => ∮ w in C(c, R), a w * e w z := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  have h1 : Continuous fun q : Z × ℝ => e (circleMap c R q.2) q.1 :=
    hc.comp_continuous (f := fun q : Z × ℝ => (circleMap c R q.2, q.1))
      ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
  have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
  have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  simp only [circleIntegral]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  simp only [Function.uncurry_def, smul_eq_mul]
  exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)

/- English proof (translation)
Take `⟨q, hq, hnd⟩` from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀`. Use `set m := d.rootMultiplicity s₀ with hm`. Establish `hev : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z` using `fun z => by conv_lhs => rw [hq]`. Simplify using the standard rewrite rules. Establish `hq0 : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0`.

Introduce `z hz h0`. Distinguish the cases in `hzs : z = s₀`. Substitute `hzs` using the available equality. Conclude with `hnd (Polynomial.dvd_iff_isRoot.2 h0)`. Conclude with `hroot z hz hzs (by rw [hev, h0, mul_zero])`.

Establish `hsub : ∀ z ∈ sphere s₀ ε, z ≠ s₀`. Introduce and unpack `z hz rfl`. Simplify using `[hε.ne] at hz`. Establish `hcongr : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) = ∮ z in C(s₀, ε), (z - s₀) ^ (j - m) * (e z / q.eval z)`. Use `circleIntegral.integral_congr hε.le fun z hz => ?_` and prove the remaining obligations.

Establish `h1 : z - s₀ ≠ 0` using `sub_ne_zero.2 (hsub z hz)`. Establish `h2` using `hq0 z (sphere_subset_closedBall hz)`. Rewrite using `[hev, show j = (j - m) + m by omega, pow_add, Nat.add_sub_cancel]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hcongr]`.

Establish `hdiff : ∀ z ∈ closedBall s₀ ε, DifferentiableAt ℂ (fun z => (z - s₀) ^ (j - m) * (e z / q.eval z)) z`. Introduce `z hz`. Establish `h1 : DifferentiableAt ℂ e z` using `he.differentiableAt (hU.mem_nhds (hB hz))`. Establish `h2 : DifferentiableAt ℂ (fun z => q.eval z) z` using `q.differentiable.differentiableAt`. Conclude with `((differentiableAt_id.sub_const s₀).pow _).mul (h1.div h2 (hq0 z hz))`.

Conclude with `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt) (fun z hz => hdiff z (ball_subset_closedBall hz.1))`.
-/
theorem circle_zero {e : ℂ → ℂ} (hU : IsOpen U) (he : DifferentiableOn ℂ e U) {d : Polynomial ℂ} (hd : d ≠ 0) {s₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hB : closedBall s₀ ε ⊆ U) (hroot : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → d.eval z ≠ 0) {j : ℕ}
    (hj : d.rootMultiplicity s₀ ≤ j) : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) = 0 := by
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  set m := d.rootMultiplicity s₀ with hm
  have hev : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := fun z => by
    conv_lhs => rw [hq]
    simp
  have hq0 : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
    intro z hz h0
    by_cases hzs : z = s₀
    · subst hzs
      exact hnd (Polynomial.dvd_iff_isRoot.2 h0)
    · exact hroot z hz hzs (by rw [hev, h0, mul_zero])
  have hsub : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  have hcongr : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ (j - m) * (e z / q.eval z) := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    have h1 : z - s₀ ≠ 0 := sub_ne_zero.2 (hsub z hz)
    have h2 := hq0 z (sphere_subset_closedBall hz)
    rw [hev, show j = (j - m) + m by omega, pow_add, Nat.add_sub_cancel]
    field_simp
  rw [hcongr]
  have hdiff : ∀ z ∈ closedBall s₀ ε, DifferentiableAt ℂ (fun z => (z - s₀) ^ (j - m) * (e z / q.eval z)) z := by
    intro z hz
    have h1 : DifferentiableAt ℂ e z := he.differentiableAt (hU.mem_nhds (hB hz))
    have h2 : DifferentiableAt ℂ (fun z => q.eval z) z := q.differentiable.differentiableAt
    exact ((differentiableAt_id.sub_const s₀).pow _).mul (h1.div h2 (hq0 z hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
    (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (ball_subset_closedBall hz.1))

end GlobalTheory.CompanionTheory.CfFJ
