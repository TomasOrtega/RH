import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeW
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

/- English proof (translation)
Establish `htm : MeasurableSet (A.chart i).target` using `(A.chart i).open_target.measurableSet`. Establish `hsm : MeasurableSet (A.chart i).source` using `(A.chart i).open_source.measurableSet`. Establish `hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target)` using `(A.chart i).continuousOn_symm.aemeasurable htm`. Establish `hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) (volume.restrict (A.chart i).target)` using `(ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm`. Establish `hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))))` using `hsymm.mono_ac (withDensity_absolutelyContinuous _ _)`.

Establish `hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))))`. Use extensionality with `s hs`. Rewrite using `[Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs, withDensity_apply' _ _, Measure.restrict_restrict' htm, A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source, (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart …`. Rewrite using `[hmeas, lintegral_map' hg.aemeasurable hsymm']`. Use `(lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans (lintegral_congr fun v => ?_)` and prove the remaining obligations.

Simplify using `only [Pi.mul_apply, Function.comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ap_lintegral_chart (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
  have htm : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hsm : MeasurableSet (A.chart i).source := (A.chart i).open_source.measurableSet
  have hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable htm
  have hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm
  have hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity
      (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity
        (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs,
      withDensity_apply' _ _, Measure.restrict_restrict' htm,
      A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source,
      (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart i).target]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm']
  refine (lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans
    (lintegral_congr fun v => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring

/- English proof (translation)
Use `hK.measure_lt_top_of_nhdsWithin fun y _ => ?_` and prove the remaining obligations. Use `set e := A.chart (A.pick y) with he`. Establish `hys : y ∈ e.source` using `A.mem_pick y`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)`. Establish `hδ : 0 < ε / 2` using `by positivity`.

Establish `hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Establish `hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2))` using `e.isOpen_inter_preimage Metric.isOpen_ball`. Establish `hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)` using `⟨hys, Metric.mem_ball_self hδ⟩`. Use `⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2), mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩` and prove the remaining obligations. Rewrite using `[A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]`.

Establish `himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `Metric.ball_subset_closedBall hx.2`. Establish `hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v))) (Metric.closedBall (e y) (ε / 2))` using `(Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb`. Take `⟨M, hM⟩` from `(isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont`.

Combine the equalities or inequalities in the displayed calculation. Apply `setLIntegral_mono' Metric.isClosed_closedBall.measurableSet` to reduce the goal to its premises. Introduce `v hv`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h1` using `hM v hv`.

Rewrite `h1` using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Conclude with `h1`. Use `_ < ⊤ := by`. Rewrite using `[setLIntegral_const]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top`.
-/
theorem ap_mu_compact (A : WeightedAtlas n Y ι La) (K : Set Y) (hK : IsCompact K) :
    A.mu K < ⊤ := by
  refine hK.measure_lt_top_of_nhdsWithin fun y _ => ?_
  set e := A.chart (A.pick y) with he
  have hys : y ∈ e.source := A.mem_pick y
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)
  have hδ : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2) := ⟨hys, Metric.mem_ball_self hδ⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩
  rw [A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]
  have himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Metric.ball_subset_closedBall hx.2
  have hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v)))
      (Metric.closedBall (e y) (ε / 2)) :=
    (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont
  calc _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) (e.symm v))) := lintegral_mono_set himg
    _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2), ENNReal.ofReal M := by
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro v hv
        apply ENNReal.ofReal_le_ofReal
        have h1 := hM v hv
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
        exact h1
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

/- English proof (translation)
Introduce `x hx`. Use `set e := A.chart (A.pick x) with he`. Establish `hxs : x ∈ e.source` using `A.mem_pick x`. Establish `hex : e x ∈ e.target` using `e.map_source hxs`. Establish `hopen : IsOpen (e.target ∩ e.symm ⁻¹' U)` using `e.isOpen_inter_preimage_symm hU`.

Establish `hmem : e x ∈ e.target ∩ e.symm ⁻¹' U`. Use `⟨hex, ?_⟩` and prove the remaining obligations. Use `show e.symm (e x) ∈ U`. Rewrite using `[e.left_inv hxs]`. Conclude with `hx`.

Establish `h1 : ContinuousAt (φ ∘ e.symm) (e x)` using `(h (A.pick x)).continuousAt (hopen.mem_nhds hmem)`. Establish `h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x` using `h1.comp (e.continuousAt hxs)`. Establish `h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ` using `by filter_upwards [e.eventually_left_inverse hxs] with y hy`. Simplify using `[hy]`. Conclude with `(h2.congr h3).continuousWithinAt`.
-/
theorem api_contOn_chart {E : Type*} [TopologicalSpace E] (A : WeightedAtlas n Y ι La)
    (φ : Y → E) {U : Set Y} (hU : IsOpen U)
    (h : ∀ i, ContinuousOn (φ ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) :
    ContinuousOn φ U := by
  intro x hx
  set e := A.chart (A.pick x) with he
  have hxs : x ∈ e.source := A.mem_pick x
  have hex : e x ∈ e.target := e.map_source hxs
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hex, ?_⟩
    show e.symm (e x) ∈ U
    rw [e.left_inv hxs]
    exact hx
  have h1 : ContinuousAt (φ ∘ e.symm) (e x) :=
    (h (A.pick x)).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hxs)
  have h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ := by
    filter_upwards [e.eventually_left_inverse hxs] with y hy
    simp [hy]
  exact (h2.congr h3).continuousWithinAt

/- English proof (translation)
Unfold `WeightedAtlas.nsq`. Establish `hj : x ∈ (A.chart (A.pick x)).source` using `A.mem_pick x`. Establish `hsec` using `hFs.2 i (A.pick x) x hxU hxs hj`. Establish `hph` using `A.ph_trans la i (A.pick x) x hxs hj`. Establish `hg` using `A.g_ne la i (A.pick x) x hxs hj`.

Establish `hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2` using `pow_pos (norm_pos_iff.mpr hg) 2`. Rewrite using `[hsec, hph, norm_mul, mul_pow, show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) = Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring, Real.exp_add, Real.exp_log hgpos]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem api_nsq_eq (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hsec := hFs.2 i (A.pick x) x hxU hxs hj
  have hph := A.ph_trans la i (A.pick x) x hxs hj
  have hg := A.g_ne la i (A.pick x) x hxs hj
  have hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
  rw [hsec, hph, norm_mul, mul_pow,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hgpos]
  ring

/- English proof (translation)
Apply `api_contOn_chart A _ hU` to reduce the goal to its premises. Introduce `i`. Use `set e := A.chart i with he`. Establish `hF : ContinuousOn (F i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U)` using `(hFs.1 i).continuousOn`. Establish `hph : ContinuousOn (A.ph la i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U)` using `(A.smooth_ph la i).continuousOn.mono Set.inter_subset_left`.

Establish `hc : ContinuousOn (fun v => ‖F i (e.symm v)‖ ^ 2 * Real.exp (-A.ph la i (e.symm v))) (e.target ∩ e.symm ⁻¹' U)` using `(hF.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)`. Use `hc.congr ?_` and prove the remaining obligations. Introduce `v hv`. Conclude with `(api_nsq_eq A hFs (e.map_target hv.1) hv.2).symm`.
-/
theorem api_nsq_contOn (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} (hU : IsOpen U)
    {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) : ContinuousOn (A.nsq la F) U := by
  apply api_contOn_chart A _ hU
  intro i
  set e := A.chart i with he
  have hF : ContinuousOn (F i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := (hFs.1 i).continuousOn
  have hph : ContinuousOn (A.ph la i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (A.smooth_ph la i).continuousOn.mono Set.inter_subset_left
  have hc : ContinuousOn (fun v => ‖F i (e.symm v)‖ ^ 2 * Real.exp (-A.ph la i (e.symm v)))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hF.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine hc.congr ?_
  intro v hv
  exact (api_nsq_eq A hFs (e.map_target hv.1) hv.2).symm

end

end ReciprocityTheory.L2DbarEstimates.Y
