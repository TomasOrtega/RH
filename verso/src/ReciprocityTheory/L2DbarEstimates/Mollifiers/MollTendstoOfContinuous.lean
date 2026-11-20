import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

/- English proof (translation)
Establish `hgu : UniformContinuous g` using `hgs.uniformContinuous_of_continuous hgc`. Use `set S := Metric.cthickening 1 (tsupport g) with hS`. Establish `hSc : IsCompact S` using `hgs.isCompact.cthickening`. Use `set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC`. Establish `hCfin : C ≠ (⊤ : ℝ≥0∞)` using `ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne`.

Establish `hgm : AEStronglyMeasurable g μ` using `hgc.aestronglyMeasurable`. Establish `key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ`. Introduce `δ hδ`. Take `⟨ρ, hρ, hρg⟩` from `Metric.uniformContinuous_iff.1 hgu δ hδ`. Use `filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi`.

Establish `hr : (K i).r < ρ` using `lt_of_lt_of_le hi (min_le_left _ _)`. Establish `hr1 : (K i).r < 1` using `lt_of_lt_of_le hi (min_le_right _ _)`. Establish `hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ`. Introduce `x`. Rewrite using `[Pi.sub_apply, ← dist_eq_norm]`.

Simplify using `only [moll]`. Conclude with `dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)`. Establish `hsupp : Function.support (moll (K i) g - g) ⊆ S`. Introduce `x hx`. Assume the negation of the conclusion as `hxS`.

Apply `hx` to reduce the goal to its premises. Establish `hx0 : ∀ y ∈ ball x (K i).r, g y = 0`. Introduce `y hy`. Assume the negation of the conclusion as `hy0`. Apply `hxS` to reduce the goal to its premises.

Use `Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_` and prove the remaining obligations. Rewrite using `[dist_comm]`. Conclude with `le_of_lt (lt_trans (mem_ball.1 hy) hr1)`. Establish `hgx : g x = 0` using `hx0 x (mem_ball_self (K i).r_pos)`. Establish `h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0`.

Simplify using `only [moll]`. Conclude with `dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm (fun y hy => by rw [hx0 y hy, dist_self])`. Rewrite using `[Pi.sub_apply, hgx, sub_zero]`. Conclude with `dist_le_zero.1 h0`. Rewrite using `[← eLpNorm_restrict_eq_of_support_subset hsupp]`.

Use `(eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hbound)).trans ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply_univ]`. Rewrite using `[ENNReal.tendsto_nhds_zero]`. Introduce `ε hε`. Take `⟨n, hn, hnε⟩` from `ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'`.

Use `filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi`. Use `hi.trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_coe_nnreal, mul_comm]`. Conclude with `hnε.le`.
-/
theorem moll_tendsto_of_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by
  have hgu : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
  set S := Metric.cthickening 1 (tsupport g) with hS
  have hSc : IsCompact S := hgs.isCompact.cthickening
  set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hCfin : C ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne
  have hgm : AEStronglyMeasurable g μ := hgc.aestronglyMeasurable
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1 hgu δ hδ
    filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi
    have hr : (K i).r < ρ := lt_of_lt_of_le hi (min_le_left _ _)
    have hr1 : (K i).r < 1 := lt_of_lt_of_le hi (min_le_right _ _)
    have hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      simp only [moll]
      exact dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
        (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)
    have hsupp : Function.support (moll (K i) g - g) ⊆ S := by
      intro x hx
      by_contra hxS
      apply hx
      have hx0 : ∀ y ∈ ball x (K i).r, g y = 0 := by
        intro y hy
        by_contra hy0
        apply hxS
        refine Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_
        rw [dist_comm]; exact le_of_lt (lt_trans (mem_ball.1 hy) hr1)
      have hgx : g x = 0 := hx0 x (mem_ball_self (K i).r_pos)
      have h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0 := by
        simp only [moll]
        exact dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
          (fun y hy => by rw [hx0 y hy, dist_self])
      rw [Pi.sub_apply, hgx, sub_zero]
      exact dist_le_zero.1 h0
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'
  filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi
  refine hi.trans ?_
  rw [ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hnε.le

/- English proof (translation)
Introduce `l K hK u hu`. Rewrite using `[ENNReal.tendsto_nhds_zero]`. Introduce `ε hε`. Establish `hη : ε / 3 ≠ 0` using `(ENNReal.div_pos hε.ne' (by simp)).ne'`. Take `⟨g, hgs, hug, hgc, hgL⟩` from `hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη`.

Establish `hmid` using `moll_tendsto_of_continuous E μ hK hgs hgc`. Rewrite `hmid` using `[ENNReal.tendsto_nhds_zero]`. Use `filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi`. Establish `hcs : HasCompactSupport (K i).toFun` using `HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by`. Assume the negation of the conclusion as `h`.

Conclude with `hx (ball_subset_closedBall ((K i).support_subset h)))`. Establish `hKc : Continuous (K i).toFun` using `(K i).smooth.continuous`. Establish `hug' : MemLp (u - g) 2 μ` using `hu.sub hgL`. Establish `hli : LocallyIntegrable (u - g) μ` using `hug'.locallyIntegrable (by norm_num)`. Establish `hgli : LocallyIntegrable g μ` using `hgL.locallyIntegrable (by norm_num)`.

Establish `hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g`. Simplify using `only [moll]`. Rewrite using `[← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli) (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]`. Establish `hc1 : Continuous (moll (K i) (u - g))` using `hcs.continuous_convolution_left _ hKc hli`. Establish `hc2 : Continuous (moll (K i) g)` using `hcs.continuous_convolution_left _ hKc hgli`.

Establish `hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u)`. Rewrite using `[hlin]`. Normalize the expressions using the abelian group laws. Establish `hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ`. Establish `h` using `moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable`.

Establish `hth : thickening (K i).r (Set.univ : Set E) = Set.univ` using `Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)`. Simplify using `only [hth, Measure.restrict_univ] at h`. Conclude with `h`. Rewrite using `[hdec]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `eLpNorm_add_le hc1.aestronglyMeasurable (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable) (by norm_num)`. Use `_ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr`. Conclude with `hY.trans hug`. Rewrite using `[eLpNorm_sub_comm]`. Conclude with `hug`.

Use `_ = ε := ENNReal.add_thirds ε`.
-/
theorem moll_l2Tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : MollifierL2Tendsto E μ ι := by
  intro l K hK u hu
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hη : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by simp)).ne'
  obtain ⟨g, hgs, hug, hgc, hgL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη
  have hmid := moll_tendsto_of_continuous E μ hK hgs hgc
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi
  have hcs : HasCompactSupport (K i).toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((K i).support_subset h)))
  have hKc : Continuous (K i).toFun := (K i).smooth.continuous
  have hug' : MemLp (u - g) 2 μ := hu.sub hgL
  have hli : LocallyIntegrable (u - g) μ := hug'.locallyIntegrable (by norm_num)
  have hgli : LocallyIntegrable g μ := hgL.locallyIntegrable (by norm_num)
  have hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g := by
    simp only [moll]
    rw [← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli)
      (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]
  have hc1 : Continuous (moll (K i) (u - g)) := hcs.continuous_convolution_left _ hKc hli
  have hc2 : Continuous (moll (K i) g) := hcs.continuous_convolution_left _ hKc hgli
  have hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u) := by
    rw [hlin]; abel
  have hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ := by
    have h := moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable
    have hth : thickening (K i).r (Set.univ : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)
    simp only [hth, Measure.restrict_univ] at h
    exact h
  rw [hdec]
  calc eLpNorm (moll (K i) (u - g) + (moll (K i) g - g) + (g - u)) 2 μ
      ≤ eLpNorm (moll (K i) (u - g) + (moll (K i) g - g)) 2 μ + eLpNorm (g - u) 2 μ :=
        eLpNorm_add_le (hc1.aestronglyMeasurable.add (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable))
          (hgc.aestronglyMeasurable.sub hu.aestronglyMeasurable) (by norm_num)
    _ ≤ eLpNorm (moll (K i) (u - g)) 2 μ + eLpNorm (moll (K i) g - g) 2 μ + eLpNorm (g - u) 2 μ := by
        gcongr
        exact eLpNorm_add_le hc1.aestronglyMeasurable
          (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable) (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hY.trans hug
        · rw [eLpNorm_sub_comm]; exact hug
    _ = ε := ENNReal.add_thirds ε

end ReciprocityTheory.L2DbarEstimates.B
