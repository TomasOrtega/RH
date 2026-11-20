import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegIndep
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollLeClosedBall
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegGlue

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

/- English proof (translation)
Distinguish the cases in `hr0 : 0 < r`. Use `⟨mollify n r u, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hx' : closedBall x r ⊆ Ω`. Use `(Metric.closedBall_subset_closedBall' ?_).trans hr` and prove the remaining obligations. Rewrite `hx` using `[Metric.mem_ball]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mollify_differentiableAt hΩ hu hw hr0 hx').differentiableWithinAt`. Rewrite using `[Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] filter_upwards [mollify_tendsto_ae hu] with x hx hxb`. Rewrite `hxb` using `[Metric.mem_ball]`. Establish `hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mollify n t u x = mollify n r u x` using `by filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr0)] with t ht1 ht2`.

Establish `ht1' : 0 < t` using `ht1`. Establish `ht2' : t < r` using `ht2`. Use `mollify_indep hΩ hu hw ht1' hr0 ((Metric.closedBall_subset_closedBall' ?_).trans hr)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (mollify n r u x))` using `tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)`.

Conclude with `tendsto_nhds_unique hx h2`. Establish `h0 : ball c r = ∅` using `Metric.ball_eq_empty.2 (not_lt.1 hr0)`. Use `⟨u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `differentiableOn_empty`.

Rewrite using `[h0, Measure.restrict_empty]`.
-/
theorem reg_ball {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω) (hu : Integrable u)
    (hw : WeakHolo Ω u) (c : V n) (r : ℝ) (hr : closedBall c (3 * r) ⊆ Ω) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] U := by
  by_cases hr0 : 0 < r
  · refine ⟨mollify n r u, fun x hx => ?_, ?_⟩
    · have hx' : closedBall x r ⊆ Ω := by
        refine (Metric.closedBall_subset_closedBall' ?_).trans hr
        rw [Metric.mem_ball] at hx; linarith
      exact (mollify_differentiableAt hΩ hu hw hr0 hx').differentiableWithinAt
    · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [mollify_tendsto_ae hu] with x hx hxb
      rw [Metric.mem_ball] at hxb
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mollify n t u x = mollify n r u x := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr0)] with t ht1 ht2
        have ht1' : 0 < t := ht1
        have ht2' : t < r := ht2
        refine mollify_indep hΩ hu hw ht1' hr0 ((Metric.closedBall_subset_closedBall' ?_).trans hr)
        linarith
      have h2 : Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (mollify n r u x)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
      exact tendsto_nhds_unique hx h2
  · have h0 : ball c r = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hr0)
    refine ⟨u, ?_, ?_⟩
    · rw [h0]; exact differentiableOn_empty
    · rw [h0, Measure.restrict_empty]

/- English proof (translation)
Introduce `n Ω u hΩ hw`. Apply `reg_glue hΩ` to reduce the goal to its premises. Introduce `x hx`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hΩ x hx`. Establish `hr0 : 0 < ε / 8` using `by positivity`.

Establish `h5 : closedBall x (5 * (ε / 8)) ⊆ Ω` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Establish `h4 : ball x (4 * (ε / 8)) ⊆ closedBall x (5 * (ε / 8))` using `Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))`. Establish `h4Ω : ball x (4 * (ε / 8)) ⊆ Ω` using `h4.trans h5`. Use `set u' := (closedBall x (5 * (ε / 8))).indicator u with hu'def`. Establish `hu' : Integrable u'`.

Rewrite using `[hu'def, integrable_indicator_iff measurableSet_closedBall]`. Conclude with `hw.1.integrableOn_compact_subset h5 (isCompact_closedBall _ _)`. Establish `hw' : WeakHolo (ball x (4 * (ε / 8))) u'`. Use `⟨hu'.locallyIntegrable.locallyIntegrableOn _, fun g hg v => ?_⟩` and prove the remaining obligations. Establish `hzero : ∀ z, z ∉ tsupport g → dbarDir g z v = 0`.

Introduce `z hz`. Establish `h0 : fderiv ℝ g z = 0`. Rewrite using `[(notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq]`. Simplify using the standard rewrite rules. Simplify using `[dbarDir, h0]`.

Establish `hts : tsupport g ⊆ ball x (4 * (ε / 8))` using `hg.2.2`. Establish `hpt : ∀ z, u' z * dbarDir g z v = u z * dbarDir g z v`. Introduce `z`. Distinguish the cases in `hz : z ∈ tsupport g`. Rewrite using `[hu'def, Set.indicator_of_mem (h4 (hts hz))]`.

Simplify using `[hzero z hz]`. Establish `h1` using `hw.2 g ⟨hg.1, hg.2.1, hts.trans h4Ω⟩ v`. Rewrite `h1` using `[setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hzero z (fun h => hz (hts.trans h4Ω h))])]`. Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hzero z (fun h => hz (hts h))])]`. Repeatedly rewrite using `[hpt]`.

Conclude with `h1`. Take `⟨U, hU, hae⟩` from `reg_ball (Ω := ball x (4 * (ε / 8))) Metric.isOpen_ball hu' hw' x (ε / 8) (Metric.closedBall_subset_ball (by linarith))`. Use `⟨ε / 8, hr0, (Metric.ball_subset_ball (by linarith)).trans h4Ω, U, hU, ?_⟩` and prove the remaining obligations. Use `Filter.EventuallyEq.trans ?_ hae` and prove the remaining obligations. Use `ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_)` and prove the remaining obligations.

Rewrite using `[hu'def, Set.indicator_of_mem (h4 (Metric.ball_subset_ball (by linarith) hz))]`.
-/
theorem reg : RegStatement := by
  intro n Ω u hΩ hw
  apply reg_glue hΩ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hr0 : 0 < ε / 8 := by positivity
  have h5 : closedBall x (5 * (ε / 8)) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have h4 : ball x (4 * (ε / 8)) ⊆ closedBall x (5 * (ε / 8)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h4Ω : ball x (4 * (ε / 8)) ⊆ Ω := h4.trans h5
  set u' := (closedBall x (5 * (ε / 8))).indicator u with hu'def
  have hu' : Integrable u' := by
    rw [hu'def, integrable_indicator_iff measurableSet_closedBall]
    exact hw.1.integrableOn_compact_subset h5 (isCompact_closedBall _ _)
  have hw' : WeakHolo (ball x (4 * (ε / 8))) u' := by
    refine ⟨hu'.locallyIntegrable.locallyIntegrableOn _, fun g hg v => ?_⟩
    have hzero : ∀ z, z ∉ tsupport g → dbarDir g z v = 0 := by
      intro z hz
      have h0 : fderiv ℝ g z = 0 := by
        rw [(notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq]; simp
      simp [dbarDir, h0]
    have hts : tsupport g ⊆ ball x (4 * (ε / 8)) := hg.2.2
    have hpt : ∀ z, u' z * dbarDir g z v = u z * dbarDir g z v := by
      intro z
      by_cases hz : z ∈ tsupport g
      · rw [hu'def, Set.indicator_of_mem (h4 (hts hz))]
      · simp [hzero z hz]
    have h1 := hw.2 g ⟨hg.1, hg.2.1, hts.trans h4Ω⟩ v
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts.trans h4Ω h))])] at h1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts h))])]
    simp_rw [hpt]
    exact h1
  obtain ⟨U, hU, hae⟩ := reg_ball (Ω := ball x (4 * (ε / 8))) Metric.isOpen_ball hu' hw' x (ε / 8)
    (Metric.closedBall_subset_ball (by linarith))
  refine ⟨ε / 8, hr0, (Metric.ball_subset_ball (by linarith)).trans h4Ω, U, hU, ?_⟩
  refine Filter.EventuallyEq.trans ?_ hae
  refine ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_)
  rw [hu'def, Set.indicator_of_mem (h4 (Metric.ball_subset_ball (by linarith) hz))]

end ReciprocityTheory.L2DbarEstimates.C
