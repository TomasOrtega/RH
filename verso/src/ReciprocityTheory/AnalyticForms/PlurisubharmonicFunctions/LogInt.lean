import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogIntSt

open MeasureTheory Set

namespace ReciprocityTheory.AnForm.A

/- English proof (translation)
Introduce `x`. Establish `hmeas : MeasurableSet (Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ)))` using `MeasurableSet.univ_pi (fun j => measurableSet_closedBall)`. Use `⟨Set.pi Set.univ (fun j => Metric.closedBall (x j) 1), set_pi_mem_nhds Set.finite_univ (fun j _ => Metric.closedBall_mem_nhds (x j) one_pos), ?_⟩` and prove the remaining obligations. Rewrite using `[← integrable_indicator_iff hmeas]`. Establish `hf : ∀ j : Fin D, Integrable (fun w : ℂ => if j = i then (Metric.closedBall (x j) 1).indicator g w else (Metric.closedBall (x j) 1).indicator (fun _ => (1 : ℝ)) w) volume`.

Introduce `j`. Use `split_ifs`. Conclude with `(integrable_indicator_iff measurableSet_closedBall).mpr (hg.integrableOn_isCompact (isCompact_closedBall _ _))`. Conclude with `(integrable_indicator_iff measurableSet_closedBall).mpr ((locallyIntegrable_const (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall _ _))`. Establish `hI` using `Integrable.fintype_prod (μ := fun _ : Fin D => (volume : Measure ℂ)) hf`.

Rewrite using `[volume_pi]`. Use `hI.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `hz : z ∈ Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))`. Rewrite using `[Set.indicator_apply, if_pos hz]`.

Rewrite `hz` using `[Set.mem_univ_pi]`. Rewrite using `[Finset.prod_eq_single i]`. Simplify using `[Set.indicator_apply, hz i]`. Introduce `j _ hj`. Simplify using `[hj, Set.indicator_apply, hz j]`.

Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_apply, if_neg hz]`. Rewrite `hz` using `[Set.mem_univ_pi]`. Use `push_neg at hz`. Take `⟨j, hj⟩` from `hz`.

Apply the tactic sequence `exact Finset.prod_eq_zero (Finset.mem_univ j) (by split_ifs <;> simp [Set.indicator_apply, hj])`.
-/
theorem locallyIntegrable_comp_eval_fin {D : ℕ} (i : Fin D) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun z : Fin D → ℂ => g (z i)) volume := by
  classical
  intro x
  have hmeas : MeasurableSet (Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))) :=
    MeasurableSet.univ_pi (fun j => measurableSet_closedBall)
  refine ⟨Set.pi Set.univ (fun j => Metric.closedBall (x j) 1),
    set_pi_mem_nhds Set.finite_univ (fun j _ => Metric.closedBall_mem_nhds (x j) one_pos), ?_⟩
  rw [← integrable_indicator_iff hmeas]
  have hf : ∀ j : Fin D, Integrable (fun w : ℂ => if j = i then (Metric.closedBall (x j) 1).indicator g w
      else (Metric.closedBall (x j) 1).indicator (fun _ => (1 : ℝ)) w) volume := by
    intro j
    split_ifs
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (hg.integrableOn_isCompact (isCompact_closedBall _ _))
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        ((locallyIntegrable_const (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall _ _))
  have hI := Integrable.fintype_prod (μ := fun _ : Fin D => (volume : Measure ℂ)) hf
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  by_cases hz : z ∈ Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))
  · rw [Set.indicator_apply, if_pos hz]
    rw [Set.mem_univ_pi] at hz
    rw [Finset.prod_eq_single i]
    · simp [Set.indicator_apply, hz i]
    · intro j _ hj
      simp [hj, Set.indicator_apply, hz j]
    · simp
  · rw [Set.indicator_apply, if_neg hz]
    rw [Set.mem_univ_pi] at hz
    push_neg at hz
    obtain ⟨j, hj⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by split_ifs <;> simp [Set.indicator_apply, hj])

/- English proof (translation)
Introduce `x`. Use `⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1, prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩` and prove the remaining obligations. Rewrite using `[← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall), Measure.volume_eq_prod]`. Establish `h1` using `(integrable_indicator_iff measurableSet_closedBall).mpr (hg.integrableOn_isCompact (isCompact_closedBall x.1 1))`. Establish `h2` using `(integrable_indicator_iff measurableSet_closedBall).mpr ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall x.2 1))`.

Use `(h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>`. Simplify using `[Set.indicator_apply, Set.mem_prod, ha, hb]`.
-/
theorem locallyIntegrable_comp_fst_real {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.1) volume := by
  intro x
  refine ⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rw [← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall),
    Measure.volume_eq_prod]
  have h1 := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hg.integrableOn_isCompact (isCompact_closedBall x.1 1))
  have h2 := (integrable_indicator_iff measurableSet_closedBall).mpr
    ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact
      (isCompact_closedBall x.2 1))
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>
    simp [Set.indicator_apply, Set.mem_prod, ha, hb]

/- English proof (translation)
Introduce `x`. Use `⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1, prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩` and prove the remaining obligations. Rewrite using `[← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall), Measure.volume_eq_prod]`. Establish `h1` using `(integrable_indicator_iff measurableSet_closedBall).mpr ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall x.1 1))`. Establish `h2` using `(integrable_indicator_iff measurableSet_closedBall).mpr (hg.integrableOn_isCompact (isCompact_closedBall x.2 1))`.

Use `(h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>`. Simplify using `[Set.indicator_apply, Set.mem_prod, ha, hb]`.
-/
theorem locallyIntegrable_comp_snd_real {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.2) volume := by
  intro x
  refine ⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rw [← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall),
    Measure.volume_eq_prod]
  have h1 := (integrable_indicator_iff measurableSet_closedBall).mpr
    ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact
      (isCompact_closedBall x.1 1))
  have h2 := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hg.integrableOn_isCompact (isCompact_closedBall x.2 1))
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>
    simp [Set.indicator_apply, Set.mem_prod, ha, hb]

/- English proof (translation)
Introduce `x`. Use `⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩` and prove the remaining obligations. Conclude with `(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp intervalIntegral.intervalIntegrable_log'`.
-/
theorem locallyIntegrable_real_log : LocallyIntegrable Real.log volume := by
  intro x
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    intervalIntegral.intervalIntegrable_log'

/- English proof (translation)
Introduce `x`. Take `⟨s, hs, h⟩` from `locallyIntegrable_real_log x`. Conclude with `⟨s, hs, h.norm⟩`.
-/
theorem locallyIntegrable_norm_real_log : LocallyIntegrable (fun x : ℝ => ‖Real.log x‖) volume := by
  intro x
  obtain ⟨s, hs, h⟩ := locallyIntegrable_real_log x
  exact ⟨s, hs, h.norm⟩

/- English proof (translation)
Simplify using `only [Real.norm_eq_abs]`. Establish `hre` using `Complex.abs_re_le_norm z`. Establish `him` using `Complex.abs_im_le_norm z`. Establish `hsum` using `Complex.norm_le_abs_re_add_abs_im z`. Establish `a1` using `abs_nonneg (Real.log z.re)`.

Establish `a2` using `abs_nonneg (Real.log z.im)`. Establish `a3` using `abs_nonneg z.re`. Establish `a4` using `abs_nonneg z.im`. Break down `le_or_gt 1 ‖z‖ with h1 | h1` into its components or cases. Establish `h2` using `Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ‖z‖)`.

Rewrite using `[abs_of_nonneg (Real.log_nonneg h1)]`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `eq_or_lt_of_le (norm_nonneg z) with h0 | h0` into its components or cases. Rewrite using `[← h0, Real.log_zero, abs_zero]`. Check the signs of the components of the expression.

Rewrite using `[abs_of_neg (Real.log_neg h0 h1)]`. Distinguish the cases in `hr : z.re = 0`. Establish `hi : z.im ≠ 0`. Introduce `hi`. Establish `hz : z = 0` using `Complex.ext hr hi`.

Rewrite `h0` using `[hz, norm_zero]`. Conclude with `lt_irrefl _ h0`. Establish `h3 : Real.log |z.im| ≤ Real.log ‖z‖` using `Real.log_le_log (abs_pos.mpr hi) him`. Rewrite `h3` using `[Real.log_abs]`. Establish `h4` using `neg_le_abs (Real.log z.im)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : Real.log |z.re| ≤ Real.log ‖z‖` using `Real.log_le_log (abs_pos.mpr hr) hre`. Rewrite `h3` using `[Real.log_abs]`. Establish `h4` using `neg_le_abs (Real.log z.re)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_log_norm_le (z : ℂ) :
    ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by
  simp only [Real.norm_eq_abs]
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hsum := Complex.norm_le_abs_re_add_abs_im z
  have a1 := abs_nonneg (Real.log z.re)
  have a2 := abs_nonneg (Real.log z.im)
  have a3 := abs_nonneg z.re
  have a4 := abs_nonneg z.im
  rcases le_or_gt 1 ‖z‖ with h1 | h1
  · have h2 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ‖z‖)
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith
  · rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
    · rw [← h0, Real.log_zero, abs_zero]
      positivity
    · rw [abs_of_neg (Real.log_neg h0 h1)]
      by_cases hr : z.re = 0
      · have hi : z.im ≠ 0 := by
          intro hi
          have hz : z = 0 := Complex.ext hr hi
          rw [hz, norm_zero] at h0
          exact lt_irrefl _ h0
        have h3 : Real.log |z.im| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hi) him
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.im)
        linarith
      · have h3 : Real.log |z.re| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hr) hre
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.re)
        linarith

/- English proof (translation)
Establish `hH : LocallyIntegrable (fun p : ℝ × ℝ => ‖Real.log p.1‖ + ‖Real.log p.2‖ + ‖p.1‖ + ‖p.2‖) volume` using `(((locallyIntegrable_comp_fst_real locallyIntegrable_norm_real_log).add (locallyIntegrable_comp_snd_real locallyIntegrable_norm_real_log)).add (locallyIntegrable_comp_fst_real (continuous_norm (E := ℝ)).locallyIntegrable)).add (locallyIntegrable_comp_snd_real (continuous_norm (E …`. Establish `hG : LocallyIntegrable (fun z : ℂ => ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖) volume`. Introduce `x`. Take `⟨s, hs, hint⟩` from `hH (Complex.measurableEquivRealProd x)`. Establish `hcont : Continuous (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ)` using `by show Continuous fun z : ℂ => (z.re, z.im) fun_prop`.

Use `⟨Complex.measurableEquivRealProd ⁻¹' s, hcont.continuousAt.preimage_mem_nhds hs, ?_⟩` and prove the remaining obligations. Conclude with `(Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage Complex.measurableEquivRealProd.measurableEmbedding).mpr hint`. Use `hG.mono (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `h1` using `norm_log_norm_le z`. Establish `h2 : 0 ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem logNormLocIntC_thm : LogNormLocIntCStatement := by
  have hH : LocallyIntegrable
      (fun p : ℝ × ℝ => ‖Real.log p.1‖ + ‖Real.log p.2‖ + ‖p.1‖ + ‖p.2‖) volume :=
    (((locallyIntegrable_comp_fst_real locallyIntegrable_norm_real_log).add
      (locallyIntegrable_comp_snd_real locallyIntegrable_norm_real_log)).add
      (locallyIntegrable_comp_fst_real (continuous_norm (E := ℝ)).locallyIntegrable)).add
      (locallyIntegrable_comp_snd_real (continuous_norm (E := ℝ)).locallyIntegrable)
  have hG : LocallyIntegrable
      (fun z : ℂ => ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖) volume := by
    intro x
    obtain ⟨s, hs, hint⟩ := hH (Complex.measurableEquivRealProd x)
    have hcont : Continuous (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) := by
      show Continuous fun z : ℂ => (z.re, z.im)
      fun_prop
    refine ⟨Complex.measurableEquivRealProd ⁻¹' s, hcont.continuousAt.preimage_mem_nhds hs, ?_⟩
    exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hint
  refine hG.mono (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have h1 := norm_log_norm_le z
  have h2 : 0 ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by positivity
  calc ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := h1
    _ = ‖‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖‖ := (Real.norm_of_nonneg h2).symm

/- English proof (translation)
Introduce `D i` and use `locallyIntegrable_comp_eval_fin i logNormLocIntC_thm`.
-/
theorem logCoordLocInt_thm : LogCoordLocIntStatement := fun D i => locallyIntegrable_comp_eval_fin i logNormLocIntC_thm

/- English proof (translation)
Introduce `D m`. Conclude with `locallyIntegrable_finset_sum (μ := volume) Finset.univ (f := fun i (z : Fin D → ℂ) => (m i : ℝ) * Real.log ‖z i‖) (fun i _ => (logCoordLocInt_thm D i).smul (m i : ℝ))`.
-/
theorem logMonoLocInt_thm : LogMonoLocIntStatement := by
  intro D m
  exact locallyIntegrable_finset_sum (μ := volume) Finset.univ
    (f := fun i (z : Fin D → ℂ) => (m i : ℝ) * Real.log ‖z i‖)
    (fun i _ => (logCoordLocInt_thm D i).smul (m i : ℝ))

/- English proof (translation)
Introduce `D m f hf hfs`. Conclude with `(logMonoLocInt_thm D m).integrable_smul_left_of_hasCompactSupport hf hfs`.
-/
theorem logMonoTestInt_thm : LogMonoTestIntStatement := by
  intro D m f hf hfs
  exact (logMonoLocInt_thm D m).integrable_smul_left_of_hasCompactSupport hf hfs

/- English proof (translation)
Rewrite using `[norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz i)))]`. Unfold `logMono`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_zpow, Real.log_zpow]`.
-/
theorem log_norm_prod_zpow_eq_logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ)
    (hz : ∀ i, z i ≠ 0) : Real.log ‖∏ i, z i ^ m i‖ = logMono m z := by
  rw [norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz i)))]
  unfold logMono
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]

/- English proof (translation)
Introduce `D m U u hU hu hu0`. Establish `hc : ContinuousOn (fun z => Real.log ‖u z‖) U` using `(hu.continuousOn.norm).log (fun z hz => norm_ne_zero_iff.mpr (hu0 z hz))`. Establish `h1 : LocallyIntegrableOn (fun z => Real.log ‖u z‖ + logMono m z) U volume` using `(hc.locallyIntegrableOn hU.measurableSet).add ((logMonoLocInt_thm D m).locallyIntegrableOn U)`. Establish `hnull : ∀ᵐ z ∂(volume : Measure (Fin D → ℂ)), ∀ i, z i ≠ 0`. Rewrite using `[ae_all_iff]`.

Introduce `i`. Establish `hs : (volume : Measure (Fin D → ℂ)) ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) : Set (Fin D → ℂ)) = 0`. Apply `Measure.addHaar_submodule` to reduce the goal to its premises. Introduce `htop`. Establish `h2 : (Pi.single i (1 : ℂ) : Fin D → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ)`.

Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Simplify using `at h2`. Establish `hset : {a : Fin D → ℂ | ¬ a i ≠ 0} = ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) : Set (Fin D → ℂ))`. Use extensionality with `z`.

Simplify using the standard rewrite rules. Rewrite using `[ae_iff, hset]`. Conclude with `hs`. Rewrite `h1`, the goal using `[locallyIntegrableOn_iff hU.isLocallyClosed]`. Introduce `K hKU hK`.

Use `(h1 K hKU hK).congr_fun_ae ?_` and prove the remaining obligations. Rewrite using `[Filter.EventuallyEq, ae_restrict_iff' hK.isClosed.measurableSet]`. Use `filter_upwards [hnull] with z hz hzK`. Establish `hzU` using `hKU hzK`. Use `show Real.log ‖u z‖ + logMono m z = Real.log ‖u z * ∏ i, z i ^ m i‖`.

Rewrite using `[norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hu0 z hzU)) (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hz i))), log_norm_prod_zpow_eq_logMono m z hz]`.
-/
theorem logUnitMonoLocInt_thm : LogUnitMonoLocIntStatement := by
  intro D m U u hU hu hu0
  have hc : ContinuousOn (fun z => Real.log ‖u z‖) U :=
    (hu.continuousOn.norm).log (fun z hz => norm_ne_zero_iff.mpr (hu0 z hz))
  have h1 : LocallyIntegrableOn (fun z => Real.log ‖u z‖ + logMono m z) U volume :=
    (hc.locallyIntegrableOn hU.measurableSet).add ((logMonoLocInt_thm D m).locallyIntegrableOn U)
  have hnull : ∀ᵐ z ∂(volume : Measure (Fin D → ℂ)), ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have hs : (volume : Measure (Fin D → ℂ))
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) = 0 := by
      apply Measure.addHaar_submodule
      intro htop
      have h2 : (Pi.single i (1 : ℂ) : Fin D → ℂ) ∈
          LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) := by
        rw [htop]
        exact Submodule.mem_top
      simp at h2
    have hset : {a : Fin D → ℂ | ¬ a i ≠ 0} =
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) := by
      ext z
      simp
    rw [ae_iff, hset]
    exact hs
  rw [locallyIntegrableOn_iff hU.isLocallyClosed] at h1 ⊢
  intro K hKU hK
  refine (h1 K hKU hK).congr_fun_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hK.isClosed.measurableSet]
  filter_upwards [hnull] with z hz hzK
  have hzU := hKU hzK
  show Real.log ‖u z‖ + logMono m z = Real.log ‖u z * ∏ i, z i ^ m i‖
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hu0 z hzU))
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hz i))),
    log_norm_prod_zpow_eq_logMono m z hz]

end ReciprocityTheory.AnForm.A
