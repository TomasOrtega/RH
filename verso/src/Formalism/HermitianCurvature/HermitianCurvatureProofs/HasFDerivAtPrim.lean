import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtTMul

open Set Filter Topology MeasureTheory intervalIntegral Metric

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def seg (w₀ x : ℂ) (t : ℝ) : ℂ := w₀ + (t : ℂ) * (x - w₀)

/- English proof (translation)
Establish `h` using `hc.add_smul_sub_mem hw₀ hx ht`. Simplify `h` using `[seg, Complex.real_smul]`.
-/
theorem seg_mem (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by
  have h := hc.add_smul_sub_mem hw₀ hx ht
  simpa [seg, Complex.real_smul] using h

/- English proof (translation)
Simplify using `[seg]`.
-/
theorem seg_one (w₀ x : ℂ) : seg w₀ x 1 = x := by
  simp [seg]

/- English proof (translation)
Unfold `seg`. Use `fun_prop`.
-/
theorem continuous_seg : Continuous fun p : ℂ × ℝ => seg w₀ p.1 p.2 := by
  unfold seg
  fun_prop

/- English proof (translation)
Establish `h` using `((hasDerivAt_id t).ofReal_comp.mul_const (x - w₀)).const_add w₀`. Simplify `h` using `[seg]`.
-/
theorem hasDerivAt_seg (x : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => seg w₀ x s) (x - w₀) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const (x - w₀)).const_add w₀
  simpa [seg] using h

/- English proof (translation)
Establish `h` using `((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)`. Establish `h2` using `h.const_add w₀`. Establish `hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y`. Use function extensionality and compare the values at `y`. Simplify using `[seg, smul_eq_mul]`.

Rewrite using `[hf]`. Conclude with `h2`.
-/
theorem hasFDerivAt_seg (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)
  have h2 := h.const_add w₀
  have hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y := by
    funext y
    simp [seg, smul_eq_mul]
  rw [hf]
  exact h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prim_eq (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) :
    prim ω w₀ w = ∫ t in (0 : ℝ)..1, ω (seg w₀ w t) (w - w₀) := rfl

/- English proof (translation)
Establish `hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p` using `fun p hp => (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt`. Establish `hcontω : ContinuousOn ω S` using `hω.continuousOn`. Establish `hcontD : ContinuousOn (fderiv ℝ ω) S` using `hω.continuousOn_fderiv_of_isOpen hS le_rfl`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.mp hS w hw`. Use `set δ' := δ / 2 with hδ'`.

Establish `hδ'0 : 0 < δ'` using `by positivity`. Establish `hcb : closedBall w δ' ⊆ S` using `(closedBall_subset_ball (by linarith)).trans hball`. Use `set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK`. Establish `hKc : IsCompact K` using `((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg`. Establish `hKS : K ⊆ S`.

Introduce and unpack `_ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩`. Conclude with `seg_mem hc hw₀ (hcb hx) ht`. Establish `hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K` using `fun x hx t ht => ⟨(x, t), ⟨hx, ht⟩, rfl⟩`. Take `⟨M₁, hM₁⟩` from `hKc.exists_bound_of_continuousOn (hcontω.mono hKS)`. Take `⟨M₂, hM₂⟩` from `hKc.exists_bound_of_continuousOn (hcontD.mono hKS)`.

Use `set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀) with hF'`. Establish `hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x`. Introduce `x hx t ht`. Establish `hs` using `hmemK x hx t ht`. Establish `hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x` using `(hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)`.

Establish `hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x` using `(hasFDerivAt_id x).sub_const w₀`. Establish `h` using `hc1.clm_apply hu`. Use `h.congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `h'`. Simplify using `only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]`.

Rewrite using `[show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]`. Simplify using the standard rewrite rules. Establish `hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1)` using `fun x _ => (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn`. Establish `hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1)` using `fun x hx => hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)`. Establish `hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1)` using `fun x hx => hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)`.

Establish `hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1)`. Introduce `x hx`. Use `(hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)` and prove the remaining obligations. Conclude with `((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const`. Establish `hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1` using `uIoc_of_le zero_le_one`.

Establish `hwc : w ∈ closedBall w δ'` using `mem_closedBall_self hδ'0.le`. Establish `hLeib` using `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1) (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_cons …`. Establish `hint : ∫ t in (0 : ℝ)..1, F' w t = ω w`. Establish `hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1)`. Introduce `t ht`.

Rewrite `ht` using `[uIcc_of_le zero_le_one]`. Establish `hs` using `hKS (hmemK w hwc t ht)`. Simplify using `only [hF']`. Use `congr 2`. Use extensionality with `h'`.

Simplify using `only [ContinuousLinearMap.flip_apply]`. Conclude with `hsym _ hs h' (w - w₀)`. Rewrite using `[intervalIntegral.integral_congr hEq]`. Establish `hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s)) (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t`. Introduce `t ht`.

Rewrite `ht` using `[uIcc_of_le zero_le_one]`. Establish `hs` using `hKS (hmemK w hwc t ht)`. Establish `h1` using `(hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)`. Establish `h2` using `(hasDerivAt_id t).smul h1`. Use `h2.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [id, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1)`. Rewrite using `[uIcc_of_le zero_le_one]`. Conclude with `(hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))`.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]`. Simplify using `[seg_one]`. Rewrite using `[← hint]`. Conclude with `hLeib`. Use `filter_upwards [ball_mem_nhds w hδ'0] with x hx`.

Establish `hxc : x ∈ closedBall w δ'` using `ball_subset_closedBall hx`. Rewrite using `[hIoc]`. Conclude with `(((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc`. Use `ContinuousOn.intervalIntegrable ?_` and prove the remaining obligations. Rewrite using `[uIcc_of_le zero_le_one]`.

Conclude with `(hωseg w hwc).clm_apply continuousOn_const`. Rewrite using `[hIoc]`. Conclude with `((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc`. Use `Eventually.of_forall fun t ht x hx => ?_` and prove the remaining obligations. Rewrite `ht` using `[hIoc]`.

Establish `ht' : t ∈ Icc (0 : ℝ) 1` using `Ioc_subset_Icc_self ht`. Establish `hxc : x ∈ closedBall w δ'` using `ball_subset_closedBall hx`. Establish `hs` using `hmemK x hxc t ht'`. Establish `h1 : ‖ω (seg w₀ x t)‖ ≤ M₁` using `hM₁ _ hs`. Establish `h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂` using `hM₂ _ hs`.

Establish `h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖`. Use `norm_sub_le_norm_sub_add_norm_sub x w w₀` as an intermediate fact. Establish `hxw : ‖x - w‖ ≤ δ'` using `by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM₂0 : 0 ≤ M₂` using `le_trans (norm_nonneg _) h2`.

Simplify using `only [hF']`. Combine the equalities or inequalities in the displayed calculation. Use `add_le_add h1 ?_` and prove the remaining obligations. Rewrite using `[norm_smul]`. Establish `hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖)`.

Use `((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.opNorm_flip]`. Conclude with `mul_le_mul h2 h3 (norm_nonneg _) hM₂0`. Establish `ht1 : ‖t‖ ≤ 1` using `by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2`. Combine the equalities or inequalities in the displayed calculation.

Use `Eventually.of_forall fun t ht x hx => ?_` and prove the remaining obligations. Rewrite `ht` using `[hIoc]`. Conclude with `hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)`.
-/
theorem hasFDerivAt_prim (hS : IsOpen S) (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) (hω : ContDiffOn ℝ 1 ω S)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} (hw : w ∈ S) :
    HasFDerivAt (prim ω w₀) (ω w) w := by
  have hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p := fun p hp =>
    (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt
  have hcontω : ContinuousOn ω S := hω.continuousOn
  have hcontD : ContinuousOn (fderiv ℝ ω) S := hω.continuousOn_fderiv_of_isOpen hS le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS w hw
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hcb : closedBall w δ' ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
  set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg
  have hKS : K ⊆ S := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact seg_mem hc hw₀ (hcb hx) ht
  have hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K := fun x hx t ht =>
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hcontω.mono hKS)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcontD.mono hKS)
  set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)
    with hF'
  have hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x := by
    intro x hx t ht
    have hs := hmemK x hx t ht
    have hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)
    have hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const w₀
    have h := hc1.clm_apply hu
    refine h.congr_fderiv ?_
    ext h'
    simp only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
    rw [show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]
    simp
  have hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1) := fun x _ =>
    (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine (hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hwc : w ∈ closedBall w δ' := mem_closedBall_self hδ'0.le
  have hLeib := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1)
    (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have hint : ∫ t in (0 : ℝ)..1, F' w t = ω w := by
      have hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        simp only [hF']
        congr 2
        ext h'
        simp only [ContinuousLinearMap.flip_apply]
        exact hsym _ hs h' (w - w₀)
      rw [intervalIntegral.integral_congr hEq]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s))
          (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        have h1 := (hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)
        have h2 := (hasDerivAt_id t).smul h1
        refine h2.congr_deriv ?_
        simp only [id, one_smul]
        abel
      have hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact (hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]
      simp [seg_one]
    rw [← hint]
    exact hLeib
  · filter_upwards [ball_mem_nhds w hδ'0] with x hx
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    rw [hIoc]
    exact (((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hωseg w hwc).clm_apply continuousOn_const
  · rw [hIoc]
    exact ((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    have hs := hmemK x hxc t ht'
    have h1 : ‖ω (seg w₀ x t)‖ ≤ M₁ := hM₁ _ hs
    have h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂ := hM₂ _ hs
    have h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w₀
      have hxw : ‖x - w‖ ≤ δ' := by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc
      linarith
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    simp only [hF']
    calc ‖ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖
        ≤ ‖ω (seg w₀ x t)‖ + ‖t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ := norm_add_le _ _
      _ ≤ M₁ + M₂ * (δ' + ‖w - w₀‖) := by
        refine add_le_add h1 ?_
        rw [norm_smul]
        have hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖) := by
          refine ((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul h2 h3 (norm_nonneg _) hM₂0
        have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
        calc ‖t‖ * ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ 1 * (M₂ * (δ' + ‖w - w₀‖)) :=
              mul_le_mul ht1 hf (norm_nonneg _) zero_le_one
          _ = M₂ * (δ' + ‖w - w₀‖) := one_mul _
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    exact hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
