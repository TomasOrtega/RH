import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation

noncomputable section

open MeasureTheory Filter Topology Set
open scoped SchwartzMap

namespace GlobalTheory.SchwartzPettis

/- English proof (translation)
Use `borelize C(K, W)`. Establish `hb : ∀ (b : C(K, W)) (r : ℝ), 0 ≤ r → NullMeasurableSet (h ⁻¹' Metric.closedBall b r) μ`. Introduce `b r hr`. Take `⟨D, hDc, hD⟩` from `TopologicalSpace.exists_countable_dense K`. Establish `e : h ⁻¹' Metric.closedBall b r = ⋂ x ∈ D, (fun t => ‖h t x - b x‖) ⁻¹' Iic r`.

Use extensionality with `t`. Rewrite using `[mem_preimage, Metric.mem_closedBall, ContinuousMap.dist_le hr]`. Simplify using `only [mem_preimage, mem_iInter, mem_Iic, dist_eq_norm]`. Use `⟨fun H x _ => H x, fun H x => ?_⟩` and prove the remaining obligations. Conclude with `(isClosed_le (f := fun x => ‖h t x - b x‖) (by fun_prop) continuous_const).closure_subset_iff.2 (fun x hx => H x hx) (hD x)`.

Rewrite using `[e]`. Conclude with `NullMeasurableSet.biInter hDc fun x _ => ((hm x).sub aestronglyMeasurable_const).norm.aemeasurable.nullMeasurable measurableSet_Iic`. Establish `hN : NullMeasurable h μ`. Use `(@measurable_of_isOpen _ (NullMeasurableSpace T μ) _ _ _ _ h fun U hU => ?_ :)` and prove the remaining obligations. Use `show NullMeasurableSet (h ⁻¹' U) μ`.

Establish `h1 : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U` using `fun x hx => Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)`. Use `choose! r hr hrU using h1`. Take `⟨S, hSU, hSc, hS⟩` from `TopologicalSpace.countable_cover_nhdsWithin (s := U) (f := fun x => Metric.closedBall x (r x)) fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (hr x hx))`. Establish `e : U = ⋃ x ∈ S, Metric.closedBall x (r x)` using `hS.antisymm (iUnion₂_subset fun x hx => hrU x (hSU hx))`. Rewrite using `[e, preimage_iUnion₂]`.

Conclude with `NullMeasurableSet.biUnion hSc fun x hx => hb x _ (hr x (hSU hx)).le`. Conclude with `hN.aemeasurable.aestronglyMeasurable`.
-/
theorem aesm_contMap {T K W : Type} [MeasurableSpace T] {μ : Measure T} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [T2Space K] [NormedAddCommGroup W] [SecondCountableTopology W]
    (h : T → C(K, W)) (hm : ∀ x, AEStronglyMeasurable (fun t => h t x) μ) : AEStronglyMeasurable h μ := by
  borelize C(K, W)
  have hb : ∀ (b : C(K, W)) (r : ℝ), 0 ≤ r → NullMeasurableSet (h ⁻¹' Metric.closedBall b r) μ := by
    intro b r hr
    obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense K
    have e : h ⁻¹' Metric.closedBall b r = ⋂ x ∈ D, (fun t => ‖h t x - b x‖) ⁻¹' Iic r := by
      ext t
      rw [mem_preimage, Metric.mem_closedBall, ContinuousMap.dist_le hr]
      simp only [mem_preimage, mem_iInter, mem_Iic, dist_eq_norm]
      refine ⟨fun H x _ => H x, fun H x => ?_⟩
      exact (isClosed_le (f := fun x => ‖h t x - b x‖) (by fun_prop) continuous_const).closure_subset_iff.2
        (fun x hx => H x hx) (hD x)
    rw [e]
    exact NullMeasurableSet.biInter hDc fun x _ =>
      ((hm x).sub aestronglyMeasurable_const).norm.aemeasurable.nullMeasurable measurableSet_Iic
  have hN : NullMeasurable h μ := by
    refine (@measurable_of_isOpen _ (NullMeasurableSpace T μ) _ _ _ _ h fun U hU => ?_ :)
    show NullMeasurableSet (h ⁻¹' U) μ
    have h1 : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U := fun x hx =>
      Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    choose! r hr hrU using h1
    obtain ⟨S, hSU, hSc, hS⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := U)
      (f := fun x => Metric.closedBall x (r x)) fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (hr x hx))
    have e : U = ⋃ x ∈ S, Metric.closedBall x (r x) :=
      hS.antisymm (iUnion₂_subset fun x hx => hrU x (hSU hx))
    rw [e, preimage_iUnion₂]
    exact NullMeasurableSet.biUnion hSc fun x hx => hb x _ (hr x (hSU hx)).le
  exact hN.aemeasurable.aestronglyMeasurable

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Use `haveI := FiniteDimensional.proper_real V`. Rewrite using `[coclosedCompact_eq_cocompact, tendsto_zero_iff_norm_tendsto_zero]`. Take `⟨C, hC0, hC⟩` from `f.decay (k + 1) n`. Establish `h1 : Tendsto (fun x : V => C * ‖x‖⁻¹) (cocompact V) (𝓝 0)`. Simplify using `using (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := V))).const_mul C`.

Use `squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1` and prove the remaining obligations. Use `filter_upwards [(tendsto_norm_cocompact_atTop (E := V)).eventually_gt_atTop 0] with x hx`. Rewrite using `[norm_smul, norm_pow, norm_norm, ← div_eq_mul_inv, le_div_iff₀ hx]`. Use `le_trans (le_of_eq ?_) (hC x)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_weight (f : 𝓢(V, ℂ)) (k n : ℕ) :
    Tendsto (fun x : V => ‖x‖ ^ k • iteratedFDeriv ℝ n f x) (coclosedCompact V) (𝓝 0) := by
  haveI := FiniteDimensional.proper_real V
  rw [coclosedCompact_eq_cocompact, tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, hC0, hC⟩ := f.decay (k + 1) n
  have h1 : Tendsto (fun x : V => C * ‖x‖⁻¹) (cocompact V) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := V))).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [(tendsto_norm_cocompact_atTop (E := V)).eventually_gt_atTop 0] with x hx
  rw [norm_smul, norm_pow, norm_norm, ← div_eq_mul_inv, le_div_iff₀ hx]
  refine le_trans (le_of_eq ?_) (hC x)
  ring

def wD (k n : ℕ) : 𝓢(V, ℂ) →ₗ[ℂ] C(OnePoint V, V [×n]→L[ℝ] ℂ) where
  toFun f := OnePoint.continuousMapMk ⟨fun x => ‖x‖ ^ k • iteratedFDeriv ℝ n f x,
    (continuous_norm.pow k).smul ((f.smooth n).continuous_iteratedFDeriv le_rfl)⟩ 0 (tendsto_weight f k n)
  map_add' f g := by
    ext1 x
    induction x using OnePoint.rec with
    | infty => exact (add_zero _).symm
    | coe x =>
      show ‖x‖ ^ k • iteratedFDeriv ℝ n (⇑f + ⇑g) x = ‖x‖ ^ k • iteratedFDeriv ℝ n f x + ‖x‖ ^ k • iteratedFDeriv ℝ n g x
      rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt, smul_add]
  map_smul' c f := by
    ext1 x
    induction x using OnePoint.rec with
    | infty => exact (smul_zero c).symm
    | coe x =>
      show ‖x‖ ^ k • iteratedFDeriv ℝ n (c • ⇑f) x = c • ‖x‖ ^ k • iteratedFDeriv ℝ n f x
      rw [iteratedFDeriv_const_smul_apply (f.smooth n).contDiffAt, smul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wD_coe (k n : ℕ) (f : 𝓢(V, ℂ)) (x : V) : wD k n f (x : OnePoint V) = ‖x‖ ^ k • iteratedFDeriv ℝ n f x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wD_infty (k n : ℕ) (f : 𝓢(V, ℂ)) : wD k n f OnePoint.infty = 0 := rfl

/- English proof (translation)
Use `le_antisymm ((ContinuousMap.norm_le _ (apply_nonneg _ _)).2 fun x => ?_) (SchwartzMap.seminorm_le_bound ℂ k n f (norm_nonneg _) fun x => ?_)` and prove the remaining obligations. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => rw [wD_infty, norm_zero]`. Conclude with `apply_nonneg _ _`. Consider the case `coe x => rw [wD_coe, norm_smul, norm_pow, norm_norm]`.

Conclude with `SchwartzMap.le_seminorm ℂ k n f x`. Use `(wD k n f).norm_coe_le_norm (x : OnePoint V)` as an intermediate fact. Rewrite `this` using `[wD_coe, norm_smul, norm_pow, norm_norm]`. Then use the resulting hypothesis.
-/
theorem norm_wD (k n : ℕ) (f : 𝓢(V, ℂ)) : ‖wD k n f‖ = SchwartzMap.seminorm ℂ k n f := by
  refine le_antisymm ((ContinuousMap.norm_le _ (apply_nonneg _ _)).2 fun x => ?_)
    (SchwartzMap.seminorm_le_bound ℂ k n f (norm_nonneg _) fun x => ?_)
  · induction x using OnePoint.rec with
    | infty => rw [wD_infty, norm_zero]; exact apply_nonneg _ _
    | coe x => rw [wD_coe, norm_smul, norm_pow, norm_norm]; exact SchwartzMap.le_seminorm ℂ k n f x
  · have := (wD k n f).norm_coe_le_norm (x : OnePoint V)
    rwa [wD_coe, norm_smul, norm_pow, norm_norm] at this

/- English proof (translation)
Take `⟨s, C, -, hC⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) ((normSeminorm ℂ ℂ).comp L.toLinearMap) (continuous_norm.comp L.continuous)`. Set `J : 𝓢(V, ℂ) →ₗ[ℂ] (∀ i : s, C(OnePoint V, V [×i.1.2]→L[ℝ] ℂ))` to `LinearMap.pi fun i => wD i.1.1 i.1.2`. Establish `hJ : ∀ f, ‖L f‖ ≤ C * ‖J f‖` using `fun f => by`. Use `(hC f).trans ?_` and prove the remaining obligations. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`.

Use `mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2` and prove the remaining obligations. Conclude with `(norm_wD i.1 i.2 f).symm.le.trans (norm_le_pi_norm (J f) ⟨i, hi⟩)`. Establish `hker : LinearMap.ker J ≤ LinearMap.ker L.toLinearMap` using `fun f hf => by`. Use `hJ f` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker.1 hf, norm_zero, mul_zero]`.

Conclude with `norm_le_zero_iff.1 this`. Set `L₀ : LinearMap.range J →ₗ[ℂ] ℂ` to `(LinearMap.ker J).liftQ L.toLinearMap hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap`. Establish `hL₀ : ∀ f, L₀ ⟨J f, f, rfl⟩ = L f` using `fun f => by`. Simplify using `only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[show J.quotKerEquivRange.symm ⟨J f, f, rfl⟩ = _ from J.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]`.

Both sides reduce to the same expression. Take `⟨L', hL', -⟩` from `exists_extension_norm_eq (LinearMap.range J) (L₀.mkContinuous C (by`. Introduce and unpack `⟨_, f, rfl⟩`. Rewrite using `[hL₀]`. Conclude with `hJ f))`.

Conclude with `⟨s, L', fun f => ((hL' ⟨J f, f, rfl⟩).trans (hL₀ f)).symm⟩`.
-/
theorem exists_factor (L : 𝓢(V, ℂ) →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (L' : (∀ i : s, C(OnePoint V, V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, L f = L' fun i => wD i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp L.toLinearMap) (continuous_norm.comp L.continuous)
  let J : 𝓢(V, ℂ) →ₗ[ℂ] (∀ i : s, C(OnePoint V, V [×i.1.2]→L[ℝ] ℂ)) := LinearMap.pi fun i => wD i.1.1 i.1.2
  have hJ : ∀ f, ‖L f‖ ≤ C * ‖J f‖ := fun f => by
    refine (hC f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_wD i.1 i.2 f).symm.le.trans (norm_le_pi_norm (J f) ⟨i, hi⟩)
  have hker : LinearMap.ker J ≤ LinearMap.ker L.toLinearMap := fun f hf => by
    have := hJ f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let L₀ : LinearMap.range J →ₗ[ℂ] ℂ := (LinearMap.ker J).liftQ L.toLinearMap hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ f, L₀ ⟨J f, f, rfl⟩ = L f := fun f => by
    simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show J.quotKerEquivRange.symm ⟨J f, f, rfl⟩ = _ from J.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨L', hL', -⟩ := exists_extension_norm_eq (LinearMap.range J) (L₀.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [hL₀]; exact hJ f))
  exact ⟨s, L', fun f => ((hL' ⟨J f, f, rfl⟩).trans (hL₀ f)).symm⟩

variable {T : Type} [MeasurableSpace T] {μ : Measure T}

/- English proof (translation)
Use `choose b hbi hb using hb`. Establish `hbd : ∀ n t x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ b n t` using `fun n t x => (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f t) n x).trans (hb n t)`. Establish `hd : ∀ n t, Differentiable ℝ (iteratedFDeriv ℝ n (f t))` using `fun n t => ((f t).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n)`. Establish `step : ∀ n, (∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (f t) x) μ) → ∀ x, AEStronglyMeasurable (fun t => fderiv ℝ (iteratedFDeriv ℝ n (f t)) x) μ ∧ HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ n (f t) y ∂μ) (∫ t, fderiv ℝ (iteratedFDeriv ℝ n (f t)) x ∂μ) x`. Introduce `n h x`.

Establish `h1` using `Formalism.FourierDecayAlt.P.Ux10.aesm_fderiv (μ := μ) (x := x) (fun t => hd n t x) (Eventually.of_forall h)`. Use `⟨h1, hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y t => iteratedFDeriv ℝ n (f t) y) (F' := fun y t => fderiv ℝ (iteratedFDeriv ℝ n (f t)) y) (bound := b (n + 1)) univ_mem (Eventually.of_forall h) ((hbi n).mono' (h x) (Eventually.of_forall fun t => hbd n t x)) h1 (Eve …` and prove the remaining obligations. Rewrite using `[norm_fderiv_iteratedFDeriv]`. Conclude with `hbd _ t z`. Establish `main : ∀ n, (∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (f t) x) μ) ∧ (∀ x, iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ) x = ∫ t, iteratedFDeriv ℝ n (f t) x ∂μ)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]`. Conclude with `⟨fun x => (continuousMultilinearCurryFin0 ℝ V ℂ).symm.continuous.comp_aestronglyMeasurable (hm x), fun x => ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toLinearIsometry.integral_comp_comm _).symm⟩`.

Consider the case `succ n ih`. Simplify using `only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]`. Use `⟨fun x => (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (step n ih.1 x).1, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[funext ih.2, (step n ih.1 x).2.fderiv]`. Conclude with `((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).symm.toLinearIsometry.integral_comp_comm _).symm`.

Use `⟨(main n).1, (main n).2, ?_⟩` and prove the remaining obligations. Rewrite using `[funext (main n).2]`. Conclude with `fun x => (step n (main n).1 x).2.differentiableAt`.
-/
theorem iter_integral (f : T → 𝓢(V, ℂ)) (hm : ∀ y, AEStronglyMeasurable (fun t => f t y) μ)
    (hb : ∀ n, ∃ b : T → ℝ, Integrable b μ ∧ ∀ t, SchwartzMap.seminorm ℂ 0 n (f t) ≤ b t) (n : ℕ) :
    (∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (f t) x) μ) ∧
    (∀ x, iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ) x = ∫ t, iteratedFDeriv ℝ n (f t) x ∂μ) ∧
    Differentiable ℝ (iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ)) := by
  choose b hbi hb using hb
  have hbd : ∀ n t x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ b n t := fun n t x =>
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f t) n x).trans (hb n t)
  have hd : ∀ n t, Differentiable ℝ (iteratedFDeriv ℝ n (f t)) := fun n t =>
    ((f t).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n)
  have step : ∀ n, (∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (f t) x) μ) → ∀ x,
      AEStronglyMeasurable (fun t => fderiv ℝ (iteratedFDeriv ℝ n (f t)) x) μ ∧
      HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ n (f t) y ∂μ) (∫ t, fderiv ℝ (iteratedFDeriv ℝ n (f t)) x ∂μ) x := by
    intro n h x
    have h1 := Formalism.FourierDecayAlt.P.Ux10.aesm_fderiv (μ := μ) (x := x) (fun t => hd n t x) (Eventually.of_forall h)
    refine ⟨h1, hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y t => iteratedFDeriv ℝ n (f t) y)
      (F' := fun y t => fderiv ℝ (iteratedFDeriv ℝ n (f t)) y) (bound := b (n + 1)) univ_mem (Eventually.of_forall h)
      ((hbi n).mono' (h x) (Eventually.of_forall fun t => hbd n t x)) h1
      (Eventually.of_forall fun t z _ => ?_) (hbi _) (Eventually.of_forall fun t z _ => (hd n t z).hasFDerivAt)⟩
    rw [norm_fderiv_iteratedFDeriv]
    exact hbd _ t z
  have main : ∀ n, (∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (f t) x) μ) ∧
      (∀ x, iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ) x = ∫ t, iteratedFDeriv ℝ n (f t) x ∂μ) := by
    intro n
    induction n with
    | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ⟨fun x => (continuousMultilinearCurryFin0 ℝ V ℂ).symm.continuous.comp_aestronglyMeasurable (hm x),
        fun x => ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toLinearIsometry.integral_comp_comm _).symm⟩
    | succ n ih =>
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      refine ⟨fun x => (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (step n ih.1 x).1, fun x => ?_⟩
      rw [funext ih.2, (step n ih.1 x).2.fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  refine ⟨(main n).1, (main n).2, ?_⟩
  rw [funext (main n).2]
  exact fun x => (step n (main n).1 x).2.differentiableAt

/- English proof (translation)
Establish `hI` using `iter_integral f hm (hb 0)`. Use `choose b hbi hb using hb`. Use `haveI : SecondCountableTopology (OnePoint V) := (onePointEquivSphereOfFinrankEq (ι := Fin (Module.finrank ℝ V + 1)) (V := V) (by simp)).secondCountableTopology`. Use `haveI : ∀ n, SecondCountableTopology (V [×n]→L[ℝ] ℂ) := fun n => by haveI : FiniteDimensional ℝ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear ContinuousMultilinearMap.toMultilinearMap_injective haveI := FiniteDimensional.proper_real …`. Establish `hw : ∀ k n, Integrable (fun t => wD k n (f t)) μ` using `fun k n => by`.

Use `(hbi k n).mono' (aesm_contMap _ fun x => ?_) (Eventually.of_forall fun t => (norm_wD k n _).le.trans (hb k n t))` and prove the remaining obligations. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => exact aestronglyMeasurable_const`. Consider the case `coe x => exact ((hI n).1 x).const_smul (‖x‖ ^ k)`. Establish `hx : ∀ k n (x : V), ‖x‖ ^ k • iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ) x = (∫ t, wD k n (f t) ∂μ) x` using `fun k n x => by`.

Rewrite using `[ContinuousMap.integral_apply (hw k n), (hI n).2.1, ← integral_smul]`. Both sides reduce to the same expression. Set `g : 𝓢(V, ℂ)` to `⟨fun y => ∫ t, f t y ∂μ, contDiff_of_differentiable_iteratedFDeriv fun n _ => (hI n).2.2, fun k n => ⟨‖∫ t, wD k n (f t) ∂μ‖, fun x => by`. Use `(∫ t, wD k n (f t) ∂μ).norm_coe_le_norm (x : OnePoint V)` as an intermediate fact. Rewrite using `[← hx, norm_smul, norm_pow, norm_norm] at this⟩⟩` and apply the resulting hypothesis.

Establish `hg : ∀ k n, wD k n g = ∫ t, wD k n (f t) ∂μ` using `fun k n => by ext1 x`. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => rw [ContinuousMap.integral_apply (hw k n)]`. Simplify using `only [wD_infty, integral_zero]`. Consider the case `coe x => exact hx k n x`.

Use `⟨g, fun _ => rfl, fun L => ?_⟩` and prove the remaining obligations. Take `⟨s, L', hL⟩` from `exists_factor L`. Establish `hi : Integrable (fun t (i : s) => wD i.1.1 i.1.2 (f t)) μ` using `Integrable.of_eval fun i => hw _ _`. Simplify using `only [hL]`. Use `⟨L'.integrable_comp hi, ?_⟩` and prove the remaining obligations.

Rewrite using `[L'.integral_comp_comm hi]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[hg, eval_integral fun i : s => hw i.1.1 i.1.2]`.
-/
theorem exists_integral (f : T → 𝓢(V, ℂ)) (hm : ∀ y, AEStronglyMeasurable (fun t => f t y) μ)
    (hb : ∀ k n, ∃ b : T → ℝ, Integrable b μ ∧ ∀ t, SchwartzMap.seminorm ℂ k n (f t) ≤ b t) :
    ∃ g : 𝓢(V, ℂ), (∀ y, g y = ∫ t, f t y ∂μ) ∧
      ∀ L : 𝓢(V, ℂ) →L[ℂ] ℂ, Integrable (fun t => L (f t)) μ ∧ L g = ∫ t, L (f t) ∂μ := by
  have hI := iter_integral f hm (hb 0)
  choose b hbi hb using hb
  haveI : SecondCountableTopology (OnePoint V) :=
    (onePointEquivSphereOfFinrankEq (ι := Fin (Module.finrank ℝ V + 1)) (V := V) (by simp)).secondCountableTopology
  haveI : ∀ n, SecondCountableTopology (V [×n]→L[ℝ] ℂ) := fun n => by
    haveI : FiniteDimensional ℝ (V [×n]→L[ℝ] ℂ) :=
      Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear ContinuousMultilinearMap.toMultilinearMap_injective
    haveI := FiniteDimensional.proper_real (V [×n]→L[ℝ] ℂ)
    infer_instance
  have hw : ∀ k n, Integrable (fun t => wD k n (f t)) μ := fun k n => by
    refine (hbi k n).mono' (aesm_contMap _ fun x => ?_) (Eventually.of_forall fun t => (norm_wD k n _).le.trans (hb k n t))
    induction x using OnePoint.rec with
    | infty => exact aestronglyMeasurable_const
    | coe x => exact ((hI n).1 x).const_smul (‖x‖ ^ k)
  have hx : ∀ k n (x : V), ‖x‖ ^ k • iteratedFDeriv ℝ n (fun y => ∫ t, f t y ∂μ) x = (∫ t, wD k n (f t) ∂μ) x := fun k n x => by
    rw [ContinuousMap.integral_apply (hw k n), (hI n).2.1, ← integral_smul]
    rfl
  let g : 𝓢(V, ℂ) := ⟨fun y => ∫ t, f t y ∂μ, contDiff_of_differentiable_iteratedFDeriv fun n _ => (hI n).2.2,
    fun k n => ⟨‖∫ t, wD k n (f t) ∂μ‖, fun x => by
      have := (∫ t, wD k n (f t) ∂μ).norm_coe_le_norm (x : OnePoint V)
      rwa [← hx, norm_smul, norm_pow, norm_norm] at this⟩⟩
  have hg : ∀ k n, wD k n g = ∫ t, wD k n (f t) ∂μ := fun k n => by
    ext1 x
    induction x using OnePoint.rec with
    | infty => rw [ContinuousMap.integral_apply (hw k n)]; simp only [wD_infty, integral_zero]
    | coe x => exact hx k n x
  refine ⟨g, fun _ => rfl, fun L => ?_⟩
  obtain ⟨s, L', hL⟩ := exists_factor L
  have hi : Integrable (fun t (i : s) => wD i.1.1 i.1.2 (f t)) μ := Integrable.of_eval fun i => hw _ _
  simp only [hL]
  refine ⟨L'.integrable_comp hi, ?_⟩
  rw [L'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hg, eval_integral fun i : s => hw i.1.1 i.1.2]

end GlobalTheory.SchwartzPettis

end
