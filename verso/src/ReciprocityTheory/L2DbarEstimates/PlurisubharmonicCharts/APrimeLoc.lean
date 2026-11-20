import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeB

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

/- English proof (translation)
Use `haveI hvolF : (volume : Measure (V a × V b)).IsAddHaarMeasure := by`. Rewrite using `[Measure.volume_eq_prod]`. Use `haveI : (volume : Measure (V a)).IsAddHaarMeasure := inferInstance`. Use `haveI : (volume : Measure (V b)).IsAddHaarMeasure := inferInstance`. Use `haveI : SigmaFinite (volume : Measure (V a)) := inferInstance`.

Use `haveI : SigmaFinite (volume : Measure (V b)) := inferInstance`. Use `first`. Consider the case `infer_instance`. Consider the case `exact Measure.prod.instIsAddHaarMeasure _ _`. Consider the case `exact { toIsFiniteMeasureOnCompacts := inferInstance toIsAddLeftInvariant := inferInstance toIsOpenPosMeasure := inferInstance }`.

Use `set ν : Measure (V n) := Measure.map (A.symm : V a × V b → V n) volume with hν`. Use `haveI : ν.IsAddHaarMeasure := by`. Rewrite using `[hν]`. Use `first`. Consider the case `infer_instance`.

Consider the case `exact A.symm.isAddHaarMeasure_map volume`. Consider the case `exact ContinuousLinearEquiv.isAddHaarMeasure_map A.symm volume`. Consider the case `exact Measure.MapContinuousLinearEquiv.isAddHaarMeasure volume A.symm`. Consider the case `exact (A.symm.restrictScalars ℝ).isAddHaarMeasure_map volume`. Consider the case `exact Measure.isAddHaarMeasure_map volume (A.symm : V a × V b →+ V n) A.symm.continuous A.symm.surjective (A.symm.toHomeomorph.toCocompactMap.cocompact_tendsto')`.

Use `⟨Measure.addHaarScalarFactor ν volume, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume, ?_⟩` and prove the remaining obligations. Introduce `B h`. Establish `hmp : MeasurePreserving (A.symm : V a × V b → V n) volume ν` using `⟨A.symm.continuous.measurable, rfl⟩`. Establish `hemb : MeasurableEmbedding (A.symm : V a × V b → V n)` using `A.symm.toHomeomorph.measurableEmbedding`. Establish `hpre : (A.symm : V a × V b → V n) ⁻¹' ((A : V n → V a × V b) ⁻¹' B) = B`.

Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `key` using `hmp.setLIntegral_comp_preimage_emb hemb h ((A : V n → V a × V b) ⁻¹' B)`. Rewrite `key` using `[hpre]`. Rewrite using `[key]`.

Use `conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν volume]`. Rewrite using `[Measure.restrict_smul, lintegral_smul_measure]`. Use `first`. Consider the case `rfl`. Consider the case `simp [ENNReal.smul_def]`.
-/
private lemma exists_const_lintegral_comp_continuousLinearEquiv {n a b : ℕ} (A : V n ≃L[ℂ] V a × V b) :
    ∃ K : NNReal, 0 < K ∧ ∀ (B : Set (V a × V b)) (h : V n → ℝ≥0∞),
      ∫⁻ z in B, h (A.symm z) = (K : ℝ≥0∞) * ∫⁻ x in (A : V n → V a × V b) ⁻¹' B, h x := by
  haveI hvolF : (volume : Measure (V a × V b)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    haveI : (volume : Measure (V a)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (V b)).IsAddHaarMeasure := inferInstance
    haveI : SigmaFinite (volume : Measure (V a)) := inferInstance
    haveI : SigmaFinite (volume : Measure (V b)) := inferInstance
    first
      | infer_instance
      | exact Measure.prod.instIsAddHaarMeasure _ _
      | exact
          { toIsFiniteMeasureOnCompacts := inferInstance
            toIsAddLeftInvariant := inferInstance
            toIsOpenPosMeasure := inferInstance }
  set ν : Measure (V n) := Measure.map (A.symm : V a × V b → V n) volume with hν
  haveI : ν.IsAddHaarMeasure := by
    rw [hν]
    first
      | infer_instance
      | exact A.symm.isAddHaarMeasure_map volume
      | exact ContinuousLinearEquiv.isAddHaarMeasure_map A.symm volume
      | exact Measure.MapContinuousLinearEquiv.isAddHaarMeasure volume A.symm
      | exact (A.symm.restrictScalars ℝ).isAddHaarMeasure_map volume
      | exact Measure.isAddHaarMeasure_map volume
          (A.symm : V a × V b →+ V n) A.symm.continuous A.symm.surjective
          (A.symm.toHomeomorph.toCocompactMap.cocompact_tendsto')
  refine ⟨Measure.addHaarScalarFactor ν volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume, ?_⟩
  intro B h
  have hmp : MeasurePreserving (A.symm : V a × V b → V n) volume ν :=
    ⟨A.symm.continuous.measurable, rfl⟩
  have hemb : MeasurableEmbedding (A.symm : V a × V b → V n) :=
    A.symm.toHomeomorph.measurableEmbedding
  have hpre : (A.symm : V a × V b → V n) ⁻¹' ((A : V n → V a × V b) ⁻¹' B) = B := by
    ext z; simp
  have key := hmp.setLIntegral_comp_preimage_emb hemb h ((A : V n → V a × V b) ⁻¹' B)
  rw [hpre] at key
  rw [key]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν volume]
  rw [Measure.restrict_smul, lintegral_smul_measure]
  first
    | rfl
    | simp [ENNReal.smul_def]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨A, hA⟩` from `aprb_complement (fderiv ℂ p v0) hsurj`. Take `⟨K, hK, hKeq⟩` from `exists_const_lintegral_comp_continuousLinearEquiv A`. Use `set Lsnd : V n →L[ℂ] V (n - d) := (ContinuousLinearMap.snd ℂ (V d) (V (n - d))).comp (A : V n →L[ℂ] V d × V (n - d)) with hLsnd`. Use `set Ψ : V n → V n := fun v => A.symm (p v, Lsnd v - Lsnd v0) with hΨdef`. Establish `hΨ0 : Ψ v0 = 0` using `by simp [Ψ, hp0]`.

Establish `hpC : ContDiffOn ℂ 1 p U` using `by simpa using aprb_contDiffOn hU hp 1`. Establish `hΨdiff : ∀ v ∈ U, DifferentiableAt ℂ Ψ v`. Introduce `v hv`. Establish `h1 : DifferentiableAt ℂ p v` using `hp.differentiableAt (hU.mem_nhds hv)`. Establish `h2 : DifferentiableAt ℂ (fun w => (p w, Lsnd w - Lsnd v0)) v` using `by first`.

Consider the case `exact h1.prodMk (Lsnd.differentiableAt.sub_const _)`. Consider the case `exact h1.prod (Lsnd.differentiableAt.sub_const _)`. Conclude with `(A.symm : V d × V (n - d) →L[ℂ] V n).differentiableAt.comp v h2`. Establish `hΨc : ContDiffAt ℂ 1 Ψ v0`. Establish `h1 : ContDiffAt ℂ 1 p v0` using `hpC.contDiffAt (hU.mem_nhds hv0)`.

Establish `h2 : ContDiffAt ℂ 1 (fun w => (p w, Lsnd w - Lsnd v0)) v0` using `by first`. Consider the case `exact h1.prodMk (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)`. Consider the case `exact h1.prod (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)`. Conclude with `(A.symm : V d × V (n - d) →L[ℂ] V n).contDiff.contDiffAt.comp v0 h2`. Establish `hΨd : HasFDerivAt Ψ ((ContinuousLinearEquiv.refl ℂ (V n) : V n ≃L[ℂ] V n) : V n →L[ℂ] V n) v0`.

Establish `h1 : HasFDerivAt p (fderiv ℂ p v0) v0` using `(hp.differentiableAt (hU.mem_nhds hv0)).hasFDerivAt`. Establish `h2 : HasFDerivAt (fun w => (p w, Lsnd w - Lsnd v0)) ((fderiv ℂ p v0).prod Lsnd) v0` using `by first`. Consider the case `exact h1.prodMk (Lsnd.hasFDerivAt.sub_const (Lsnd v0))`. Consider the case `exact h1.prod (Lsnd.hasFDerivAt.sub_const (Lsnd v0))`. Establish `h3` using `(A.symm : V d × V (n - d) →L[ℂ] V n).hasFDerivAt.comp v0 h2`.

Use `h3.congr_fderiv ?_` and prove the remaining obligations. Use `ext1 h`. Establish `hh : ((fderiv ℂ p v0) h, Lsnd h) = A h` using `Prod.ext (hA h).symm rfl`. Simplify using `[hh]`. Establish `hs` using `hΨc.hasStrictFDerivAt' hΨd (by simp)`.

Use `set G : V n → V n := hs.localInverse Ψ (ContinuousLinearEquiv.refl ℂ (V n)) v0 with hGdef`. Establish `hGc : ContDiffAt ℂ 1 G (Ψ v0)` using `hΨc.to_localInverse hΨd (by simp)`. Establish `hC : ContDiffAt ℝ 1 Ψ v0` using `hΨc.restrict_scalars ℝ`. Establish `hcontD : ContinuousAt (fderiv ℝ Ψ) v0` using `(hC.fderiv_right (m := 0) (by rw [zero_add])).continuousAt`. Establish `habs : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v0` using `continuous_abs.continuousAt.comp (ContinuousLinearMap.continuous_det.continuousAt.comp hcontD)`.

Establish `hev1 : ∀ᶠ v in 𝓝 v0, G (Ψ v) = v ∧ |(fderiv ℝ Ψ v).det| < |(fderiv ℝ Ψ v0).det| + 1` using `hs.eventually_left_inverse.and (habs.eventually (Iio_mem_nhds (lt_add_one _)))`. Use `set C : ℝ := |(fderiv ℝ Ψ v0).det| + 1 with hCdef`. Establish `hCpos : 0 < C` using `by rw [hCdef]; positivity`. Take `⟨δ1, hδ1, hδ1b⟩` from `Metric.eventually_nhds_iff_ball.1 hev1`. Take `⟨δ2, hδ2, hδ2b⟩` from `Metric.isOpen_iff.1 hU v0 hv0`.

Use `set δ : ℝ := min δ1 δ2 / 2 with hδdef`. Establish `hδpos : 0 < δ` using `half_pos (lt_min hδ1 hδ2)`. Establish `hδlt : δ < min δ1 δ2` using `half_lt_self (lt_min hδ1 hδ2)`. Establish `hballU : Metric.ball v0 δ ⊆ U` using `fun v hv => hδ2b (Metric.ball_subset_ball ((hδlt.le).trans (min_le_right _ _)) hv)`. Establish `hballP : ∀ v ∈ Metric.ball v0 δ, G (Ψ v) = v ∧ |(fderiv ℝ Ψ v).det| < C` using `fun v hv => hδ1b v (Metric.ball_subset_ball ((hδlt.le).trans (min_le_left _ _)) hv)`.

Use `⟨δ, hδpos, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Metric.closedBall_subset_ball hδlt).trans (fun v hv => hδ2b (Metric.ball_subset_ball (min_le_right _ _) hv))`. Establish `hevB : ∀ᶠ x in 𝓝 (Ψ v0), G x ∈ Metric.ball v0 δ` using `hs.localInverse_tendsto (Metric.ball_mem_nhds v0 hδpos)`. Establish `hevD : ∀ᶠ x in 𝓝 (Ψ v0), DifferentiableAt ℂ G x` using `(hGc.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)`. Establish `hev2 : ∀ᶠ x in 𝓝 (Ψ v0), Ψ (G x) = x ∧ G x ∈ Metric.ball v0 δ ∧ DifferentiableAt ℂ G x` using `Filter.Eventually.and hs.eventually_right_inverse (Filter.Eventually.and hevB hevD)`.

Rewrite `hev2` using `[hΨ0]`. Take `⟨r, hr, hrb⟩` from `Metric.eventually_nhds_iff_ball.1 hev2`. Use `set As : V d × V (n - d) →L[ℂ] V n := (A.symm : V d × V (n - d) →L[ℂ] V n) with hAs`. Use `set ε : ℝ := r / (‖As‖ + 1) with hεdef`. Establish `hAs1 : 0 < ‖As‖ + 1` using `by positivity`.

Establish `hε : 0 < ε` using `div_pos hr hAs1`. Use `set Box : Set (V d × V (n - d)) := Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V (n - d)) ε with hBoxdef`. Establish `hBox : ∀ z ∈ Box, A.symm z ∈ Metric.ball (0 : V n) r`. Introduce `z hz`. Establish `hz1 : ‖z.1‖ < ε` using `by simpa using hz.1`.

Establish `hz2 : ‖z.2‖ < ε` using `by simpa using hz.2`. Establish `hzn : ‖z‖ < ε` using `by rw [Prod.norm_def]; exact max_lt hz1 hz2`. Rewrite using `[Metric.mem_ball, dist_zero_right]`. Establish `h1 : ‖A.symm z‖ ≤ ‖As‖ * ‖z‖` using `As.le_opNorm z`. Establish `h2 : ‖As‖ * ‖z‖ ≤ ‖As‖ * ε` using `mul_le_mul_of_nonneg_left hzn.le (norm_nonneg _)`.

Establish `h3 : ‖As‖ * ε < (‖As‖ + 1) * ε` using `by nlinarith`. Establish `h4 : (‖As‖ + 1) * ε = r` using `by rw [hεdef]; field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `M`. Take `⟨τ0, hτ0, hblow⟩` from `ap_prod_blowup d (n - d) hd (hMVd d) (hMVd (n - d)) hMVI ε hε (M * ((K : ℝ) * C))`.

Use `⟨τ0, hτ0, fun τ hτ hττ0 u hu => ?_⟩` and prove the remaining obligations. Establish `hBm : MeasurableSet Box` using `measurableSet_ball.prod measurableSet_ball`. Establish `hu' : DifferentiableOn ℂ (fun z => u (G (A.symm z))) Box`. Introduce `z hz`. Take `⟨_, hGb, hGd⟩` from `hrb _ (hBox z hz)`.

Establish `hu1 : DifferentiableAt ℂ u (G (A.symm z))` using `hu.differentiableAt (Metric.isOpen_ball.mem_nhds hGb)`. Conclude with `((hu1.comp _ hGd).comp z As.differentiableAt).differentiableWithinAt`. Establish `hb` using `hblow τ hτ hττ0 _ hu'`. Use `beta_reduce at hb`. Rewrite `hb` using `[← hBoxdef]`.

Establish `hG0 : G 0 = v0`. Rewrite using `[← hΨ0]`. Conclude with `hs.localInverse_apply_image`. Establish `hu0 : u (G (A.symm 0)) = u v0` using `by rw [map_zero, hG0]`. Use `set g : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) with hgdef`.

Establish `hpz : ∀ z ∈ Box, p (G (A.symm z)) = z.1`. Introduce `z hz`. Establish `hR` using `(hrb _ (hBox z hz)).1`. Use `congrArg (fun w => (A w).1) hR` as an intermediate fact. Simplify `this` using `[Ψ]`.

Establish `hI1 : ∫⁻ z in Box, ENNReal.ofReal (‖u (G (A.symm z))‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) = ∫⁻ z in Box, g (G (A.symm z))`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem hBm] with z hz`. Simplify using `only [g]`. Rewrite using `[hpz z hz]`.

Establish `hI2 : ∫⁻ z in Box, g (G (A.symm z)) = (K : ℝ≥0∞) * ∫⁻ x in (A : V n → V d × V (n - d)) ⁻¹' Box, g (G x)` using `hKeq Box (fun x => g (G x))`. Use `set T : Set (V n) := (A : V n → V d × V (n - d)) ⁻¹' Box with hTdef`. Use `set s : Set (V n) := Metric.ball v0 δ ∩ Ψ ⁻¹' T with hsdef`. Establish `hTopen : IsOpen T` using `(Metric.isOpen_ball.prod Metric.isOpen_ball).preimage A.continuous`. Establish `hΨcont : ContinuousOn Ψ (Metric.ball v0 δ)` using `fun v hv => (hΨdiff v (hballU hv)).continuousAt.continuousWithinAt`.

Establish `hsm : MeasurableSet s` using `(hΨcont.isOpen_inter_preimage Metric.isOpen_ball hTopen).measurableSet`. Establish `himg : Ψ '' s = T`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, ⟨_, hv⟩, rfl⟩`.

Conclude with `hv`. Introduce `hx`. Establish `hxr : x ∈ Metric.ball (0 : V n) r`. Use `hBox (A x) hx` as an intermediate fact. Simplify using `using this`.

Take `⟨hR, hB, _⟩` from `hrb x hxr`. Use `⟨G x, ⟨hB, ?_⟩, hR⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, hR]`. Conclude with `hx`. Establish `hinj : Set.InjOn Ψ s`.

Introduce `v hv w hw hvw`. Rewrite using `[← (hballP v hv.1).1, ← (hballP w hw.1).1, hvw]`. Establish `hderiv : ∀ v ∈ s, HasFDerivWithinAt Ψ (fderiv ℝ Ψ v) s v` using `fun v hv => ((hΨdiff v (hballU hv.1)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt`. Establish `hcv` using `lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj (fun x => g (G x))`. Rewrite `hcv` using `[himg]`.

Establish `hbd : ∫⁻ v in s, ENNReal.ofReal |(fderiv ℝ Ψ v).det| * g (G (Ψ v)) ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem hsm] with v hv`. Take `⟨hL, hD⟩` from `hballP v hv.1`.

Rewrite using `[hL]`. Conclude with `mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hD.le) (by simp)`. Use `_ = ENNReal.ofReal C * ∫⁻ v in s, g v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v := mul_le_mul_of_nonneg_left (lintegral_mono_set Set.inter_subset_left) (by simp)`. Establish `hmain : ENNReal.ofReal (M * ((K : ℝ) * C) * ‖u v0‖ ^ 2) ≤ (K : ℝ≥0∞) * (ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v)`.

Establish `h` using `hb`. Rewrite `h` using `[hu0, hI1, hI2, hcv]`. Conclude with `h.trans (mul_le_mul_of_nonneg_left hbd (by simp))`. Establish `hKC : (0 : ℝ) ≤ (K : ℝ) * C` using `mul_nonneg K.coe_nonneg hCpos.le`. Rewrite `hmain` using `[show M * ((K : ℝ) * C) * ‖u v0‖ ^ 2 = ((K : ℝ) * C) * (M * ‖u v0‖ ^ 2) by ring, ENNReal.ofReal_mul hKC, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← mul_assoc]`.

Establish `h0 : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ 0` using `mul_ne_zero (by exact_mod_cast hK.ne') (by simpa using hCpos)`. Establish `htop : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top`. Use `first`. Consider the case `exact ENNReal.le_of_mul_le_mul_left hmain h0 htop`. Consider the case `exact (ENNReal.mul_le_mul_iff_right h0 htop).1 hmain`.

Consider the case `exact (ENNReal.mul_le_mul_iff_left h0 htop).1 hmain`. Consider the case `exact (ENNReal.mul_le_mul_left h0 htop).1 hmain`.
-/
theorem ap_local_blowup (n d : ℕ) (hd : 1 ≤ d) (hMVd : ∀ k, MVStatement k)
    (hMVI : MVIntStatement d) (U : Set (V n)) (hU : IsOpen U) (p : V n → V d)
    (hp : DifferentiableOn ℂ p U) (v0 : V n) (hv0 : v0 ∈ U) (hp0 : p v0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ p v0)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall v0 δ ⊆ U ∧ ∀ M : ℝ, ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V n → ℂ, DifferentiableOn ℂ u (Metric.ball v0 δ) →
        ENNReal.ofReal (M * ‖u v0‖ ^ 2) ≤
          ∫⁻ v in Metric.ball v0 δ, ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  classical
  obtain ⟨A, hA⟩ := aprb_complement (fderiv ℂ p v0) hsurj
  obtain ⟨K, hK, hKeq⟩ := exists_const_lintegral_comp_continuousLinearEquiv A
  set Lsnd : V n →L[ℂ] V (n - d) :=
    (ContinuousLinearMap.snd ℂ (V d) (V (n - d))).comp (A : V n →L[ℂ] V d × V (n - d)) with hLsnd
  set Ψ : V n → V n := fun v => A.symm (p v, Lsnd v - Lsnd v0) with hΨdef
  have hΨ0 : Ψ v0 = 0 := by simp [Ψ, hp0]
  have hpC : ContDiffOn ℂ 1 p U := by simpa using aprb_contDiffOn hU hp 1
  have hΨdiff : ∀ v ∈ U, DifferentiableAt ℂ Ψ v := by
    intro v hv
    have h1 : DifferentiableAt ℂ p v := hp.differentiableAt (hU.mem_nhds hv)
    have h2 : DifferentiableAt ℂ (fun w => (p w, Lsnd w - Lsnd v0)) v := by
      first
        | exact h1.prodMk (Lsnd.differentiableAt.sub_const _)
        | exact h1.prod (Lsnd.differentiableAt.sub_const _)
    exact (A.symm : V d × V (n - d) →L[ℂ] V n).differentiableAt.comp v h2
  have hΨc : ContDiffAt ℂ 1 Ψ v0 := by
    have h1 : ContDiffAt ℂ 1 p v0 := hpC.contDiffAt (hU.mem_nhds hv0)
    have h2 : ContDiffAt ℂ 1 (fun w => (p w, Lsnd w - Lsnd v0)) v0 := by
      first
        | exact h1.prodMk (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)
        | exact h1.prod (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)
    exact (A.symm : V d × V (n - d) →L[ℂ] V n).contDiff.contDiffAt.comp v0 h2
  have hΨd : HasFDerivAt Ψ
      ((ContinuousLinearEquiv.refl ℂ (V n) : V n ≃L[ℂ] V n) : V n →L[ℂ] V n) v0 := by
    have h1 : HasFDerivAt p (fderiv ℂ p v0) v0 :=
      (hp.differentiableAt (hU.mem_nhds hv0)).hasFDerivAt
    have h2 : HasFDerivAt (fun w => (p w, Lsnd w - Lsnd v0))
        ((fderiv ℂ p v0).prod Lsnd) v0 := by
      first
        | exact h1.prodMk (Lsnd.hasFDerivAt.sub_const (Lsnd v0))
        | exact h1.prod (Lsnd.hasFDerivAt.sub_const (Lsnd v0))
    have h3 := (A.symm : V d × V (n - d) →L[ℂ] V n).hasFDerivAt.comp v0 h2
    refine h3.congr_fderiv ?_
    ext1 h
    have hh : ((fderiv ℂ p v0) h, Lsnd h) = A h := Prod.ext (hA h).symm rfl
    simp [hh]
  have hs := hΨc.hasStrictFDerivAt' hΨd (by simp)
  set G : V n → V n := hs.localInverse Ψ (ContinuousLinearEquiv.refl ℂ (V n)) v0 with hGdef
  have hGc : ContDiffAt ℂ 1 G (Ψ v0) := hΨc.to_localInverse hΨd (by simp)
  have hC : ContDiffAt ℝ 1 Ψ v0 := hΨc.restrict_scalars ℝ
  have hcontD : ContinuousAt (fderiv ℝ Ψ) v0 :=
    (hC.fderiv_right (m := 0) (by rw [zero_add])).continuousAt
  have habs : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v0 :=
    continuous_abs.continuousAt.comp
      (ContinuousLinearMap.continuous_det.continuousAt.comp hcontD)
  have hev1 : ∀ᶠ v in 𝓝 v0, G (Ψ v) = v ∧
      |(fderiv ℝ Ψ v).det| < |(fderiv ℝ Ψ v0).det| + 1 :=
    hs.eventually_left_inverse.and (habs.eventually (Iio_mem_nhds (lt_add_one _)))
  set C : ℝ := |(fderiv ℝ Ψ v0).det| + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  obtain ⟨δ1, hδ1, hδ1b⟩ := Metric.eventually_nhds_iff_ball.1 hev1
  obtain ⟨δ2, hδ2, hδ2b⟩ := Metric.isOpen_iff.1 hU v0 hv0
  set δ : ℝ := min δ1 δ2 / 2 with hδdef
  have hδpos : 0 < δ := half_pos (lt_min hδ1 hδ2)
  have hδlt : δ < min δ1 δ2 := half_lt_self (lt_min hδ1 hδ2)
  have hballU : Metric.ball v0 δ ⊆ U := fun v hv =>
    hδ2b (Metric.ball_subset_ball ((hδlt.le).trans (min_le_right _ _)) hv)
  have hballP : ∀ v ∈ Metric.ball v0 δ, G (Ψ v) = v ∧ |(fderiv ℝ Ψ v).det| < C :=
    fun v hv => hδ1b v (Metric.ball_subset_ball ((hδlt.le).trans (min_le_left _ _)) hv)
  refine ⟨δ, hδpos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_ball hδlt).trans
      (fun v hv => hδ2b (Metric.ball_subset_ball (min_le_right _ _) hv))
  have hevB : ∀ᶠ x in 𝓝 (Ψ v0), G x ∈ Metric.ball v0 δ :=
    hs.localInverse_tendsto (Metric.ball_mem_nhds v0 hδpos)
  have hevD : ∀ᶠ x in 𝓝 (Ψ v0), DifferentiableAt ℂ G x :=
    (hGc.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have hev2 : ∀ᶠ x in 𝓝 (Ψ v0), Ψ (G x) = x ∧ G x ∈ Metric.ball v0 δ ∧
      DifferentiableAt ℂ G x :=
    Filter.Eventually.and hs.eventually_right_inverse (Filter.Eventually.and hevB hevD)
  rw [hΨ0] at hev2
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 hev2
  set As : V d × V (n - d) →L[ℂ] V n := (A.symm : V d × V (n - d) →L[ℂ] V n) with hAs
  set ε : ℝ := r / (‖As‖ + 1) with hεdef
  have hAs1 : 0 < ‖As‖ + 1 := by positivity
  have hε : 0 < ε := div_pos hr hAs1
  set Box : Set (V d × V (n - d)) :=
    Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V (n - d)) ε with hBoxdef
  have hBox : ∀ z ∈ Box, A.symm z ∈ Metric.ball (0 : V n) r := by
    intro z hz
    have hz1 : ‖z.1‖ < ε := by simpa using hz.1
    have hz2 : ‖z.2‖ < ε := by simpa using hz.2
    have hzn : ‖z‖ < ε := by rw [Prod.norm_def]; exact max_lt hz1 hz2
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖A.symm z‖ ≤ ‖As‖ * ‖z‖ := As.le_opNorm z
    have h2 : ‖As‖ * ‖z‖ ≤ ‖As‖ * ε := mul_le_mul_of_nonneg_left hzn.le (norm_nonneg _)
    have h3 : ‖As‖ * ε < (‖As‖ + 1) * ε := by nlinarith
    have h4 : (‖As‖ + 1) * ε = r := by rw [hεdef]; field_simp
    linarith
  intro M
  obtain ⟨τ0, hτ0, hblow⟩ := ap_prod_blowup d (n - d) hd (hMVd d) (hMVd (n - d)) hMVI ε hε
    (M * ((K : ℝ) * C))
  refine ⟨τ0, hτ0, fun τ hτ hττ0 u hu => ?_⟩
  have hBm : MeasurableSet Box := measurableSet_ball.prod measurableSet_ball
  have hu' : DifferentiableOn ℂ (fun z => u (G (A.symm z))) Box := by
    intro z hz
    obtain ⟨_, hGb, hGd⟩ := hrb _ (hBox z hz)
    have hu1 : DifferentiableAt ℂ u (G (A.symm z)) :=
      hu.differentiableAt (Metric.isOpen_ball.mem_nhds hGb)
    exact ((hu1.comp _ hGd).comp z As.differentiableAt).differentiableWithinAt
  have hb := hblow τ hτ hττ0 _ hu'
  beta_reduce at hb
  rw [← hBoxdef] at hb
  have hG0 : G 0 = v0 := by
    rw [← hΨ0]
    exact hs.localInverse_apply_image
  have hu0 : u (G (A.symm 0)) = u v0 := by rw [map_zero, hG0]
  set g : V n → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) with hgdef
  have hpz : ∀ z ∈ Box, p (G (A.symm z)) = z.1 := by
    intro z hz
    have hR := (hrb _ (hBox z hz)).1
    have := congrArg (fun w => (A w).1) hR
    simpa [Ψ] using this
  have hI1 : ∫⁻ z in Box, ENNReal.ofReal (‖u (G (A.symm z))‖ ^ 2 *
        (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) = ∫⁻ z in Box, g (G (A.symm z)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hBm] with z hz
    simp only [g]
    rw [hpz z hz]
  have hI2 : ∫⁻ z in Box, g (G (A.symm z)) =
      (K : ℝ≥0∞) * ∫⁻ x in (A : V n → V d × V (n - d)) ⁻¹' Box, g (G x) :=
    hKeq Box (fun x => g (G x))
  set T : Set (V n) := (A : V n → V d × V (n - d)) ⁻¹' Box with hTdef
  set s : Set (V n) := Metric.ball v0 δ ∩ Ψ ⁻¹' T with hsdef
  have hTopen : IsOpen T := (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage A.continuous
  have hΨcont : ContinuousOn Ψ (Metric.ball v0 δ) := fun v hv =>
    (hΨdiff v (hballU hv)).continuousAt.continuousWithinAt
  have hsm : MeasurableSet s :=
    (hΨcont.isOpen_inter_preimage Metric.isOpen_ball hTopen).measurableSet
  have himg : Ψ '' s = T := by
    ext x
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro hx
      have hxr : x ∈ Metric.ball (0 : V n) r := by
        have := hBox (A x) hx
        simpa using this
      obtain ⟨hR, hB, _⟩ := hrb x hxr
      refine ⟨G x, ⟨hB, ?_⟩, hR⟩
      rw [Set.mem_preimage, hR]
      exact hx
  have hinj : Set.InjOn Ψ s := by
    intro v hv w hw hvw
    rw [← (hballP v hv.1).1, ← (hballP w hw.1).1, hvw]
  have hderiv : ∀ v ∈ s, HasFDerivWithinAt Ψ (fderiv ℝ Ψ v) s v := fun v hv =>
    ((hΨdiff v (hballU hv.1)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj
    (fun x => g (G x))
  rw [himg] at hcv
  have hbd : ∫⁻ v in s, ENNReal.ofReal |(fderiv ℝ Ψ v).det| * g (G (Ψ v))
      ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v := by
    calc ∫⁻ v in s, ENNReal.ofReal |(fderiv ℝ Ψ v).det| * g (G (Ψ v))
        ≤ ∫⁻ v in s, ENNReal.ofReal C * g v := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hsm] with v hv
          obtain ⟨hL, hD⟩ := hballP v hv.1
          rw [hL]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hD.le) (by simp)
      _ = ENNReal.ofReal C * ∫⁻ v in s, g v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set Set.inter_subset_left) (by simp)
  have hmain : ENNReal.ofReal (M * ((K : ℝ) * C) * ‖u v0‖ ^ 2)
      ≤ (K : ℝ≥0∞) * (ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v) := by
    have h := hb
    rw [hu0, hI1, hI2, hcv] at h
    exact h.trans (mul_le_mul_of_nonneg_left hbd (by simp))
  have hKC : (0 : ℝ) ≤ (K : ℝ) * C := mul_nonneg K.coe_nonneg hCpos.le
  rw [show M * ((K : ℝ) * C) * ‖u v0‖ ^ 2 = ((K : ℝ) * C) * (M * ‖u v0‖ ^ 2) by ring,
    ENNReal.ofReal_mul hKC, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ← mul_assoc] at hmain
  have h0 : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hK.ne') (by simpa using hCpos)
  have htop : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  first
    | exact ENNReal.le_of_mul_le_mul_left hmain h0 htop
    | exact (ENNReal.mul_le_mul_iff_right h0 htop).1 hmain
    | exact (ENNReal.mul_le_mul_iff_left h0 htop).1 hmain
    | exact (ENNReal.mul_le_mul_left h0 htop).1 hmain

end

end ReciprocityTheory.L2DbarEstimates.Y
