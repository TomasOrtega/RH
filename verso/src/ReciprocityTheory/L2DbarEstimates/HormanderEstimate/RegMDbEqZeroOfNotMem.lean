import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegGlue

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Use `set L := fderiv ℝ g y with hL`. Establish `hsm : ∀ (c : ℂ) (w : V n), L (c • w) = c.re • L w + c.im • L (Complex.I • w)`. Introduce `c w`. Establish `hc : c • w = c.re • w + c.im • (Complex.I • w)` using `by conv_lhs => rw [← Complex.re_add_im c]`. Rewrite using `[add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`.

Rewrite using `[hc, map_add, map_smul, map_smul]`. Establish `hv : v = ∑ j, v j • bas n j` using `by conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]`. Simplify using `[bas]`. Establish `hIv : Complex.I • v = ∑ j, (Complex.I * v j) • bas n j` using `by conv_lhs => rw [hv]`. Simplify using `[Finset.smul_sum, smul_smul]`.

Establish `hLv : L v = ∑ j, L (v j • bas n j)` using `by conv_lhs => rw [hv]`. Rewrite using `[map_sum]`. Establish `hLIv : L (Complex.I • v) = ∑ j, L ((Complex.I * v j) • bas n j)`. Rewrite using `[hIv, map_sum]`. Simplify using `only [C.dbarDir, wdb, ← hL]`.

Rewrite using `[hLIv, hLv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsm (Complex.I * v j) (bas n j), hsm (v j) (bas n j)]`. Establish `hcj : conj (v j) = ((v j).re : ℂ) - ((v j).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Rewrite using `[hcj]`. Simplify using `only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, sub_zero, zero_add, Complex.ofReal_neg]`. Take the linear combination `(((v j).re : ℂ) * L (Complex.I • bas n j) - ((v j).im : ℂ) * L (bas n j) - Complex.I * ((v j).im : ℂ) * L (Complex.I • bas n j)) * Complex.I_sq`.
-/
theorem regM_dbarDir_eq {n : ℕ} (g : V n → ℂ) (y v : V n) :
    C.dbarDir g y v = -2 * Complex.I * ∑ j, conj (v j) * wdb n j g y := by
  set L := fderiv ℝ g y with hL
  have hsm : ∀ (c : ℂ) (w : V n), L (c • w) = c.re • L w + c.im • L (Complex.I • w) := by
    intro c w
    have hc : c • w = c.re • w + c.im • (Complex.I • w) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [hc, map_add, map_smul, map_smul]
  have hv : v = ∑ j, v j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    simp [bas]
  have hIv : Complex.I • v = ∑ j, (Complex.I * v j) • bas n j := by
    conv_lhs => rw [hv]
    simp [Finset.smul_sum, smul_smul]
  have hLv : L v = ∑ j, L (v j • bas n j) := by
    conv_lhs => rw [hv]
    rw [map_sum]
  have hLIv : L (Complex.I • v) = ∑ j, L ((Complex.I * v j) • bas n j) := by
    rw [hIv, map_sum]
  simp only [C.dbarDir, wdb, ← hL]
  rw [hLIv, hLv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsm (Complex.I * v j) (bas n j), hsm (v j) (bas n j)]
  have hcj : conj (v j) = ((v j).re : ℂ) - ((v j).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hcj]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, sub_zero, zero_add, Complex.ofReal_neg]
  linear_combination (((v j).re : ℂ) * L (Complex.I • bas n j) - ((v j).im : ℂ) * L (bas n j) -
    Complex.I * ((v j).im : ℂ) * L (Complex.I • bas n j)) * Complex.I_sq

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/- English proof (translation)
Unfold `db`. Use `split_ifs with h`. Take `⟨hch, hxs⟩` from `Classical.choose_spec h set e := Classical.choose h`. Establish `hzx : z x = e x` using `hch hxs`. Establish `h0 : φ =ᶠ[𝓝 x] 0` using `notMem_tsupport_iff_eventuallyEq.1 hx`.

Establish `htend : Tendsto e.symm (𝓝 (e x)) (𝓝 x)`. Use `(e.continuousAt_symm (e.map_source hxs)).tendsto` as an intermediate fact. Rewrite `this` using `[e.left_inv hxs]`. Then use the resulting hypothesis. Establish `h1 : (φ ∘ e.symm) =ᶠ[𝓝 (e x)] (fun _ => (0 : ℂ))` using `h0.comp_tendsto htend`. Rewrite using `[hzx, wdb, h1.fderiv_eq]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem regM_db_eq_zero_of_notMem {n : ℕ} (z : M → V n) (j : Fin n) (φ : M → ℂ) (x : M)
    (hx : x ∉ tsupport φ) : db n z j φ x = 0 := by
  unfold db
  split_ifs with h
  · obtain ⟨hch, hxs⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := hch hxs
    have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have htend : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source hxs)).tendsto
      rwa [e.left_inv hxs] at this
    have h1 : (φ ∘ e.symm) =ᶠ[𝓝 (e x)] (fun _ => (0 : ℂ)) := h0.comp_tendsto htend
    rw [hzx, wdb, h1.fderiv_eq]
    simp
  · rfl

/- English proof (translation)
Establish `hC : IsCompact (e.symm '' K)` using `hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)`. Establish `hCm : MeasurableSet (e.symm '' K)` using `hC.isClosed.measurableSet`. Establish `hCs : e.symm '' K ⊆ e.source`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `e.map_target (hKt hy)`.

Rewrite using `[← lintegral_indicator hCm, lintegral_vol_chart n z hz e he _ (hf.indicator hCm) (fun x hx => indicator_of_notMem (fun h => hx (hCs h)) _)]`. Establish `h1 : ∫⁻ y in K, f (e.symm y) = ∫⁻ y in e.target, K.indicator (fun y => f (e.symm y)) y`. Rewrite using `[lintegral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet, inter_eq_self_of_subset_left hKt]`. Rewrite using `[h1]`. Use `setLIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)` and prove the remaining obligations.

Distinguish the cases in `hyK : y ∈ K`. Rewrite using `[indicator_of_mem hyK, indicator_of_mem (mem_image_of_mem _ hyK)]`. Rewrite using `[indicator_of_notMem hyK, indicator_of_notMem]`. Introduce and unpack `⟨k, hk, hke⟩`. Establish `: k = y` using `e.symm.injOn (by simpa using hKt hk) (by simpa using hy) hke`.

Conclude with `hyK (this ▸ hk)`.
-/
theorem regM_lintegral_image {n : ℕ} (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f)
    (K : Set (V n)) (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∫⁻ y in K, f (e.symm y) = ∫⁻ x in e.symm '' K, f x ∂vol n z := by
  have hC : IsCompact (e.symm '' K) := hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hCm : MeasurableSet (e.symm '' K) := hC.isClosed.measurableSet
  have hCs : e.symm '' K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hKt hy)
  rw [← lintegral_indicator hCm, lintegral_vol_chart n z hz e he _ (hf.indicator hCm)
    (fun x hx => indicator_of_notMem (fun h => hx (hCs h)) _)]
  have h1 : ∫⁻ y in K, f (e.symm y) = ∫⁻ y in e.target, K.indicator (fun y => f (e.symm y)) y := by
    rw [lintegral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_eq_self_of_subset_left hKt]
  rw [h1]
  refine setLIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)
  by_cases hyK : y ∈ K
  · rw [indicator_of_mem hyK, indicator_of_mem (mem_image_of_mem _ hyK)]
  · rw [indicator_of_notMem hyK, indicator_of_notMem]
    rintro ⟨k, hk, hke⟩
    have : k = y := e.symm.injOn (by simpa using hKt hk) (by simpa using hy) hke
    exact hyK (this ▸ hk)

/- English proof (translation)
Rewrite using `[locallyIntegrableOn_iff e.open_target.isLocallyClosed]`. Introduce `K hKt hK`. Establish `hcont : ContinuousOn e.symm K` using `e.continuousOn_symm.mono hKt`. Establish `hmeas : AEStronglyMeasurable (F ∘ e.symm) (volume.restrict K)` using `(hFm.comp_aemeasurable (hcont.aemeasurable hK.measurableSet)).aestronglyMeasurable`. Establish `h2 : ∫⁻ y in K, ‖(F ∘ e.symm) y‖ₑ ^ 2 < ⊤`.

Establish `h3` using `regM_lintegral_image z hz e he (fun x => ‖F x‖ₑ ^ 2) (hFm.enorm.pow_const 2) K hK hKt`. Simplify using `only [Function.comp_apply]`. Rewrite using `[h3]`. Conclude with `hF.2 _ (hK.image_of_continuousOn hcont)`. Use `haveI : IsFiniteMeasure (volume.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩`.

Establish `hL2 : MemLp (F ∘ e.symm) 2 (volume.restrict K)`. Use `⟨hmeas, ?_⟩` and prove the remaining obligations. Rewrite using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]`. Simplify `h2` using `[ENNReal.rpow_two]`. Conclude with `hL2.integrable one_le_two`.
-/
theorem regM_locInt {n : ℕ} (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (F : M → ℂ) (hFm : Measurable F)
    (hF : LocalL2Isometry (vol n z) F) : LocallyIntegrableOn (F ∘ e.symm) e.target volume := by
  rw [locallyIntegrableOn_iff e.open_target.isLocallyClosed]
  intro K hKt hK
  have hcont : ContinuousOn e.symm K := e.continuousOn_symm.mono hKt
  have hmeas : AEStronglyMeasurable (F ∘ e.symm) (volume.restrict K) :=
    (hFm.comp_aemeasurable (hcont.aemeasurable hK.measurableSet)).aestronglyMeasurable
  have h2 : ∫⁻ y in K, ‖(F ∘ e.symm) y‖ₑ ^ 2 < ⊤ := by
    have h3 := regM_lintegral_image z hz e he (fun x => ‖F x‖ₑ ^ 2) (hFm.enorm.pow_const 2) K hK hKt
    simp only [Function.comp_apply]
    rw [h3]
    exact hF.2 _ (hK.image_of_continuousOn hcont)
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hL2 : MemLp (F ∘ e.symm) 2 (volume.restrict K) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa [ENNReal.rpow_two] using h2
  exact hL2.integrable one_le_two

/- English proof (translation)
Establish `hli` using `regM_locInt z hz e he F hFm hF`. Use `⟨hli, fun g hg v => ?_⟩` and prove the remaining obligations. Take `⟨hgs, hgc, hgt⟩` from `hg`. Take `⟨hφs, hφc, hφt, hφd⟩` from `hExt z hz e g he hgs hgc hgt`. Establish `hj : ∀ j, ∫ y in e.target, F (e.symm y) * wdb n j g y = 0`.

Introduce `j`. Establish `h0` using `hw _ ⟨hφs, hφc⟩ j`. Establish `hdbc` using `Smooth.continuous n z hz _ (Smooth.db n z j _ hφs)`. Rewrite using `[integral_vol_chart n z hz e he (fun x => F x * db n z j _ x) (hFm.mul hdbc.measurable) (fun x hx => by`. Rewrite `h0` using `[regM_db_eq_zero_of_notMem z j _ x (fun h => hx (hφt h)), mul_zero])]`.

Rewrite using `[← h0]`. Use `setIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)` and prove the remaining obligations. Rewrite using `[(hφd j (e.symm y) (e.map_target hy)).2, e.right_inv hy]`. Establish `hD : Continuous (fderiv ℝ g)` using `hgs.continuous_fderiv (by simp)`. Establish `hint : ∀ j, IntegrableOn (fun y => F (e.symm y) * wdb n j g y) e.target`.

Introduce `j`. Establish `hwc : Continuous (wdb n j g)`. Unfold `wdb`. Conclude with `((hD.clm_apply continuous_const).add (continuous_const.mul (hD.clm_apply continuous_const))).div_const 2`. Use `((hli.integrableOn_compact_subset hgt hgc).mul_continuousOn hwc.continuousOn hgc).of_forall_sdiff_eq_zero e.open_target.measurableSet (fun y hy => ?_)` and prove the remaining obligations.

Establish `h0 : fderiv ℝ g y = 0` using `Function.notMem_support.mp (fun h => hy.2 (support_fderiv_subset ℝ h))`. Simplify using `[wdb, h0]`. Combine the equalities or inequalities in the displayed calculation. Use `setIntegral_congr_fun e.open_target.measurableSet (fun y _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, regM_dbarDir_eq, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ j, ∫ y in e.target, (-2 * Complex.I * conj (v j)) * (F (e.symm y) * wdb n j g y) := integral_finsetSum _ (fun j _ => (hint j).const_mul _)`. Use `_ = 0 := by simp only [integral_const_mul, hj, mul_zero, Finset.sum_const_zero]`.
-/
theorem regM_weakHolo {n : ℕ} (hExt : ExtendStatement n M) (z : M → V n)
    (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (F : M → ℂ) (hFm : Measurable F) (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    C.WeakHolo e.target (F ∘ e.symm) := by
  have hli := regM_locInt z hz e he F hFm hF
  refine ⟨hli, fun g hg v => ?_⟩
  obtain ⟨hgs, hgc, hgt⟩ := hg
  obtain ⟨hφs, hφc, hφt, hφd⟩ := hExt z hz e g he hgs hgc hgt
  have hj : ∀ j, ∫ y in e.target, F (e.symm y) * wdb n j g y = 0 := by
    intro j
    have h0 := hw _ ⟨hφs, hφc⟩ j
    have hdbc := Smooth.continuous n z hz _ (Smooth.db n z j _ hφs)
    rw [integral_vol_chart n z hz e he (fun x => F x * db n z j _ x) (hFm.mul hdbc.measurable)
      (fun x hx => by
        rw [regM_db_eq_zero_of_notMem z j _ x (fun h => hx (hφt h)), mul_zero])] at h0
    rw [← h0]
    refine setIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)
    rw [(hφd j (e.symm y) (e.map_target hy)).2, e.right_inv hy]
  have hD : Continuous (fderiv ℝ g) := hgs.continuous_fderiv (by simp)
  have hint : ∀ j, IntegrableOn (fun y => F (e.symm y) * wdb n j g y) e.target := by
    intro j
    have hwc : Continuous (wdb n j g) := by
      unfold wdb
      exact ((hD.clm_apply continuous_const).add
        (continuous_const.mul (hD.clm_apply continuous_const))).div_const 2
    refine ((hli.integrableOn_compact_subset hgt hgc).mul_continuousOn hwc.continuousOn
      hgc).of_forall_sdiff_eq_zero e.open_target.measurableSet (fun y hy => ?_)
    have h0 : fderiv ℝ g y = 0 :=
      Function.notMem_support.mp (fun h => hy.2 (support_fderiv_subset ℝ h))
    simp [wdb, h0]
  calc ∫ y in e.target, (F ∘ e.symm) y * C.dbarDir g y v
      = ∫ y in e.target, ∑ j, (-2 * Complex.I * conj (v j)) * (F (e.symm y) * wdb n j g y) := by
        refine setIntegral_congr_fun e.open_target.measurableSet (fun y _ => ?_)
        simp only [Function.comp_apply, regM_dbarDir_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, ∫ y in e.target, (-2 * Complex.I * conj (v j)) * (F (e.symm y) * wdb n j g y) :=
        integral_finsetSum _ (fun j _ => (hint j).const_mul _)
    _ = 0 := by simp only [integral_const_mul, hj, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Establish `hU : ∀ e : OpenPartialHomeomorph M (V n), ∃ U : V n → ℂ, IsChart n z e → DifferentiableOn ℂ U e.target ∧ (F ∘ e.symm) =ᵐ[volume.restrict e.target] U`. Introduce `e`. Distinguish the cases in `he : IsChart n z e`. Take `⟨U, h1, h2⟩` from `hReg n e.target (F ∘ e.symm) e.open_target (regM_weakHolo hExt z hz e he F hFm hF hw)`. Conclude with `⟨U, fun _ => ⟨h1, h2⟩⟩`.

Conclude with `⟨0, fun h => absurd h he⟩`. Use `choose U hU using hU`. Establish `hagree : ∀ e₁ e₂ : OpenPartialHomeomorph M (V n), IsChart n z e₁ → IsChart n z e₂ → ∀ x ∈ e₁.source ∩ e₂.source, U e₁ (z x) = U e₂ (z x)`. Introduce `e₁ e₂ h₁ h₂ x hx`. Establish `hWo : IsOpen (e₁.source ∩ e₂.source)` using `e₁.open_source.inter e₂.open_source`.

Use `set Ω := e₁.target ∩ e₁.symm ⁻¹' (e₁.source ∩ e₂.source) with hΩdef`. Establish `hΩo : IsOpen Ω` using `e₁.isOpen_inter_preimage_symm hWo`. Establish `hΩ1 : Ω ⊆ e₁.target` using `inter_subset_left`. Establish `hkey : ∀ y ∈ Ω, e₂.symm y = e₁.symm y ∧ y ∈ e₂.target`. Introduce `y hy`.

Establish `hw1` using `hy.2.1`. Establish `hw2` using `hy.2.2`. Establish `hy' : y = e₂ (e₁.symm y)`. Rewrite using `[← h₂ hw2, h₁ hw1, e₁.right_inv hy.1]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `(congrArg e₂.symm hy').trans (e₂.left_inv hw2)`. Rewrite using `[hy']`. Conclude with `e₂.map_source hw2`. Establish `hΩ2 : Ω ⊆ e₂.target` using `fun y hy => (hkey y hy).2`. Establish `heq` using `C.ae_eq_eqOn hΩo ((hU e₁ h₁).1.continuousOn.mono hΩ1) ((hU e₂ h₂).1.continuousOn.mono hΩ2) (by`.

Establish `a1` using `ae_restrict_of_ae_restrict_of_subset hΩ1 (hU e₁ h₁).2`. Establish `a2` using `ae_restrict_of_ae_restrict_of_subset hΩ2 (hU e₂ h₂).2`. Use `filter_upwards [a1, a2, ae_restrict_mem hΩo.measurableSet] with y hy1 hy2 hyΩ`. Rewrite using `[← hy1, ← hy2]`. Simplify using `only [Function.comp_apply, (hkey y hyΩ).1])`.

Establish `hzx : z x ∈ Ω`. Rewrite using `[h₁ hx.1]`. Conclude with `⟨e₁.map_source hx.1, by simpa [e₁.left_inv hx.1] using hx⟩`. Conclude with `heq hzx`. Use `choose ec hec hxc using exists_chart n z hz`.

Set `G : M → ℂ` to `fun x => U (ec x) (z x)`. Establish `hGe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → ∀ y ∈ e.target, G (e.symm y) = U e y`. Introduce `e he y hy`. Establish `hs : e.symm y ∈ e.source` using `e.map_target hy`. Use `show U (ec (e.symm y)) (z (e.symm y)) = U e y`.

Rewrite using `[hagree (ec (e.symm y)) e (hec _) he (e.symm y) ⟨hxc _, hs⟩, chart_z_symm n z e he y hy]`. Establish `hG : Holo n z G`. Introduce `e he`. Conclude with `(hU e he).1.congr (fun y hy => hGe e he y hy)`. Establish `hGc : Continuous G` using `Smooth.continuous n z hz G (Holo.smooth n z G hG)`.

Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Establish `hloc : ∀ x, ∀ᵐ y ∂(vol n z).restrict (ec x).source, F y = G y`. Introduce `x`. Rewrite using `[vol_restrict_source n z hz (ec x) (hec x), ae_map_iff ((ec x).continuousOn_symm.aemeasurable (ec x).open_target.measurableSet) (measurableSet_eq_fun hFm hGc.measurable)]`. Use `filter_upwards [(hU (ec x) (hec x)).2, ae_restrict_mem (ec x).open_target.measurableSet] with y hy hyt`.

Rewrite using `[hGe (ec x) (hec x) y hyt]`. Conclude with `hy`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun x => (ec x).source) (fun x => (ec x).open_source)`. Establish `hcov : (⋃ x ∈ T, (ec x).source) = univ`. Rewrite using `[hTU]`.

Conclude with `eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hxc x⟩`. Rewrite using `[EventuallyEq, ← Measure.restrict_univ (μ := vol n z), ← hcov, ae_restrict_biUnion_iff _ hTc]`. Conclude with `fun x _ => hloc x`.
-/
theorem regM_of_measurable {n : ℕ} (hReg : C.RegStatement) (hExt : ExtendStatement n M)
    (z : M → V n) (hz : IsLocalHomeomorph z) (F : M → ℂ) (hFm : Measurable F)
    (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    ∃ G : M → ℂ, Holo n z G ∧ F =ᵐ[vol n z] G := by
  have hU : ∀ e : OpenPartialHomeomorph M (V n), ∃ U : V n → ℂ, IsChart n z e →
      DifferentiableOn ℂ U e.target ∧ (F ∘ e.symm) =ᵐ[volume.restrict e.target] U := by
    intro e
    by_cases he : IsChart n z e
    · obtain ⟨U, h1, h2⟩ := hReg n e.target (F ∘ e.symm) e.open_target
        (regM_weakHolo hExt z hz e he F hFm hF hw)
      exact ⟨U, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose U hU using hU
  have hagree : ∀ e₁ e₂ : OpenPartialHomeomorph M (V n), IsChart n z e₁ → IsChart n z e₂ →
      ∀ x ∈ e₁.source ∩ e₂.source, U e₁ (z x) = U e₂ (z x) := by
    intro e₁ e₂ h₁ h₂ x hx
    have hWo : IsOpen (e₁.source ∩ e₂.source) := e₁.open_source.inter e₂.open_source
    set Ω := e₁.target ∩ e₁.symm ⁻¹' (e₁.source ∩ e₂.source) with hΩdef
    have hΩo : IsOpen Ω := e₁.isOpen_inter_preimage_symm hWo
    have hΩ1 : Ω ⊆ e₁.target := inter_subset_left
    have hkey : ∀ y ∈ Ω, e₂.symm y = e₁.symm y ∧ y ∈ e₂.target := by
      intro y hy
      have hw1 := hy.2.1
      have hw2 := hy.2.2
      have hy' : y = e₂ (e₁.symm y) := by
        rw [← h₂ hw2, h₁ hw1, e₁.right_inv hy.1]
      refine ⟨?_, ?_⟩
      · exact (congrArg e₂.symm hy').trans (e₂.left_inv hw2)
      · rw [hy']; exact e₂.map_source hw2
    have hΩ2 : Ω ⊆ e₂.target := fun y hy => (hkey y hy).2
    have heq := C.ae_eq_eqOn hΩo ((hU e₁ h₁).1.continuousOn.mono hΩ1)
      ((hU e₂ h₂).1.continuousOn.mono hΩ2) (by
        have a1 := ae_restrict_of_ae_restrict_of_subset hΩ1 (hU e₁ h₁).2
        have a2 := ae_restrict_of_ae_restrict_of_subset hΩ2 (hU e₂ h₂).2
        filter_upwards [a1, a2, ae_restrict_mem hΩo.measurableSet] with y hy1 hy2 hyΩ
        rw [← hy1, ← hy2]
        simp only [Function.comp_apply, (hkey y hyΩ).1])
    have hzx : z x ∈ Ω := by
      rw [h₁ hx.1]
      exact ⟨e₁.map_source hx.1, by simpa [e₁.left_inv hx.1] using hx⟩
    exact heq hzx
  choose ec hec hxc using exists_chart n z hz
  let G : M → ℂ := fun x => U (ec x) (z x)
  have hGe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ∀ y ∈ e.target, G (e.symm y) = U e y := by
    intro e he y hy
    have hs : e.symm y ∈ e.source := e.map_target hy
    show U (ec (e.symm y)) (z (e.symm y)) = U e y
    rw [hagree (ec (e.symm y)) e (hec _) he (e.symm y) ⟨hxc _, hs⟩, chart_z_symm n z e he y hy]
  have hG : Holo n z G := by
    intro e he
    exact (hU e he).1.congr (fun y hy => hGe e he y hy)
  have hGc : Continuous G := Smooth.continuous n z hz G (Holo.smooth n z G hG)
  refine ⟨G, hG, ?_⟩
  have hloc : ∀ x, ∀ᵐ y ∂(vol n z).restrict (ec x).source, F y = G y := by
    intro x
    rw [vol_restrict_source n z hz (ec x) (hec x),
      ae_map_iff ((ec x).continuousOn_symm.aemeasurable (ec x).open_target.measurableSet)
        (measurableSet_eq_fun hFm hGc.measurable)]
    filter_upwards [(hU (ec x) (hec x)).2, ae_restrict_mem (ec x).open_target.measurableSet]
      with y hy hyt
    rw [hGe (ec x) (hec x) y hyt]
    exact hy
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => (ec x).source)
    (fun x => (ec x).open_source)
  have hcov : (⋃ x ∈ T, (ec x).source) = univ := by
    rw [hTU]; exact eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hxc x⟩
  rw [EventuallyEq, ← Measure.restrict_univ (μ := vol n z), ← hcov,
    ae_restrict_biUnion_iff _ hTc]
  exact fun x _ => hloc x

/- English proof (translation)
Introduce `z hz F hF hw`. Take `⟨hFae, hF2⟩` from `hF`. Establish `hFF' : F =ᵐ[vol n z] hFae.mk F` using `hFae.ae_eq_mk`. Establish `hF'm : Measurable (hFae.mk F)` using `hFae.stronglyMeasurable_mk.measurable`. Apply the tactic sequence `have hF'L : LocalL2Isometry (vol n z) (hFae.mk F) := by`.

Use `⟨hFae.stronglyMeasurable_mk.aestronglyMeasurable, fun C hC => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hw' : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, hFae.mk F x * db n z j φ x ∂vol n z = 0`. Introduce `φ hφ j`. Rewrite using `[← hw φ hφ j]`.

Conclude with `integral_congr_ae (hFF'.mono fun x hx => by simp only [hx])`. Take `⟨G, hG, hG'⟩` from `regM_of_measurable hReg hExt z hz (hFae.mk F) hF'm hF'L hw'`. Conclude with `⟨G, hG, hFF'.trans hG'⟩`.
-/
theorem regM (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : C.RegStatement) (hExt : ExtendStatement n M) : RegMStatement n M := by
  intro z hz F hF hw
  obtain ⟨hFae, hF2⟩ := hF
  have hFF' : F =ᵐ[vol n z] hFae.mk F := hFae.ae_eq_mk
  have hF'm : Measurable (hFae.mk F) := hFae.stronglyMeasurable_mk.measurable
  have hF'L : LocalL2Isometry (vol n z) (hFae.mk F) := by
    refine ⟨hFae.stronglyMeasurable_mk.aestronglyMeasurable, fun C hC => ?_⟩
    calc ∫⁻ x in C, ‖hFae.mk F x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in C, ‖F x‖ₑ ^ 2 ∂vol n z :=
          lintegral_congr_ae (ae_restrict_of_ae (hFF'.mono fun x hx => by simp only [hx]))
      _ < ⊤ := hF2 C hC
  have hw' : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n,
      ∫ x, hFae.mk F x * db n z j φ x ∂vol n z = 0 := by
    intro φ hφ j
    rw [← hw φ hφ j]
    exact integral_congr_ae (hFF'.mono fun x hx => by simp only [hx])
  obtain ⟨G, hG, hG'⟩ := regM_of_measurable hReg hExt z hz (hFae.mk F) hF'm hF'L hw'
  exact ⟨G, hG, hFF'.trans hG'⟩

end

end ReciprocityTheory.L2DbarEstimates.F
