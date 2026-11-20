import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SmoothRLog
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

noncomputable section

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Conclude with `Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩`.
-/
theorem near_vsq_pos {p : ℕ} (w : Fin p → ℂ) (hw : w ≠ 0) : 0 < vsq w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  exact Finset.sum_pos' (fun j _ => by positivity)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

/- English proof (translation)
Unfold `vsq gv`. Use `ContDiffOn.sum fun l _ => ?_` and prove the remaining obligations. Establish `hd : DifferentiableOn ℂ (g l ∘ e.symm) e.target` using `hg l e he`. Establish `ho : IsOpen e.target` using `e.open_target`. Establish `h0 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target` using `C.holo_contDiffOn_complex ho hd`.

Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target` using `h0.restrict_scalars ℝ`. Conclude with `(contDiff_norm_sq ℝ).comp_contDiffOn h1`.
-/
private theorem contDiffOn_vsq_gv_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => vsq (gv g (e.symm y))) e.target := by
  unfold vsq gv
  refine ContDiffOn.sum fun l _ => ?_
  have hd : DifferentiableOn ℂ (g l ∘ e.symm) e.target := hg l e he
  have ho : IsOpen e.target := e.open_target
  have h0 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    C.holo_contDiffOn_complex ho hd
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    h0.restrict_scalars ℝ
  exact (contDiff_norm_sq ℝ).comp_contDiffOn h1

/- English proof (translation)
Introduce `e he`. Establish `h1` using `contDiffOn_vsq_gv_comp_chart_symm n z g hg e he`. Establish `h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log (vsq (gv g (e.symm y)))) e.target` using `h1.log fun y _ => (near_vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne'`. Conclude with `Complex.ofRealCLM.contDiff.comp_contDiffOn h2`.
-/
theorem near_smoothR_log {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (hN : ∀ x, gv g x ≠ 0) : SmoothR n z (fun x => Real.log (vsq (gv g x))) := by
  intro e he
  have h1 := contDiffOn_vsq_gv_comp_chart_symm n z g hg e he
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log (vsq (gv g (e.symm y)))) e.target :=
    h1.log fun y _ => (near_vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h2

/- English proof (translation)
Unfold `vsq gv`. Conclude with `continuous_finset_sum _ fun i _ => ((hg i).norm).pow 2`.
-/
theorem near_continuous_vsq {M : Type*} [TopologicalSpace M] {p : ℕ} (g : Fin p → M → ℂ)
    (hg : ∀ l, Continuous (g l)) : Continuous (fun x => vsq (gv g x)) := by
  unfold vsq gv
  exact continuous_finset_sum _ fun i _ => ((hg i).norm).pow 2

/- English proof (translation)
Establish `hc : Continuous (fun x => (f x : ℂ))`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨e, hx, he⟩` from `hz x`. Establish `hch : IsChart n z e` using `fun y _ => by rw [he]`.

Establish `h1` using `(hf e hch).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))`. Establish `h2 : ContinuousAt (((fun y => (f y : ℂ)) ∘ e.symm) ∘ e) x` using `ContinuousAt.comp (f := e) h1 (e.continuousAt hx)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [e.open_source.mem_nhds hx] with y hy`. Simplify using `[e.left_inv hy]`.

Conclude with `(Complex.continuous_re.comp hc).congr fun x => by simp`.
-/
theorem near_continuous_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hx, he⟩ := hz x
    have hch : IsChart n z e := fun y _ => by rw [he]
    have h1 := (hf e hch).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
    have h2 : ContinuousAt (((fun y => (f y : ℂ)) ∘ e.symm) ∘ e) x :=
      ContinuousAt.comp (f := e) h1 (e.continuousAt hx)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

/- English proof (translation)
Introduce `e he`. Establish `hu' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ e.symm) e.target` using `(C.holo_contDiffOn_complex e.open_target (hu e he)).restrict_scalars ℝ`. Establish `hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i ∘ e.symm) e.target` using `(C.holo_contDiffOn_complex e.open_target (hg i e he)).restrict_scalars ℝ`. Establish `hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (g i (e.symm y))) e.target` using `Complex.conjCLE.contDiff.comp_contDiffOn hg'`. Establish `hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (((vsq (gv g (e.symm y)))⁻¹ : ℝ) : ℂ)) e.target` using `Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_vsq_gv_comp_chart_symm n z g hg e he).inv fun y _ => (near_vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne')`.

Establish `hnum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y))) e.target` using `hu'.mul hc`. Use `show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y)) / ((vsq (gv g (e.symm y)) : ℝ) : ℂ)) e.target`. Conclude with `(hnum.mul hv).congr fun y _ => by simp [div_eq_mul_inv]`.
-/
theorem near_smooth_slice {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (hN : ∀ x, gv g x ≠ 0) (u : M → ℂ) (hu : Holo n z u) (i : Fin p) :
    Smooth n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) := by
  intro e he
  have hu' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hu e he)).restrict_scalars ℝ
  have hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hg i e he)).restrict_scalars ℝ
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (g i (e.symm y))) e.target :=
    Complex.conjCLE.contDiff.comp_contDiffOn hg'
  have hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (((vsq (gv g (e.symm y)))⁻¹ : ℝ) : ℂ))
      e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_vsq_gv_comp_chart_symm n z g hg e he).inv
      fun y _ => (near_vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne')
  have hnum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y))) e.target := hu'.mul hc
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y)) /
    ((vsq (gv g (e.symm y)) : ℝ) : ℂ)) e.target
  exact (hnum.mul hv).congr fun y _ => by simp [div_eq_mul_inv]

/- English proof (translation)
Introduce `X p g φ₀ t hH hp hg hN hφ₀ hLφ₀ ht u u' hu' huu' F0 hF0`. Establish `hz` using `X.isLocalHomeomorph`. Establish `hgc : ∀ l, Continuous (g l)` using `fun l => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg l))`. Establish `huc : Continuous u'` using `Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hu')`. Establish `hNc` using `near_continuous_vsq g hgc`.

Establish `hNp : ∀ x, 0 < vsq (gv g x)` using `fun x => near_vsq_pos _ (hN x)`. Establish `hW` using `skodaWeight n M X.z hz p g φ₀ t hg hN hφ₀ hLφ₀ ht.le`. Establish `hWc : Continuous (skW g φ₀ t)` using `near_continuous_of_smoothR n X.z hz _ hW.1`. Establish `hlogc : Continuous (fun x => Real.log (vsq (gv g x)))` using `hNc.log fun x => (hNp x).ne'`. Establish `hTr` using `fun x => perpTrace p (gv g x) (hN x)`.

Set `F0f : M × Fin p → ℂ` to `fun q => u' q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)`. Set `c : M × Fin p → ℝ` to `fun q => ‖u' q.1‖ ^ 2 * (1 - ‖g q.2 q.1‖ ^ 2 / vsq (gv g q.1)) / (t * vsq (gv g q.1))`. Establish `hc0 : ∀ q, 0 ≤ c q` using `fun q => div_nonneg (mul_nonneg (by positivity) ((hTr q.1).1 q.2)) (mul_pos ht (hNp q.1)).le`. Establish `hcm : Measurable c` using `measurable_from_prod_countable_left fun i => by`. Establish `: Continuous (fun x => ‖u' x‖ ^ 2 * (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) / (t * vsq (gv g x)))` using `((huc.norm.pow 2).mul (continuous_const.sub (((hgc i).norm.pow 2).div hNc fun x => (hNp x).ne'))).div (continuous_const.mul hNc) fun x => (mul_pos ht (hNp x)).ne'`.

Conclude with `this.measurable`. Establish `hsl : ∀ i, Smooth n X.z (fun x => F0f (x, i))` using `fun i => near_smooth_slice n X.z hz g hg hN u' hu' i`. Establish `hF0fm : Measurable F0f` using `measurable_from_prod_countable_left fun i => (Smooth.continuous n X.z hz _ (hsl i)).measurable`. Establish `hF0fs : Smooth n (fun q : M × Fin p => X.z q.1) F0f` using `(smooth_prodFin_iff n X.z hz p F0f).2 hsl`. Establish `hph' : SmoothR n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1)` using `(smooth_prodFin_iff n X.z hz p _).2 fun _ => hW.1`.

Establish `hLph' : LeviNonneg n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1)`. Introduce and unpack `⟨x, i⟩ ξ`. Rewrite using `[levi_prodFin n X.z hz p]`. Conclude with `hW.2.1 x ξ`. Establish `hfm : Measurable (fun q => ENNReal.ofReal (c q))` using `ENNReal.measurable_ofReal.comp hcm`.

Establish `hpt : ∀ (q : M × Fin p) (ξ : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n (fun q : M × Fin p => X.z q.1) F0f q ξ‖ ^ 2) ≤ ENNReal.ofReal (c q) * ENNReal.ofReal (Levi n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) q ξ).re`. Introduce and unpack `⟨x, i⟩ ξ`. Establish `hd : dbarDot n (fun q : M × Fin p => X.z q.1) F0f (x, i) ξ = dbarDot n X.z (fun y => F0f (y, i)) x ξ`. Simplify using `only [dbarDot, db_prodFin n X.z hz p]`. Rewrite using `[hd, levi_prodFin n X.z hz p, ← ENNReal.ofReal_mul (hc0 _)]`.

Conclude with `ENNReal.ofReal_le_ofReal (skodaHyp n M X.z hz p g φ₀ t u' hg hu' hN hφ₀ hLφ₀ ht x i ξ)`. Take `⟨F, hFh, hFb⟩` from `hH (EtaleStein.prodFin n X p) (fun q => skW g φ₀ t q.1) F0f (fun q => ENNReal.ofReal (c q)) hph' hLph' hF0fs hfm hpt`. Establish `hph'm : Measurable (fun q : M × Fin p => skW g φ₀ t q.1)` using `hWc.measurable.comp measurable_fst`. Establish `hψm : Measurable (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))` using `(hWc.add hlogc).measurable`. Establish `hpt0 : 0 ≤ ((p : ℝ) - 1) / t` using `div_nonneg (sub_nonneg.2 (by exact_mod_cast hp)) ht.le`.

Establish `hEm : Measurable (fun q : M × Fin p => ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1)))` using `hfm.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'm.neg))`. Establish `hR : ∫⁻ q, ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1)) ∂vol n (fun q : M × Fin p => X.z q.1) = ENNReal.ofReal (((p : ℝ) - 1) / t) * wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))`. Establish `hmi : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable (fun x : M => ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1)))` using `fun i _ => hEm.comp measurable_prodMk_right`. Rewrite using `[lintegral_vol_prodFin n X.z hz p _ hEm, ← lintegral_finsetSum _ hmi]`. Unfold `wint`.

Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hs : ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) = (p : ℝ) - 1` using `(hTr x).2`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Establish `hsum : ∑ i, c (x, i) * Real.exp (-skW g φ₀ t x) = (‖u' x‖ ^ 2 / (t * vsq (gv g x)) * Real.exp (-skW g φ₀ t x)) * ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x))`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hNx` using `hNp x`. Rewrite using `[hsum, hs, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hNx]`. Clear the denominators using the available nonvanishing facts. Use `_ = _ := ENNReal.ofReal_mul hpt0`. Establish `hl2` using `l2w n M X.z _ hψm`.

Establish `hl2'` using `l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1) _ hph'm`. Take `⟨hu_fin, hu_norm⟩` from `hl2.2.1 u`. Establish `hwu : wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) = wint n X.z (u : M → ℂ) (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))` using `lintegral_congr_ae (huu'.mono fun x hx => by dsimp only; rw [hx])`. Establish `hR_fin : ENNReal.ofReal (((p : ℝ) - 1) / t) * wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) < ⊤` using `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hwu ▸ hu_fin)`. Establish `hFb' : wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1) ≤ ENNReal.ofReal (((p : ℝ) - 1) / t) * wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))` using `hR ▸ hFb`.

Establish `hwF0 : wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) < ⊤`. Establish `h1` using `(hl2'.2.1 F0).1`. Establish `h2 : wint n (fun q : M × Fin p => X.z q.1) (F0 : M × Fin p → ℂ) (fun q => skW g φ₀ t q.1) = wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1)` using `lintegral_congr_ae (hF0.mono fun q hq => by dsimp only at hq ⊢; rw [hq])`. Conclude with `h2 ▸ h1`. Establish `hFc : Continuous F` using `Smooth.continuous n _ (EtaleStein.prodFin n X p).isLocalHomeomorph _ (Holo.smooth n _ _ hFh)`.

Establish `hwF : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) < ⊤`. Establish `hle : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) ≤ 2 * wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) + 2 * wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1)`. Unfold `wint`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_add_left]`. Use `lintegral_mono fun q => ?_` and prove the remaining obligations.

Establish `hE` using `Real.exp_pos (-skW g φ₀ t q.1)`. Establish `h3 : ‖F q‖ ≤ ‖F0f q‖ + ‖F0f q - F q‖`. Simplify using `using norm_sub_le (F0f q) (F0f q - F q)`. Establish `h4 : ‖F q‖ ^ 2 ≤ 2 * ‖F0f q‖ ^ 2 + 2 * ‖F0f q - F q‖ ^ 2`. Use polynomial arithmetic with `[sq_nonneg (‖F0f q‖ - ‖F0f q - F q‖), norm_nonneg (F q), norm_nonneg (F0f q), norm_nonneg (F0f q - F q)]`.

Rewrite using `[show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h4 hE.le]`. Conclude with `measurable_const.mul (ENNReal.measurable_ofReal.comp (((hF0fm.norm.pow_const 2).mul (Real.measurable_exp.comp hph'm.neg))))`. Conclude with `hle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwF0, ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hFb'.trans_lt hR_fin)⟩)`.

Take `⟨Fc, hFcF⟩` from `hl2'.2.2 F hFc.aestronglyMeasurable hwF`. Use `⟨Fc, ⟨F, hFh, (hl2'.1 (fun q => (Fc : M × Fin p → ℂ) q = F q)).2 hFcF⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(hl2'.2.1 (F0 - Fc)).2]`. Establish `hsub : wint n (fun q : M × Fin p => X.z q.1) ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ) (fun q => skW g φ₀ t q.1) = wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1)`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Establish `h1` using `(hl2'.1 (fun q => ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ) q = ((F0 : M × Fin p → ℂ) - (Fc : M × Fin p → ℂ)) q)).1 (Lp.coeFn_sub F0 Fc)`. Use `filter_upwards [h1, hF0, hFcF] with q h1 h2 h3`. Rewrite using `[h1, Pi.sub_apply, h2, h3]`. Rewrite using `[hsub]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem skodaNear (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaNearStatement n M := by
  intro X p g φ₀ t hH hp hg hN hφ₀ hLφ₀ ht u u' hu' huu' F0 hF0
  have hz := X.isLocalHomeomorph
  have hgc : ∀ l, Continuous (g l) := fun l =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg l))
  have huc : Continuous u' := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hu')
  have hNc := near_continuous_vsq g hgc
  have hNp : ∀ x, 0 < vsq (gv g x) := fun x => near_vsq_pos _ (hN x)
  have hW := skodaWeight n M X.z hz p g φ₀ t hg hN hφ₀ hLφ₀ ht.le
  have hWc : Continuous (skW g φ₀ t) := near_continuous_of_smoothR n X.z hz _ hW.1
  have hlogc : Continuous (fun x => Real.log (vsq (gv g x))) :=
    hNc.log fun x => (hNp x).ne'
  have hTr := fun x => perpTrace p (gv g x) (hN x)
  let F0f : M × Fin p → ℂ := fun q =>
    u' q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)
  let c : M × Fin p → ℝ := fun q =>
    ‖u' q.1‖ ^ 2 * (1 - ‖g q.2 q.1‖ ^ 2 / vsq (gv g q.1)) / (t * vsq (gv g q.1))
  have hc0 : ∀ q, 0 ≤ c q := fun q =>
    div_nonneg (mul_nonneg (by positivity) ((hTr q.1).1 q.2)) (mul_pos ht (hNp q.1)).le
  have hcm : Measurable c := measurable_from_prod_countable_left fun i => by
    have : Continuous (fun x =>
        ‖u' x‖ ^ 2 * (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) / (t * vsq (gv g x))) :=
      ((huc.norm.pow 2).mul (continuous_const.sub
        (((hgc i).norm.pow 2).div hNc fun x => (hNp x).ne'))).div
        (continuous_const.mul hNc) fun x => (mul_pos ht (hNp x)).ne'
    exact this.measurable
  have hsl : ∀ i, Smooth n X.z (fun x => F0f (x, i)) := fun i =>
    near_smooth_slice n X.z hz g hg hN u' hu' i
  have hF0fm : Measurable F0f := measurable_from_prod_countable_left fun i =>
    (Smooth.continuous n X.z hz _ (hsl i)).measurable
  have hF0fs : Smooth n (fun q : M × Fin p => X.z q.1) F0f :=
    (smooth_prodFin_iff n X.z hz p F0f).2 hsl
  have hph' : SmoothR n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) :=
    (smooth_prodFin_iff n X.z hz p _).2 fun _ => hW.1
  have hLph' : LeviNonneg n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z hz p]
    exact hW.2.1 x ξ
  have hfm : Measurable (fun q => ENNReal.ofReal (c q)) := ENNReal.measurable_ofReal.comp hcm
  have hpt : ∀ (q : M × Fin p) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n (fun q : M × Fin p => X.z q.1) F0f q ξ‖ ^ 2) ≤
        ENNReal.ofReal (c q) *
          ENNReal.ofReal (Levi n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) q ξ).re := by
    rintro ⟨x, i⟩ ξ
    have hd : dbarDot n (fun q : M × Fin p => X.z q.1) F0f (x, i) ξ =
        dbarDot n X.z (fun y => F0f (y, i)) x ξ := by
      simp only [dbarDot, db_prodFin n X.z hz p]
    rw [hd, levi_prodFin n X.z hz p, ← ENNReal.ofReal_mul (hc0 _)]
    exact ENNReal.ofReal_le_ofReal (skodaHyp n M X.z hz p g φ₀ t u' hg hu' hN hφ₀ hLφ₀ ht x i ξ)
  obtain ⟨F, hFh, hFb⟩ := hH (EtaleStein.prodFin n X p) (fun q => skW g φ₀ t q.1) F0f
    (fun q => ENNReal.ofReal (c q)) hph' hLph' hF0fs hfm hpt
  have hph'm : Measurable (fun q : M × Fin p => skW g φ₀ t q.1) :=
    hWc.measurable.comp measurable_fst
  have hψm : Measurable (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    (hWc.add hlogc).measurable
  have hpt0 : 0 ≤ ((p : ℝ) - 1) / t :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hp)) ht.le
  have hEm : Measurable (fun q : M × Fin p =>
      ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))) :=
    hfm.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'm.neg))
  have hR : ∫⁻ q, ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))
      ∂vol n (fun q : M × Fin p => X.z q.1) =
      ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := by
    have hmi : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable (fun x : M =>
        ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))) :=
      fun i _ => hEm.comp measurable_prodMk_right
    rw [lintegral_vol_prodFin n X.z hz p _ hEm, ← lintegral_finsetSum _ hmi]
    unfold wint
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    have hs : ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) = (p : ℝ) - 1 := (hTr x).2
    calc ∑ i, ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))
        = ∑ i, ENNReal.ofReal (c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hc0 _)).symm
      _ = ENNReal.ofReal (∑ i, c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg (hc0 _) (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (((p : ℝ) - 1) / t *
            (‖u' x‖ ^ 2 * Real.exp (-(skW g φ₀ t x + Real.log (vsq (gv g x)))))) := by
          congr 1
          have hsum : ∑ i, c (x, i) * Real.exp (-skW g φ₀ t x) =
              (‖u' x‖ ^ 2 / (t * vsq (gv g x)) * Real.exp (-skW g φ₀ t x)) *
                ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [c]
            ring
          have hNx := hNp x
          rw [hsum, hs, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hNx]
          field_simp
      _ = _ := ENNReal.ofReal_mul hpt0
  have hl2 := l2w n M X.z _ hψm
  have hl2' := l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1) _ hph'm
  obtain ⟨hu_fin, hu_norm⟩ := hl2.2.1 u
  have hwu : wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) =
      wint n X.z (u : M → ℂ) (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    lintegral_congr_ae (huu'.mono fun x hx => by dsimp only; rw [hx])
  have hR_fin : ENNReal.ofReal (((p : ℝ) - 1) / t) *
      wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hwu ▸ hu_fin)
  have hFb' : wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
      (fun q => skW g φ₀ t q.1) ≤ ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := hR ▸ hFb
  have hwF0 : wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) < ⊤ := by
    have h1 := (hl2'.2.1 F0).1
    have h2 : wint n (fun q : M × Fin p => X.z q.1) (F0 : M × Fin p → ℂ)
        (fun q => skW g φ₀ t q.1) = wint n (fun q : M × Fin p => X.z q.1) F0f
        (fun q => skW g φ₀ t q.1) := lintegral_congr_ae (hF0.mono fun q hq => by dsimp only at hq ⊢; rw [hq])
    exact h2 ▸ h1
  have hFc : Continuous F :=
    Smooth.continuous n _ (EtaleStein.prodFin n X p).isLocalHomeomorph _ (Holo.smooth n _ _ hFh)
  have hwF : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) < ⊤ := by
    have hle : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) ≤
        2 * wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) +
          2 * wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
            (fun q => skW g φ₀ t q.1) := by
      unfold wint
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_add_left]
      · refine lintegral_mono fun q => ?_
        have hE := Real.exp_pos (-skW g φ₀ t q.1)
        have h3 : ‖F q‖ ≤ ‖F0f q‖ + ‖F0f q - F q‖ := by
          simpa using norm_sub_le (F0f q) (F0f q - F q)
        have h4 : ‖F q‖ ^ 2 ≤ 2 * ‖F0f q‖ ^ 2 + 2 * ‖F0f q - F q‖ ^ 2 := by
          nlinarith [sq_nonneg (‖F0f q‖ - ‖F0f q - F q‖), norm_nonneg (F q),
            norm_nonneg (F0f q), norm_nonneg (F0f q - F q)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_le_mul_of_nonneg_right h4 hE.le]
      · exact measurable_const.mul (ENNReal.measurable_ofReal.comp
          (((hF0fm.norm.pow_const 2).mul (Real.measurable_exp.comp hph'm.neg))))
    exact hle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwF0,
      ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hFb'.trans_lt hR_fin)⟩)
  obtain ⟨Fc, hFcF⟩ := hl2'.2.2 F hFc.aestronglyMeasurable hwF
  refine ⟨Fc, ⟨F, hFh, (hl2'.1 (fun q => (Fc : M × Fin p → ℂ) q = F q)).2 hFcF⟩, ?_⟩
  rw [(hl2'.2.1 (F0 - Fc)).2]
  have hsub : wint n (fun q : M × Fin p => X.z q.1) ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ)
      (fun q => skW g φ₀ t q.1) =
      wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1) := by
    refine lintegral_congr_ae ?_
    have h1 := (hl2'.1 (fun q => ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ) q =
      ((F0 : M × Fin p → ℂ) - (Fc : M × Fin p → ℂ)) q)).1 (Lp.coeFn_sub F0 Fc)
    filter_upwards [h1, hF0, hFcF] with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [hsub]
  calc _ ≤ (ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))).toReal :=
        ENNReal.toReal_mono hR_fin.ne hFb'
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpt0, hwu, hu_norm]

end

end ReciprocityTheory.L2DbarEstimates.H
