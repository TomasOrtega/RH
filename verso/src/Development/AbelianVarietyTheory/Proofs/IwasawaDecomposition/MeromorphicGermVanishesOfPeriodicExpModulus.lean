import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

/- English proof (translation)
Introduce `hpos`. Use `set F := Function.Periodic.cuspFunction M f with hF`. Establish `hF0 : F 0 = 0` using `Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0`. Establish `hd0 : DifferentiableAt ℂ F 0` using `Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)`. Establish `hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q` using `Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd`.

Establish `hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re` using `by filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0`. Rewrite using `[hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]` and apply the resulting hypothesis. Establish `hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q` using `by filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq`. Distinguish the cases in `hq0 : q = 0`. Substitute `hq0` using the available equality.

Conclude with `hd0.neg.cexp`. Conclude with `(hq hq0).neg.cexp`. Establish `hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0` using `by filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq`. Distinguish the cases in `hq0 : q = 0`. Substitute `hq0` using the available equality.

Conclude with `le_rfl`. Use `hq hq0` as an intermediate fact. Simplify using `only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]`. Simplify using `using this.le`. Establish `hc` using `Complex.eventually_eq_of_isLocalMax_norm hd2 hmax`.

Take `⟨q, hq1, hq2⟩` from `(hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists`. Use `congrArg norm hq2` as an intermediate fact. Simplify using `only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this`. Simplify using `at this`. Conclude with `hq1.ne' this`.
-/
theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

/- English proof (translation)
Introduce `ht`. Establish `hT : ∀ᶠ w in imTop, T < w.im` using `(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)`. Establish `hopen : IsOpen {w : ℂ | T < w.im}` using `isOpen_lt continuous_const Complex.continuous_im`. Establish `hpos : ∀ᶠ w in imTop, 0 < (L w).re` using `ht.eventually (eventually_gt_atTop 0)`. Use `set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf`.

Establish `hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹` using `fun w hw => if_pos hw`. Use `not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `w`. Distinguish the cases in `hw : T < w.im`. Establish `hw' : T < (w + M).im` using `by simpa using hw`.

Rewrite using `[hfe _ hw, hfe _ hw', hper w hw]`. Establish `hw' : ¬ T < (w + M).im` using `by simpa using hw`. Simplify using `only [hf, if_neg hw, if_neg hw']`. Use `filter_upwards [hT, hpos] with w hw hw0`. Establish `hne : L w ≠ 0` using `fun h => by simp [h] at hw0`.

Use `((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz`. Establish `h1 : Tendsto (fun w => ‖L w‖) imTop atTop` using `tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht`. Establish `h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0)`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`.

Simplify using `only [norm_inv]`. Conclude with `h1.inv_tendsto_atTop`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hT] with w hw using (hfe w hw).symm`. Use `filter_upwards [hT, hpos] with w hw hw0`.

Establish `hne : L w ≠ 0` using `fun h => by simp [h] at hw0`. Rewrite using `[hfe w hw, Complex.inv_re]`. Conclude with `div_pos hw0 (Complex.normSq_pos.mpr hne)`.
-/
theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

/- English proof (translation)
Introduce `p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab`. Establish `hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ)` using `Metric.ball_mem_nhds _ hr`. Establish `hmer : MeromorphicAt h 0`. Use `((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0`.

Take `⟨h1, h2⟩` from `hab u hu hu0`. Simplify using `only [Pi.div_apply]`. Rewrite using `[← h2, mul_div_cancel_right₀ _ h1]`. Rewrite using `[tendsto_zero_iff_meromorphicOrderAt_pos hmer]`. Assume the negation of the conclusion as `hord`.

Rewrite `hord` using `[not_lt]`. Establish `hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0` using `(meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by`. Rewrite using `[tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]`. Proceed by induction on `hk : meromorphicOrderAt h 0 with`.

Consider the case `top => simp`. Consider the case `coe k`. Rewrite `hord` using `[hk]`. Establish `hk0 : k ≤ 0` using `by exact_mod_cast hord`. Establish `: (0 : ℤ) ≤ -k` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `he : Tendsto eTwoPi imTop (𝓝[≠] 0)`. Use `(Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_` and prove the remaining obligations. Simplify using `[Function.Periodic.qParam, eTwoPi]`. Establish `hT : ∀ᶠ w in imTop, T < w.im` using `(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)`.

Use `not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL (fun w hw' => by simpa using (hw w hw').2.1) ?_` and prove the remaining obligations. Rewrite using `[← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]`. Establish `h1` using `hp.norm.mul (hc.comp he).norm`. Simplify using `only [norm_zero, zero_mul] at h1`. Use `h1.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [hT, he.eventually hne] with w hw' hw0`. Establish `h2` using `(hw w hw').2.2`. Establish `h3 : ‖h (eTwoPi w)‖ ≠ 0` using `norm_ne_zero_iff.mpr hw0`. Simplify using `only [Function.comp, Pi.inv_apply, norm_inv]`. Rewrite `h2` using `[Complex.norm_exp]`.

Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
