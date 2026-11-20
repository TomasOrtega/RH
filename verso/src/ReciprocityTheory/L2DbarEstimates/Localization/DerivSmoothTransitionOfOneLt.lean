import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Establish `h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ)` using `by filter_upwards [Iio_mem_nhds ht] with s hs`. Conclude with `Real.smoothTransition.zero_of_nonpos (le_of_lt hs)`. Rewrite using `[h.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) : deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [h.deriv_eq]
  simp

/- English proof (translation)
Establish `h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ)` using `by filter_upwards [Ioi_mem_nhds ht] with s hs`. Conclude with `Real.smoothTransition.one_of_one_le (le_of_lt hs)`. Rewrite using `[h.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) : deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  rw [h.deriv_eq]
  simp

/- English proof (translation)
Establish `hd : Continuous (deriv Real.smoothTransition)` using `(Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl`. Take `⟨C, hC⟩` from `(isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hd.continuousOn`. Use `⟨C, fun t => ?_⟩` and prove the remaining obligations. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)`. Break down `lt_or_ge t 0 with ht | ht` into its components or cases.

Rewrite using `[deriv_smoothTransition_of_neg ht]`. Simplify using `using hC0`. Break down `lt_or_ge 1 t with ht' | ht'` into its components or cases. Rewrite using `[deriv_smoothTransition_of_one_lt ht']`. Simplify using `using hC0`.

Simplify `hC t ⟨ht, ht'⟩` using `[Real.norm_eq_abs]`.
-/
theorem deriv_smoothTransition_bounded : ∃ C : ℝ, ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨C, fun t => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  rcases lt_or_ge t 0 with ht | ht
  · rw [deriv_smoothTransition_of_neg ht]; simpa using hC0
  rcases lt_or_ge 1 t with ht' | ht'
  · rw [deriv_smoothTransition_of_one_lt ht']; simpa using hC0
  · simpa [Real.norm_eq_abs] using hC t ⟨ht, ht'⟩

/- English proof (translation)
Unfold `SmoothR Smooth at *`. Introduce `c hc`. Establish `hG` using `he c hc`. Establish `hfd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target` using `hG.fderiv_of_isOpen c.open_target (by simp)`. Establish `hw : ∀ j, ContDiffOn ℝ ∞ (fun y => wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target`.

Introduce `j`. Unfold `wdb`. Conclude with `((hfd.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hfd.clm_apply contDiffOn_const))).div_const 2`. Establish `hsum : ContDiffOn ℝ ∞ (fun y => ∑ j ∈ Finset.univ, ‖wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y‖ ^ 2) c.target` using `ContDiffOn.sum fun j _ => (contDiff_norm_sq ℝ).comp_contDiffOn (hw j)`. Establish `hΦ` using `Complex.ofRealCLM.contDiff.comp_contDiffOn hsum`.

Use `hΦ.congr fun y hy => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Complex.ofRealCLM_apply]`. Use `congr 1`. Unfold `dbarSq`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 2`. Establish `hx : c.symm y ∈ c.source` using `c.map_target hy`. Establish `hzx : z (c.symm y) = y` using `by rw [hc hx]; exact c.right_inv hy`. Establish `hex : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ c.symm y ∈ e'.source` using `⟨c, hc, hx⟩`. Unfold `db`.

Rewrite using `[dif_pos hex]`. Take `⟨hc1, hc2⟩` from `Classical.choose_spec hex`. Use `set c' := Classical.choose hex`. Rewrite using `[hzx]`. Establish `hcx : c' (c.symm y) = y` using `by rw [← hc1 hc2]; exact hzx`.

Establish `hsym : c'.symm y = c.symm y`. Combine the equalities or inequalities in the displayed calculation. Establish `hyt : y ∈ c'.target` using `hcx ▸ c'.map_source hc2`. Establish `hloc : (fun x => (e x : ℂ)) ∘ c'.symm =ᶠ[𝓝 y] (fun x => (e x : ℂ)) ∘ c.symm`. Establish `h1 : ∀ᶠ w in 𝓝 y, w ∈ c'.target` using `c'.open_target.mem_nhds hyt`.

Establish `h2 : ∀ᶠ w in 𝓝 y, c'.symm w ∈ c.source` using `(c'.continuousAt_symm hyt).preimage_mem_nhds (c.open_source.mem_nhds (by rw [hsym]; exact hx))`. Use `filter_upwards [h1, h2] with w hw1 hw2`. Establish `hcw : c (c'.symm w) = w`. Rewrite using `[← hc hw2, hc1 (c'.map_target hw1), c'.right_inv hw1]`. Establish `hsw : c'.symm w = c.symm w`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Function.comp_apply, hsw]`. Unfold `wdb`. Rewrite using `[hloc.fderiv_eq]`.
-/
theorem smoothReal_dbar_sq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : M → ℝ) (he : SmoothR n z e) : SmoothR n z (dbarSq n z (fun y => (e y : ℂ))) := by
  unfold SmoothR Smooth at *
  intro c hc
  have hG := he c hc
  have hfd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target :=
    hG.fderiv_of_isOpen c.open_target (by simp)
  have hw : ∀ j, ContDiffOn ℝ ∞ (fun y => wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target := by
    intro j
    unfold wdb
    exact ((hfd.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hfd.clm_apply contDiffOn_const))).div_const 2
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ j ∈ Finset.univ, ‖wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y‖ ^ 2) c.target :=
    ContDiffOn.sum fun j _ => (contDiff_norm_sq ℝ).comp_contDiffOn (hw j)
  have hΦ := Complex.ofRealCLM.contDiff.comp_contDiffOn hsum
  refine hΦ.congr fun y hy => ?_
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  congr 1
  unfold dbarSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  have hx : c.symm y ∈ c.source := c.map_target hy
  have hzx : z (c.symm y) = y := by rw [hc hx]; exact c.right_inv hy
  have hex : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ c.symm y ∈ e'.source :=
    ⟨c, hc, hx⟩
  unfold db
  rw [dif_pos hex]
  obtain ⟨hc1, hc2⟩ := Classical.choose_spec hex
  set c' := Classical.choose hex
  rw [hzx]
  have hcx : c' (c.symm y) = y := by rw [← hc1 hc2]; exact hzx
  have hsym : c'.symm y = c.symm y := by
    calc c'.symm y = c'.symm (c' (c.symm y)) := by rw [hcx]
      _ = c.symm y := c'.left_inv hc2
  have hyt : y ∈ c'.target := hcx ▸ c'.map_source hc2
  have hloc : (fun x => (e x : ℂ)) ∘ c'.symm =ᶠ[𝓝 y] (fun x => (e x : ℂ)) ∘ c.symm := by
    have h1 : ∀ᶠ w in 𝓝 y, w ∈ c'.target := c'.open_target.mem_nhds hyt
    have h2 : ∀ᶠ w in 𝓝 y, c'.symm w ∈ c.source :=
      (c'.continuousAt_symm hyt).preimage_mem_nhds (c.open_source.mem_nhds (by rw [hsym]; exact hx))
    filter_upwards [h1, h2] with w hw1 hw2
    have hcw : c (c'.symm w) = w := by
      rw [← hc hw2, hc1 (c'.map_target hw1), c'.right_inv hw1]
    have hsw : c'.symm w = c.symm w := by
      calc c'.symm w = c.symm (c (c'.symm w)) := (c.left_inv hw2).symm
        _ = c.symm w := by rw [hcw]
    simp only [Function.comp_apply, hsw]
  unfold wdb
  rw [hloc.fderiv_eq]

/- English proof (translation)
Unfold `dbarSq`. Conclude with `Finset.sum_nonneg fun j _ => by positivity`.
-/
theorem dbar_sq_nonneg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (u : M → ℂ) (x : M) : 0 ≤ dbarSq n z u x := by
  unfold dbarSq
  exact Finset.sum_nonneg fun j _ => by positivity

/- English proof (translation)
Unfold `dbarSq`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `db`. Use `split_ifs with h`.

Take `⟨hc1, hc2⟩` from `Classical.choose_spec h set c := Classical.choose h`. Establish `hy : z x ∈ c.target` using `by rw [hc1 hc2]; exact c.map_source hc2`. Establish `hE : DifferentiableAt ℝ ((fun y => (e y : ℂ)) ∘ c.symm) (z x)` using `((he c hc1).differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hy)`. Take `⟨r, hr⟩ : ∃ r : V n → ℝ, r = fun y => (((fun y => (e y : ℂ)) ∘ c.symm) y).re` from `⟨_, rfl⟩`. Establish `hR : DifferentiableAt ℝ r (z x)`.

Rewrite using `[hr]`. Conclude with `Complex.reCLM.differentiableAt.comp _ hE`. Establish `hK : (fun y => ((k (e y) : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ (k ∘ r)`. Use function extensionality and compare the values at `y`. Simplify using `[hr]`.

Establish `hG : (fun y => ((e y : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ r`. Use function extensionality and compare the values at `y`. Simplify using `[hr]`. Establish `hrx : r (z x) = e x` using `by simp [hr, hc1 hc2, c.left_inv hc2]`. Establish `hk' : HasDerivAt k (deriv k (e x)) (r (z x))`.

Rewrite using `[hrx]`. Conclude with `((hk.differentiable (by simp)) (e x)).hasDerivAt`. Establish `hd1` using `Complex.ofRealCLM.hasFDerivAt.comp (z x) (hk'.comp_hasFDerivAt (z x) hR.hasFDerivAt)`. Establish `hd2` using `Complex.ofRealCLM.hasFDerivAt.comp (z x) hR.hasFDerivAt`. Rewrite using `[hK, hG]`.

Unfold `wdb`. Rewrite using `[hd1.fderiv, hd2.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply]`. Rewrite using `[show ∀ a b c' : ℝ, (((a * b : ℝ) : ℂ) + Complex.I * ((a * c' : ℝ) : ℂ)) / 2 = (a : ℂ) * (((b : ℂ) + Complex.I * (c' : ℂ)) / 2) from fun a b c' => by push_cast; ring]`. Rewrite using `[norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`.

Simplify using the standard rewrite rules.
-/
theorem dbar_sq_comp_eq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (e : M → ℝ) (he : SmoothR n z e) (x : M) :
    dbarSq n z (fun y => (k (e y) : ℂ)) x = deriv k (e x) ^ 2 * dbarSq n z (fun y => (e y : ℂ)) x := by
  unfold dbarSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold db
  split_ifs with h
  · obtain ⟨hc1, hc2⟩ := Classical.choose_spec h
    set c := Classical.choose h
    have hy : z x ∈ c.target := by rw [hc1 hc2]; exact c.map_source hc2
    have hE : DifferentiableAt ℝ ((fun y => (e y : ℂ)) ∘ c.symm) (z x) :=
      ((he c hc1).differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hy)
    obtain ⟨r, hr⟩ : ∃ r : V n → ℝ, r = fun y => (((fun y => (e y : ℂ)) ∘ c.symm) y).re :=
      ⟨_, rfl⟩
    have hR : DifferentiableAt ℝ r (z x) := by
      rw [hr]; exact Complex.reCLM.differentiableAt.comp _ hE
    have hK : (fun y => ((k (e y) : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ (k ∘ r) := by
      funext y; simp [hr]
    have hG : (fun y => ((e y : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ r := by
      funext y; simp [hr]
    have hrx : r (z x) = e x := by simp [hr, hc1 hc2, c.left_inv hc2]
    have hk' : HasDerivAt k (deriv k (e x)) (r (z x)) := by
      rw [hrx]
      exact ((hk.differentiable (by simp)) (e x)).hasDerivAt
    have hd1 := Complex.ofRealCLM.hasFDerivAt.comp (z x) (hk'.comp_hasFDerivAt (z x) hR.hasFDerivAt)
    have hd2 := Complex.ofRealCLM.hasFDerivAt.comp (z x) hR.hasFDerivAt
    rw [hK, hG]
    unfold wdb
    rw [hd1.fderiv, hd2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofRealCLM_apply]
    rw [show ∀ a b c' : ℝ, (((a * b : ℝ) : ℂ) + Complex.I * ((a * c' : ℝ) : ℂ)) / 2 =
        (a : ℂ) * (((b : ℂ) + Complex.I * (c' : ℂ)) / 2) from fun a b c' => by push_cast; ring]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨c, hx, hzc⟩` from `hz x`. Establish `hc : IsChart n z c` using `fun y _ => by rw [hzc]`. Establish `hg` using `(he c hc).continuousOn`.

Establish `h1 : ContinuousAt (((fun y => (e y : ℂ)) ∘ c.symm) ∘ c) x` using `(hg.continuousAt (c.open_target.mem_nhds (c.map_source hx))).comp (c.continuousAt hx)`. Establish `h2 : ((fun y => (e y : ℂ)) ∘ c.symm) ∘ c =ᶠ[𝓝 x] fun y => (e y : ℂ)` using `by filter_upwards [c.open_source.mem_nhds hx] with y hy`. Simplify using `[c.left_inv hy]`. Establish `h3` using `Complex.continuous_re.continuousAt.comp (h1.congr h2)`. Simplify `h3` using `[Function.comp_def]`.
-/
theorem continuous_of_smoothReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (e : M → ℝ) (he : SmoothR n z e) : Continuous e := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨c, hx, hzc⟩ := hz x
  have hc : IsChart n z c := fun y _ => by rw [hzc]
  have hg := (he c hc).continuousOn
  have h1 : ContinuousAt (((fun y => (e y : ℂ)) ∘ c.symm) ∘ c) x :=
    (hg.continuousAt (c.open_target.mem_nhds (c.map_source hx))).comp (c.continuousAt hx)
  have h2 : ((fun y => (e y : ℂ)) ∘ c.symm) ∘ c =ᶠ[𝓝 x] fun y => (e y : ℂ) := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    simp [c.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3

/- English proof (translation)
Introduce `z hz e a he hcomp`. Establish `hec : Continuous e` using `continuous_of_smoothReal n z hz e he`. Take `⟨C, hC⟩` from `deriv_smoothTransition_bounded`. Use `set D := dbarSq n z (fun y => (e y : ℂ)) with hD`. Establish `hDs : SmoothR n z D` using `smoothReal_dbar_sq n z e he`.

Establish `hk0 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - a - 2))` using `Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)`. Use `⟨fun x => Real.smoothTransition (e x - a - 2) * (C ^ 2 * D x), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `SmoothR.mul n z _ _ (SmoothR.comp n z _ hk0 e he) (SmoothR.mul n z _ _ ?_ hDs) show Smooth n z (fun _ => ((C ^ 2 : ℝ) : ℂ))` and prove the remaining obligations. Conclude with `Smooth.const n z _`. Introduce `x hx`.

Establish `h0 : ∀ y, e y < a + 2 → Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) = 0`. Introduce `y hy`. Rewrite using `[Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]`. Use `⟨h0 x (by linarith), ?_⟩` and prove the remaining obligations. Unfold `dSqR`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hnot : x ∉ tsupport (fun y => ((Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) : ℝ) : ℂ))`. Rewrite using `[notMem_tsupport_iff_eventuallyEq]`. Use `filter_upwards [(isOpen_lt hec continuous_const).mem_nhds (show e x < a + 2 by linarith)] with y hy`. Simplify using `[h0 y hy]`.

Establish `hnot2` using `fun h => hnot (tsupport_d_subset n z j _ h)`. Rewrite using `[image_eq_zero_of_notMem_tsupport hnot2]`. Simplify using the standard rewrite rules. Introduce `ν set N : ℝ := max (ν : ℝ) (a + 3) with hN`. Establish `hk : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition (t - N))` using `contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))`.

Use `⟨fun x => 1 - Real.smoothTransition (e x - N), ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `SmoothR.comp n z _ hk e he`. Use `HasCompactSupport.intro (hcomp (N + 1)) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, not_le] at hx`. Use `beta_reduce`.

Rewrite using `[Real.smoothTransition.one_of_one_le (show 1 ≤ e x - N by linarith)]`. Simplify using the standard rewrite rules. Introduce `x`. Conclude with `⟨by linarith [Real.smoothTransition.le_one (e x - N)], by linarith [Real.smoothTransition.nonneg (e x - N)]⟩`. Introduce `x hx beta_reduce`.

Rewrite using `[Real.smoothTransition.zero_of_nonpos (show e x - N ≤ 0 by linarith [le_max_left (ν : ℝ) (a + 3)])]`. Simplify using the standard rewrite rules. Introduce `x`. Establish `hcomp' : dbarSq n z (fun y => ((1 - Real.smoothTransition (e y - N) : ℝ) : ℂ)) x = deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) ^ 2 * D x` using `dbar_sq_comp_eq n z _ hk e he x`. Establish `hder : deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) = -deriv Real.smoothTransition (e x - N)`.

Rewrite using `[deriv_const_sub, deriv_comp_sub_const]`. Rewrite using `[hcomp', hder, neg_sq]`. Establish `hD0 : 0 ≤ D x` using `dbar_sq_nonneg n z _ x`. Distinguish the cases in `hlt : e x < N`. Rewrite using `[deriv_smoothTransition_of_neg (by linarith)]`.

Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]`. Conclude with `(Real.exp_pos _).le`. Establish `hge : a + 3 ≤ e x` using `le_trans (le_max_right _ _) (not_lt.1 hlt) beta_reduce`. Rewrite using `[Real.smoothTransition.one_of_one_le (show 1 ≤ e x - a - 2 by linarith), one_mul]`. Establish `h1 : deriv Real.smoothTransition (e x - N) ^ 2 ≤ C ^ 2`.

Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hC _) 2`. Establish `h2` using `Real.add_one_le_exp (C ^ 2 * D x)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psi (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : PsiStatement n M := by
  intro z hz e a he hcomp
  have hec : Continuous e := continuous_of_smoothReal n z hz e he
  obtain ⟨C, hC⟩ := deriv_smoothTransition_bounded
  set D := dbarSq n z (fun y => (e y : ℂ)) with hD
  have hDs : SmoothR n z D := smoothReal_dbar_sq n z e he
  have hk0 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - a - 2)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)
  refine ⟨fun x => Real.smoothTransition (e x - a - 2) * (C ^ 2 * D x), ?_, ?_, ?_⟩
  · refine SmoothR.mul n z _ _ (SmoothR.comp n z _ hk0 e he) (SmoothR.mul n z _ _ ?_ hDs)
    show Smooth n z (fun _ => ((C ^ 2 : ℝ) : ℂ))
    exact Smooth.const n z _
  · intro x hx
    have h0 : ∀ y, e y < a + 2 →
        Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) = 0 := by
      intro y hy
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    refine ⟨h0 x (by linarith), ?_⟩
    unfold dSqR
    refine Finset.sum_eq_zero fun j _ => ?_
    have hnot : x ∉ tsupport (fun y =>
        ((Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) : ℝ) : ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [(isOpen_lt hec continuous_const).mem_nhds
        (show e x < a + 2 by linarith)] with y hy
      simp [h0 y hy]
    have hnot2 := fun h => hnot (tsupport_d_subset n z j _ h)
    rw [image_eq_zero_of_notMem_tsupport hnot2]
    simp
  · intro ν
    set N : ℝ := max (ν : ℝ) (a + 3) with hN
    have hk : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition (t - N)) :=
      contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
    refine ⟨fun x => 1 - Real.smoothTransition (e x - N), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact SmoothR.comp n z _ hk e he
    · refine HasCompactSupport.intro (hcomp (N + 1)) fun x hx => ?_
      simp only [Set.mem_ofPred_eq, not_le] at hx
      beta_reduce
      rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - N by linarith)]
      simp
    · intro x
      exact ⟨by linarith [Real.smoothTransition.le_one (e x - N)],
        by linarith [Real.smoothTransition.nonneg (e x - N)]⟩
    · intro x hx
      beta_reduce
      rw [Real.smoothTransition.zero_of_nonpos (show e x - N ≤ 0 by linarith [le_max_left (ν : ℝ) (a + 3)])]
      simp
    · intro x
      have hcomp' : dbarSq n z (fun y => ((1 - Real.smoothTransition (e y - N) : ℝ) : ℂ)) x =
          deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) ^ 2 * D x :=
        dbar_sq_comp_eq n z _ hk e he x
      have hder : deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) =
          -deriv Real.smoothTransition (e x - N) := by
        rw [deriv_const_sub, deriv_comp_sub_const]
      rw [hcomp', hder, neg_sq]
      have hD0 : 0 ≤ D x := dbar_sq_nonneg n z _ x
      by_cases hlt : e x < N
      · rw [deriv_smoothTransition_of_neg (by linarith)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact (Real.exp_pos _).le
      · have hge : a + 3 ≤ e x := le_trans (le_max_right _ _) (not_lt.1 hlt)
        beta_reduce
        rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - a - 2 by linarith), one_mul]
        have h1 : deriv Real.smoothTransition (e x - N) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
        have h2 := Real.add_one_le_exp (C ^ 2 * D x)
        nlinarith

end

end ReciprocityTheory.L2DbarEstimates.F
