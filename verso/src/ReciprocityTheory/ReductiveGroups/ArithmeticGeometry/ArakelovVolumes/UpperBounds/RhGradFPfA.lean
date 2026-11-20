import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff

noncomputable section

/- English proof (translation)
Establish `hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ)` using `(hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv`. Rewrite using `[wdb, hd]`. Simplify using `only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]`. Use `set D := fderiv ℝ g (F v)`. Use `set c := J (bas n j)`.

Rewrite using `[fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]`. Take the linear combination `((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 - (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) * Complex.I_sq`.
-/
theorem gc_wdb_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wdb n j (g ∘ F) v = ∑ a, wdb d a g (F v) * (starRingEnd ℂ) (J (bas n j) a) := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wdb, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination ((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 -
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

/- English proof (translation)
Establish `hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ)` using `(hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv`. Rewrite using `[wd, hd]`. Simplify using `only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]`. Use `set D := fderiv ℝ g (F v)`. Use `set c := J (bas n j)`.

Rewrite using `[fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]`. Take the linear combination `(-(D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 + (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) * Complex.I_sq`.
-/
theorem gc_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wd n j (g ∘ F) v = ∑ a, wd d a g (F v) * J (bas n j) a := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wd, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination (-(D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 +
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

/- English proof (translation)
Establish `h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j`. Use extensionality with `k`. Simplify using `[bas, Pi.single_apply]`. Rewrite using `[h, map_sum]`. Simplify using `[map_smul]`.
-/
theorem gc_toLp_apply (n d : ℕ) (J : V n →L[ℂ] V d) (ξ : Fin n → ℂ) (b : Fin d) :
    J (WithLp.toLp 2 ξ) b = ∑ j, ξ j * J (bas n j) b := by
  have h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j := by
    ext k
    simp [bas, Pi.single_apply]
  rw [h, map_sum]
  simp [map_smul]

/- English proof (translation)
Simplify using `only [gc_wd_comp n d g F J v hg hF, gc_toLp_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem gc_sum_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (ξ : Fin n → ℂ) :
    ∑ j, wd n j (g ∘ F) v * ξ j = ∑ a, wd d a g (F v) * J (WithLp.toLp 2 ξ) a := by
  simp only [gc_wd_comp n d g F J v hg hF, gc_toLp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_four_indices_comm (n d : ℕ) (f : Fin n → Fin n → Fin d → Fin d → ℂ) :
    ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := by
  calc ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ j, ∑ k, ∑ b, ∑ a, f j k a b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ k, ∑ a, f j k a b := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ a, f j k a b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ a, ∑ k, f j k a b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

/- English proof (translation)
Establish `hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y` using `fun y hy => (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt`. Establish `hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y)` using `(hFd v hv).continuousAt.eventually (hg.eventually (by simp))`. Establish `hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v] fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)`. Introduce `k`. Use `filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU`.

Conclude with `gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k`. Establish `hD : DifferentiableAt ℝ (fderiv ℝ g) (F v)` using `(hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v)`. Introduce `a`. Use `show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) + Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)`.

Establish `h1` using `hD.clm_apply (differentiableAt_const (bas d a))`. Establish `h2` using `hD.clm_apply (differentiableAt_const (Complex.I • bas d a))`. Establish `h3` using `(h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[div_eq_mul_inv]`.

Establish `hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v` using `fun a => (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt`. Establish `hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v` using `((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt (by norm_num)`. Establish `hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v` using `fun k a => (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a`. Establish `hCa : ∀ k a, DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v`. Introduce `k a`.

Use `Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `step : ∀ j k, wd n j (wdb n k (g ∘ F)) v = ∑ a, ∑ b, wd d b (wdb d a g) (F v) * fderiv ℂ F v (bas n j) b * (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a)`. Introduce `j k`. Rewrite using `[wd_congr n j _ _ v (hwdb k), fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero, mul_zero, add_zero]`. Use `gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j` as an intermediate fact. Rewrite using `[show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]`. Unfold `leviV`.

Simplify using `only [step, gc_toLp_apply, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[sum_four_indices_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem gc_leviV_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v))
    (ξ : Fin n → ℂ) :
    leviV n (g ∘ F) v ξ = leviV d g (F v) (fun b => fderiv ℂ F v (WithLp.toLp 2 ξ) b) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  have step : ∀ j k, wd n j (wdb n k (g ∘ F)) v = ∑ a, ∑ b,
      wd d b (wdb d a g) (F v) * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
    intro j k
    rw [wd_congr n j _ _ v (hwdb k),
      fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
        (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
      mul_zero, add_zero]
    have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
    rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  unfold leviV
  simp only [step, gc_toLp_apply, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]
  rw [sum_four_indices_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
