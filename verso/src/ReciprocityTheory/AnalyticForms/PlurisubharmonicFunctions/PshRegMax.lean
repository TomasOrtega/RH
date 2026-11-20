import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval

noncomputable section

section RegMaxDeriv
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- English proof (translation)
Conclude with `le_top` after adjusting the coercions.
-/
lemma succ_le_inf (m : ℕ) : (m : WithTop ℕ∞) + 1 ≤ ∞ := by exact_mod_cast le_top
/- English proof (translation)
Conclude with `succ_le_inf 1` after adjusting the coercions.
-/
lemma one_add_one_le_inf : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by exact_mod_cast succ_le_inf 1
/- English proof (translation)
Conclude with `le_top` after adjusting the coercions.
-/
lemma one_le_inf : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
/- English proof (translation)
Conclude with `succ_le_inf 1` after adjusting the coercions.
-/
lemma two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast succ_le_inf 1

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (regMax (ι` using `ι) η) t := (regMax_contDiff hη).differentiable (by simp) t`. Rewrite using `[← map_sum, Finset.univ_sum_single (fun _ : ι => (1 : ℝ))]`. Establish `hl : HasDerivAt (fun c : ℝ => t + c • (fun _ : ι => (1 : ℝ))) (fun _ => 1) 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const (fun _ : ι => (1 : ℝ))).const_add t`. Establish `h1` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)`.

Establish `h2 : HasDerivAt (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) 1 0`. Establish `e : (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) = fun c => regMax η t + c`. Use function extensionality and compare the values at `c`. Rewrite using `[← regMax_add_const]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `(hasDerivAt_id (0 : ℝ)).const_add _`. Conclude with `h1.unique h2`.
-/
lemma regMax_fderiv_sum [DecidableEq ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1 := by
  have hd : DifferentiableAt ℝ (regMax (ι := ι) η) t :=
    (regMax_contDiff hη).differentiable (by simp) t
  rw [← map_sum, Finset.univ_sum_single (fun _ : ι => (1 : ℝ))]
  have hl : HasDerivAt (fun c : ℝ => t + c • (fun _ : ι => (1 : ℝ))) (fun _ => 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fun _ : ι => (1 : ℝ))).const_add t
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) 1 0 := by
    have e : (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) = fun c => regMax η t + c := by
      funext c; rw [← regMax_add_const]; congr 1; funext j; simp
    rw [e]; exact (hasDerivAt_id (0 : ℝ)).const_add _
  exact h1.unique h2

/- English proof (translation)
Rewrite using `[regMax_one_eq_conv]`. Use function extensionality and compare the values at `x`. Simplify using `only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]`. Establish `hi : Integrable (fun s : ι → ℝ => kK s * tmax (x - s))` using `(integrable_mul_kK (g := fun s => tmax (x - s)) (continuous_tmax.comp (continuous_const.sub continuous_id))).congr (Eventually.of_forall fun s => mul_comm _ _)`. Rewrite using `[integral_sub hi (kK_integrable.mul_const c), integral_mul_const, kK_integral]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma regMax_one_eq_conv_sub (c : ℝ) :
    regMax (ι := ι) 1 = fun x => convolution kK (fun y => tmax y - c)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x + c := by
  rw [regMax_one_eq_conv]; funext x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]
  have hi : Integrable (fun s : ι → ℝ => kK s * tmax (x - s)) :=
    (integrable_mul_kK (g := fun s => tmax (x - s))
      (continuous_tmax.comp (continuous_const.sub continuous_id))).congr
      (Eventually.of_forall fun s => mul_comm _ _)
  rw [integral_sub hi (kK_integrable.mul_const c), integral_mul_const, kK_integral]; ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Conclude with `(kK_hasCompactSupport.hasFDerivAt_convolution_left _ (kK_contDiff.of_le (by simp)) hg.locallyIntegrable x).fderiv`.
-/
lemma fderiv_conv_eq {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    fderiv ℝ (convolution kK g (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (fderiv ℝ kK) g ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by
  funext x
  exact (kK_hasCompactSupport.hasFDerivAt_convolution_left _ (kK_contDiff.of_le (by simp))
    hg.locallyIntegrable x).fderiv

/- English proof (translation)
The claim follows from `(tsupport_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans (closure_minimal (fun h hh => mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hh)) isClosed_closedBall))`.
-/
lemma tsupport_fderiv2_kK :
    tsupport (fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))) ⊆ closedBall 0 (1 / 2) :=
  (tsupport_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans
    (closure_minimal (fun h hh => mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hh))
      isClosed_closedBall))

/- English proof (translation)
Establish `key : ‖x‖ * ‖y‖ ≤ ‖x‖ * (1 / 2)`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, norm_zero, zero_mul, zero_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hy hx) (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left key (norm_nonneg _)`.
-/
lemma norm_bilin_bound {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F)
    (hy : x ≠ 0 → ‖y‖ ≤ 1 / 2) : ‖L x y‖ ≤ ‖L‖ * ‖x‖ * (1 / 2) := by
  have key : ‖x‖ * ‖y‖ ≤ ‖x‖ * (1 / 2) := by
    by_cases hx : x = 0
    · rw [hx, norm_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hy hx) (norm_nonneg _)
  calc ‖L x y‖ ≤ ‖L‖ * ‖x‖ * ‖y‖ := L.le_opNorm₂ _ _
    _ ≤ ‖L‖ * ‖x‖ * (1 / 2) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left key (norm_nonneg _)

/- English proof (translation)
Establish `hs' : ‖s‖ ≤ 1 / 2` using `mem_closedBall_zero_iff.1 (tsupport_fderiv2_kK (subset_tsupport _ hs))`. Use `abs_tmax_sub_le (s₀ - s) s₀` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel_left, norm_neg]`. Rewrite using `[Real.norm_eq_abs]`. Conclude with `this.trans hs'`.
-/
lemma norm_coordMax_sub_le_half (s₀ s : ι → ℝ) (hs : fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ)) s ≠ 0) :
    ‖tmax (s₀ - s) - tmax s₀‖ ≤ 1 / 2 := by
  have hs' : ‖s‖ ≤ 1 / 2 :=
    mem_closedBall_zero_iff.1 (tsupport_fderiv2_kK (subset_tsupport _ hs))
  have := abs_tmax_sub_le (s₀ - s) s₀
  rw [sub_sub_cancel_left, norm_neg] at this
  rw [Real.norm_eq_abs]; exact this.trans hs'

/- English proof (translation)
Use `set L2 := ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (ι → ℝ)).precompL (ι → ℝ)`. Use `set F := fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))`. Establish `hFc : Continuous F` using `(kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf).continuous_fderiv (by simp)`. Establish `hFcs : HasCompactSupport F` using `(kK_hasCompactSupport.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)`. Use `⟨∫ s, ‖L2‖ * ‖F s‖ * (1 / 2), fun s₀ => ?_⟩` and prove the remaining obligations.

Use `set c := tmax s₀`. Use `set g₀ : (ι → ℝ) → ℝ := fun y => tmax y - c`. Establish `hg₀ : Continuous g₀` using `continuous_tmax.sub continuous_const`. Establish `e1 : fderiv ℝ (regMax (ι` using `ι) 1) = convolution (fderiv ℝ kK) g₀ ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by`. Rewrite using `[regMax_one_eq_conv_sub c]`.

Use function extensionality and compare the values at `x`. Rewrite using `[fderiv_add_const]`. Conclude with `congrFun (fderiv_conv_eq hg₀) x`. Establish `e2 : fderiv ℝ (fderiv ℝ (regMax (ι` using `ι) 1)) s₀ = convolution F g₀ L2 volume s₀ := by`. Rewrite using `[e1]`.

Conclude with `((kK_hasCompactSupport.fderiv (𝕜 := ℝ)).hasFDerivAt_convolution_left _ (kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf) hg₀.locallyIntegrable s₀).fderiv`. Rewrite using `[e2, convolution_def]`. Use `norm_integral_le_of_norm_le (((hFc.norm.integrable_of_hasCompactSupport hFcs.norm).const_mul _).mul_const _) (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Conclude with `norm_bilin_bound L2 (F s) (g₀ (s₀ - s)) (norm_coordMax_sub_le_half s₀ s)`.
-/
lemma regMax_one_fderiv2_bound : ∃ C : ℝ, ∀ s : ι → ℝ,
    ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) s‖ ≤ C := by
  set L2 := ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (ι → ℝ)).precompL (ι → ℝ)
  set F := fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))
  have hFc : Continuous F :=
    (kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf).continuous_fderiv (by simp)
  have hFcs : HasCompactSupport F := (kK_hasCompactSupport.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  refine ⟨∫ s, ‖L2‖ * ‖F s‖ * (1 / 2), fun s₀ => ?_⟩
  set c := tmax s₀
  set g₀ : (ι → ℝ) → ℝ := fun y => tmax y - c
  have hg₀ : Continuous g₀ := continuous_tmax.sub continuous_const
  have e1 : fderiv ℝ (regMax (ι := ι) 1) =
      convolution (fderiv ℝ kK) g₀ ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by
    rw [regMax_one_eq_conv_sub c]
    funext x; rw [fderiv_add_const]; exact congrFun (fderiv_conv_eq hg₀) x
  have e2 : fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) s₀ = convolution F g₀ L2 volume s₀ := by
    rw [e1]
    exact ((kK_hasCompactSupport.fderiv (𝕜 := ℝ)).hasFDerivAt_convolution_left _
      (kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf) hg₀.locallyIntegrable s₀).fderiv
  rw [e2, convolution_def]
  refine norm_integral_le_of_norm_le
    (((hFc.norm.integrable_of_hasCompactSupport hFcs.norm).const_mul _).mul_const _)
    (Eventually.of_forall fun s => ?_)
  exact norm_bilin_bound L2 (F s) (g₀ (s₀ - s)) (norm_coordMax_sub_le_half s₀ s)

/- English proof (translation)
Use `hg.hasFDerivAt.comp t ((hasFDerivAt_id t).const_smul c)` as an intermediate fact. Conclude with `this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)`.
-/
lemma hasFDerivAt_comp_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (ι → ℝ) → F} (c : ℝ) (t : ι → ℝ) (hg : DifferentiableAt ℝ g (c • t)) :
    HasFDerivAt (fun t => g (c • t)) (c • fderiv ℝ g (c • t)) t := by
  have := hg.hasFDerivAt.comp t ((hasFDerivAt_id t).const_smul c)
  exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Rewrite using `[regMax_eq_fun hη]`. Establish `hd : DifferentiableAt ℝ (regMax (ι` using `ι) 1) (η⁻¹ • t) := regMax_one_contDiff.differentiable (by simp) _`. Rewrite using `[((hasFDerivAt_comp_smul' η⁻¹ t hd).const_mul η).fderiv, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]`.
-/
lemma fderiv_regMax {η : ℝ} (hη : 0 < η) :
    fderiv ℝ (regMax (ι := ι) η) = fun t => fderiv ℝ (regMax (ι := ι) 1) (η⁻¹ • t) := by
  funext t
  rw [regMax_eq_fun hη]
  have hd : DifferentiableAt ℝ (regMax (ι := ι) 1) (η⁻¹ • t) :=
    regMax_one_contDiff.differentiable (by simp) _
  rw [((hasFDerivAt_comp_smul' η⁻¹ t hd).const_mul η).fderiv, smul_smul,
    mul_inv_cancel₀ hη.ne', one_smul]

/- English proof (translation)
Rewrite using `[fderiv_regMax hη]`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ (regMax (ι` using `ι) 1)) (η⁻¹ • t) := (regMax_one_contDiff.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero _`. Conclude with `(hasFDerivAt_comp_smul' η⁻¹ t hd).fderiv`.
-/
lemma fderiv2_regMax {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t =
      η⁻¹ • fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) := by
  rw [fderiv_regMax hη]
  have hd : DifferentiableAt ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) :=
    (regMax_one_contDiff.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero _
  exact (hasFDerivAt_comp_smul' η⁻¹ t hd).fderiv

/- English proof (translation)
The claim follows from `|fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t v w| ≤ C / η := by obtain ⟨C, hC⟩ := regMax_one_fderiv2_bound (ι := ι) refine ⟨C, fun η hη t v w hv hw => ?_⟩ rw [fderiv2_regMax hη, ← Real.norm_eq_abs] set A := fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) have hA : ‖A v w‖ ≤ C := …`.
-/
lemma regMax_fderiv2_bound : ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t v w : ι → ℝ), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
    |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t v w| ≤ C / η := by
  obtain ⟨C, hC⟩ := regMax_one_fderiv2_bound (ι := ι)
  refine ⟨C, fun η hη t v w hv hw => ?_⟩
  rw [fderiv2_regMax hη, ← Real.norm_eq_abs]
  set A := fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t)
  have hA : ‖A v w‖ ≤ C :=
    calc ‖A v w‖ ≤ ‖A‖ * ‖v‖ * ‖w‖ := A.le_opNorm₂ v w
      _ ≤ ‖A‖ * 1 * 1 := by gcongr
      _ ≤ C := by simpa using hC (η⁻¹ • t)
  rw [smul_apply, smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hA (inv_pos.2 hη).le

end RegMaxDeriv

/- English proof (translation)
Introduce `ι _ _ _`. Use `⟨fun η hη => ⟨regMax_contDiff hη, regMax_convex η, regMax_mono η, fun t => ⟨regMax_ge η t, regMax_le hη.le t⟩, fun t i hi => regMax_eq_of_dom hη.le t i hi, fun t j k s hkj htj hs => regMax_update hη.le t j k s hkj htj hs, fun t c => regMax_add_const η t c, fun t => regMax_fderiv_ …` and prove the remaining obligations. Take `⟨C, hC⟩` from `regMax_fderiv2_bound (ι := ι)`. Conclude with `⟨C, fun η hη t i j => hC η hη t _ _ (by simp [Pi.norm_single]) (by simp [Pi.norm_single])⟩`.
-/
theorem regMax_thm : RegMaxStatement := by
  intro ι _ _ _
  refine ⟨fun η hη => ⟨regMax_contDiff hη, regMax_convex η, regMax_mono η,
    fun t => ⟨regMax_ge η t, regMax_le hη.le t⟩,
    fun t i hi => regMax_eq_of_dom hη.le t i hi,
    fun t j k s hkj htj hs => regMax_update hη.le t j k s hkj htj hs,
    fun t c => regMax_add_const η t c,
    fun t => regMax_fderiv_sum hη t⟩, ?_⟩
  obtain ⟨C, hC⟩ := regMax_fderiv2_bound (ι := ι)
  exact ⟨C, fun η hη t i j => hC η hη t _ _ (by simp [Pi.norm_single]) (by simp [Pi.norm_single])⟩

section Psh
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_tmax (0 : ι → ℝ)`. Simplify using `using hi`.
-/
lemma tmax_zero : tmax (0 : ι → ℝ) = 0 := by
  obtain ⟨i, hi⟩ := exists_tmax (0 : ι → ℝ); simpa using hi

/- English proof (translation)
Establish `h1` using `regMax_ge η v`. Establish `h2` using `regMax_le hη v`. Establish `h3` using `abs_tmax_sub_le v 0`. Rewrite `h3` using `[tmax_zero, sub_zero, sub_zero]`. Apply the tactic sequence `rw [abs_le] at h3 ⊢; constructor <;> linarith`.
-/
lemma abs_regMax_le {η : ℝ} (hη : 0 ≤ η) (v : ι → ℝ) : |regMax η v| ≤ ‖v‖ + η / 2 := by
  have h1 := regMax_ge η v
  have h2 := regMax_le hη v
  have h3 := abs_tmax_sub_le v 0
  rw [tmax_zero, sub_zero, sub_zero] at h3
  rw [abs_le] at h3 ⊢; constructor <;> linarith

/- English proof (translation)
Introduce `z hz y hy`. Establish `he : 0 < (y - regMax η (fun j => u j z)) / 2` using `by linarith`. Establish `hev : ∀ᶠ x in 𝓝[U] z, ∀ j, u j x < u j z + (y - regMax η (fun j => u j z)) / 2` using `Filter.eventually_all.2 fun j => hu j z hz _ (by linarith)`. Use `filter_upwards [hev] with x hx`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma regMax_usc {X : Type*} [TopologicalSpace X] {U : Set X} (η : ℝ) {u : ι → X → ℝ}
    (hu : ∀ j, UpperSemicontinuousOn (u j) U) :
    UpperSemicontinuousOn (fun z => regMax η (fun j => u j z)) U := by
  intro z hz y hy
  have he : 0 < (y - regMax η (fun j => u j z)) / 2 := by linarith
  have hev : ∀ᶠ x in 𝓝[U] z, ∀ j, u j x < u j z + (y - regMax η (fun j => u j z)) / 2 :=
    Filter.eventually_all.2 fun j => hu j z hz _ (by linarith)
  filter_upwards [hev] with x hx
  calc regMax η (fun j => u j x)
      ≤ regMax η (fun j => u j z + (y - regMax η (fun j => u j z)) / 2) :=
        regMax_mono η fun j => (hx j).le
    _ = regMax η (fun j => u j z) + (y - regMax η (fun j => u j z)) / 2 := regMax_add_const η _ _
    _ < y := by linarith

/- English proof (translation)
Establish `hμ : volume (Ι (0:ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi)`. Rewrite using `[Set.uIoc_of_le (by positivity), Real.volume_Ioc, sub_zero]`. Establish `: IsFiniteMeasure (volume.restrict (Ι (0:ℝ) (2 * Real.pi)))` using `isFiniteMeasure_restrict.2 (by rw [hμ]; exact ENNReal.ofReal_ne_top)`. Establish `: NeZero (volume.restrict (Ι (0:ℝ) (2 * Real.pi)))` using `⟨fun h => by`. Use `Measure.restrict_eq_zero.1 h` as an intermediate fact.

Rewrite `this` using `[hμ, ENNReal.ofReal_eq_zero]`. Combine the linear relations using `[Real.pi_pos]⟩`. Establish `hg : Integrable (fun θ => f (circleMap c R θ)) (volume.restrict (Ι (0:ℝ) (2 * Real.pi)))` using `integrable_pi_iff.2 fun j => intervalIntegrable_iff.1 (hf j)`. Establish `hF : Continuous (regMax (ι` using `ι) η) := (regMax_contDiff hη).continuous`. Establish `hFg : Integrable (fun θ => regMax η (f (circleMap c R θ))) (volume.restrict (Ι (0:ℝ) (2 * Real.pi)))`.

Use `Integrable.mono' (hg.norm.add (integrable_const (η / 2))) (hF.comp_aestronglyMeasurable hg.aestronglyMeasurable) (Eventually.of_forall fun θ => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `abs_regMax_le hη.le _`. Establish `hci : CircleIntegrable f c R` using `intervalIntegrable_iff.2 hg`. Use `⟨intervalIntegrable_iff.2 hFg, ?_⟩` and prove the remaining obligations.

Establish `e : (fun j => Real.circleAverage (fun ζ => f ζ j) c R) = Real.circleAverage f c R`. Use function extensionality and compare the values at `j`. Conclude with `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).circleAverage_comp_comm hci`. Rewrite using `[e, Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]`. Conclude with `(regMax_convex η).map_average_le hF.continuousOn isClosed_univ (Eventually.of_forall fun _ => trivial) hg hFg`.
-/
lemma regMax_circle {η : ℝ} (hη : 0 < η) (f : ℂ → ι → ℝ) (c : ℂ) (R : ℝ)
    (hf : ∀ j, CircleIntegrable (fun ζ => f ζ j) c R) :
    CircleIntegrable (fun ζ => regMax η (f ζ)) c R ∧
      regMax η (fun j => Real.circleAverage (fun ζ => f ζ j) c R) ≤
        Real.circleAverage (fun ζ => regMax η (f ζ)) c R := by
  have hμ : volume (Ι (0:ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Set.uIoc_of_le (by positivity), Real.volume_Ioc, sub_zero]
  have : IsFiniteMeasure (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.2 (by rw [hμ]; exact ENNReal.ofReal_ne_top)
  have : NeZero (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) := ⟨fun h => by
    have := Measure.restrict_eq_zero.1 h
    rw [hμ, ENNReal.ofReal_eq_zero] at this; linarith [Real.pi_pos]⟩
  have hg : Integrable (fun θ => f (circleMap c R θ)) (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) :=
    integrable_pi_iff.2 fun j => intervalIntegrable_iff.1 (hf j)
  have hF : Continuous (regMax (ι := ι) η) := (regMax_contDiff hη).continuous
  have hFg : Integrable (fun θ => regMax η (f (circleMap c R θ)))
      (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) := by
    refine Integrable.mono' (hg.norm.add (integrable_const (η / 2)))
      (hF.comp_aestronglyMeasurable hg.aestronglyMeasurable) (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs]; exact abs_regMax_le hη.le _
  have hci : CircleIntegrable f c R := intervalIntegrable_iff.2 hg
  refine ⟨intervalIntegrable_iff.2 hFg, ?_⟩
  have e : (fun j => Real.circleAverage (fun ζ => f ζ j) c R) = Real.circleAverage f c R := by
    funext j
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).circleAverage_comp_comm hci
  rw [e, Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  exact (regMax_convex η).map_average_le hF.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => trivial) hg hFg

end Psh

section Levi
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Simplify using `using ((hasDerivAt_id s).smul_const w).const_add z`.
-/
lemma hasDerivAt_line (z w : E) (s : ℝ) : HasDerivAt (fun s : ℝ => z + s • w) w s := by
  simpa using ((hasDerivAt_id s).smul_const w).const_add z

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 2 φ z` using `hφ.contDiffAt (hU.mem_nhds hz)`. Establish `h2 : DifferentiableAt ℝ (fderiv ℝ φ) z` using `(h1.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero`. Establish `h3 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w)) (fderiv ℝ (fderiv ℝ φ) z w) 0` using `h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line z w 0) (by simp)`. Simplify using `using h3.clm_apply (hasDerivAt_const (0 : ℝ) w)`.
-/
lemma hasDerivAt_line_fderiv {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w) w) (fderiv ℝ (fderiv ℝ φ) z w w) 0 := by
  have h1 : ContDiffAt ℝ 2 φ z := hφ.contDiffAt (hU.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (h1.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w)) (fderiv ℝ (fderiv ℝ φ) z w) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line z w 0) (by simp)
  simpa using h3.clm_apply (hasDerivAt_const (0 : ℝ) w)

/- English proof (translation)
Establish `hc : Continuous (fun s : ℝ => z + s • w)` using `continuous_const.add (continuous_id.smul continuous_const)`. Establish `hev : ∀ᶠ s in 𝓝 (0 : ℝ), z + s • w ∈ U` using `hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hz)`. Use `filter_upwards [hev] with s hs`. Establish `hd : DifferentiableAt ℝ φ (z + s • w)` using `(hφ.differentiableOn two_ne_zero).differentiableAt (hU.mem_nhds hs)`. Conclude with `hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line z w s)`.
-/
lemma line_deriv_eventually {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => φ (z + s • w)) (fderiv ℝ φ (z + s • w) w) s := by
  have hc : Continuous (fun s : ℝ => z + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), z + s • w ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hz)
  filter_upwards [hev] with s hs
  have hd : DifferentiableAt ℝ φ (z + s • w) :=
    (hφ.differentiableOn two_ne_zero).differentiableAt (hU.mem_nhds hs)
  exact hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line z w s)

/- English proof (translation)
Establish `e : deriv (fun s : ℝ => φ (z + s • w)) =ᶠ[𝓝 0] fun s => fderiv ℝ φ (z + s • w) w` using `(line_deriv_eventually hU hφ hz w).mono fun s hs => hs.deriv`. Rewrite using `[e.deriv_eq, (hasDerivAt_line_fderiv hU hφ hz w).deriv]`.
-/
lemma fderiv2_eq_deriv2 {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    fderiv ℝ (fderiv ℝ φ) z w w = deriv (deriv (fun s : ℝ => φ (z + s • w))) 0 := by
  have e : deriv (fun s : ℝ => φ (z + s • w)) =ᶠ[𝓝 0] fun s => fderiv ℝ φ (z + s • w) w :=
    (line_deriv_eventually hU hφ hz w).mono fun s hs => hs.deriv
  rw [e.deriv_eq, (hasDerivAt_line_fderiv hU hφ hz w).deriv]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- English proof (translation)
Establish `hF : ContDiff ℝ ∞ (regMax (ι` using `ι) η) := regMax_contDiff hη`. Establish `hG : ContDiffOn ℝ 2 (fun x => regMax η (fun j => u j x)) U` using `(hF.of_le two_le_inf).comp_contDiffOn (contDiffOn_pi.2 hu)`. Rewrite using `[fderiv2_eq_deriv2 hU hG hz v]`. Establish `hγ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => fun j => u j (z + s • v)) (fun j => fderiv ℝ (u j) (z + s • v) v) s` using `by filter_upwards [Filter.eventually_all.2 fun j => line_deriv_eventually hU (hu j) hz v] with s hs`. Conclude with `hasDerivAt_pi.2 hs`.

Establish `e : deriv (fun s : ℝ => regMax η (fun j => u j (z + s • v))) =ᶠ[𝓝 0] fun s => fderiv ℝ (regMax (ι` using `ι) η) (fun j => u j (z + s • v)) (fun j => fderiv ℝ (u j) (z + s • v) v) := by filter_upwards [hγ] with s hs`. Conclude with `((hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s hs).deriv`. Rewrite using `[e.deriv_eq]`. Establish `hA : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι` using `ι) η) (fun j => u j (z + s • v))) (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)) 0 := by`. Establish `hγ0 : HasDerivAt (fun s : ℝ => fun j => u j (z + s • v)) (fun j => fderiv ℝ (u j) z v) 0`.

Use `hγ.self_of_nhds` as an intermediate fact. Simplify using `using this`. Conclude with `((hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero (fun j => u j z)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ0 (by simp)`. Establish `hB : HasDerivAt (fun s : ℝ => fun j => fderiv ℝ (u j) (z + s • v) v) (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) 0` using `hasDerivAt_pi.2 fun j => hasDerivAt_line_fderiv hU (hu j) hz v`. Simplify using `using (hA.clm_apply hB).deriv`.
-/
lemma regMax_comp_fderiv2 {η : ℝ} (hη : 0 < η) {U : Set E} (hU : IsOpen U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {z : E} (hz : z ∈ U) (v : E) :
    fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x))) z v v =
      fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)
          (fun j => fderiv ℝ (u j) z v) +
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) := by
  have hF : ContDiff ℝ ∞ (regMax (ι := ι) η) := regMax_contDiff hη
  have hG : ContDiffOn ℝ 2 (fun x => regMax η (fun j => u j x)) U :=
    (hF.of_le two_le_inf).comp_contDiffOn (contDiffOn_pi.2 hu)
  rw [fderiv2_eq_deriv2 hU hG hz v]
  have hγ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => fun j => u j (z + s • v))
      (fun j => fderiv ℝ (u j) (z + s • v) v) s := by
    filter_upwards [Filter.eventually_all.2 fun j => line_deriv_eventually hU (hu j) hz v]
      with s hs
    exact hasDerivAt_pi.2 hs
  have e : deriv (fun s : ℝ => regMax η (fun j => u j (z + s • v))) =ᶠ[𝓝 0]
      fun s => fderiv ℝ (regMax (ι := ι) η) (fun j => u j (z + s • v))
        (fun j => fderiv ℝ (u j) (z + s • v) v) := by
    filter_upwards [hγ] with s hs
    exact ((hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s hs).deriv
  rw [e.deriv_eq]
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι := ι) η) (fun j => u j (z + s • v)))
      (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)) 0 := by
    have hγ0 : HasDerivAt (fun s : ℝ => fun j => u j (z + s • v))
        (fun j => fderiv ℝ (u j) z v) 0 := by
      have := hγ.self_of_nhds; simpa using this
    exact ((hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero
      (fun j => u j z)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ0 (by simp)
  have hB : HasDerivAt (fun s : ℝ => fun j => fderiv ℝ (u j) (z + s • v) v)
      (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) 0 :=
    hasDerivAt_pi.2 fun j => hasDerivAt_line_fderiv hU (hu j) hz v
  simpa using (hA.clm_apply hB).deriv

/- English proof (translation)
Establish `h1` using `((regMax_contDiff hη).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p e 0) (by simp)`. Rewrite using `[← h1.deriv]`. Apply `Monotone.deriv_nonneg` to reduce the goal to its premises. Introduce `a b hab`. Apply `regMax_mono` to reduce the goal to its premises.

Introduce `j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Establish `: 0 ≤ e j` using `he j`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma regMax_fderiv_nonneg {η : ℝ} (hη : 0 < η) (p e : ι → ℝ) (he : 0 ≤ e) :
    0 ≤ fderiv ℝ (regMax (ι := ι) η) p e := by
  have h1 := ((regMax_contDiff hη).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line p e 0) (by simp)
  rw [← h1.deriv]
  apply Monotone.deriv_nonneg
  intro a b hab
  apply regMax_mono
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : 0 ≤ e j := he j
  nlinarith

/- English proof (translation)
Establish `hF` using `regMax_contDiff (ι := ι) hη`. Establish `hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => regMax η (p + s • a)) (fderiv ℝ (regMax (ι` using `ι) η) (p + s • a) a) s := fun s => (hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line p a s)`. Establish `hconv : ConvexOn ℝ Set.univ (fun s : ℝ => regMax η (p + s • a))`. Use `⟨convex_univ, fun x _ y _ c d hc hd hcd => ?_⟩` and prove the remaining obligations. Establish `e : p + (c • x + d • y) • a = c • (p + x • a) + d • (p + y • a)`.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-p j) * hcd`. Use `show regMax η (p + (c • x + d • y) • a) ≤ c • regMax η (p + x • a) + d • regMax η (p + y • a)`. Rewrite using `[e]`.

Conclude with `(regMax_convex η).2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd`. Establish `hmono : Monotone (deriv fun s : ℝ => regMax η (p + s • a))`. Use `hconv.monotoneOn_deriv (fun x _ => (hder x).differentiableAt)` as an intermediate fact. Conclude with `fun x y hxy => this (Set.mem_univ x) (Set.mem_univ y) hxy`. Establish `h0` using `hmono.deriv_nonneg (x := 0)`.

Establish `e2 : deriv (fun s : ℝ => regMax η (p + s • a)) = fun s => fderiv ℝ (regMax (ι` using `ι) η) (p + s • a) a := funext fun s => (hder s).deriv`. Rewrite `h0` using `[e2]`. Establish `h2 : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι` using `ι) η) (p + s • a) a) (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a) 0 := by`. Establish `hd` using `(hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero p`. Use `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p a 0) (by simp)` as an intermediate fact.

Simplify using `using this.clm_apply (hasDerivAt_const (0 : ℝ) a)`. Rewrite `h0` using `[h2.deriv]`. Then use the resulting hypothesis.
-/
lemma regMax_fderiv2_nonneg {η : ℝ} (hη : 0 < η) (p a : ι → ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a := by
  have hF := regMax_contDiff (ι := ι) hη
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => regMax η (p + s • a))
      (fderiv ℝ (regMax (ι := ι) η) (p + s • a) a) s := fun s =>
    (hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line p a s)
  have hconv : ConvexOn ℝ Set.univ (fun s : ℝ => regMax η (p + s • a)) := by
    refine ⟨convex_univ, fun x _ y _ c d hc hd hcd => ?_⟩
    have e : p + (c • x + d • y) • a = c • (p + x • a) + d • (p + y • a) := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-p j) * hcd
    show regMax η (p + (c • x + d • y) • a) ≤ c • regMax η (p + x • a) + d • regMax η (p + y • a)
    rw [e]
    exact (regMax_convex η).2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd
  have hmono : Monotone (deriv fun s : ℝ => regMax η (p + s • a)) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hder x).differentiableAt)
    exact fun x y hxy => this (Set.mem_univ x) (Set.mem_univ y) hxy
  have h0 := hmono.deriv_nonneg (x := 0)
  have e2 : deriv (fun s : ℝ => regMax η (p + s • a)) =
      fun s => fderiv ℝ (regMax (ι := ι) η) (p + s • a) a := funext fun s => (hder s).deriv
  rw [e2] at h0
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ (regMax (ι := ι) η) (p + s • a) a)
      (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a) 0 := by
    have hd := (hF.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero p
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line p a 0) (by simp)
    simpa using this.clm_apply (hasDerivAt_const (0 : ℝ) a)
  rwa [h2.deriv] at h0

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single c]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: (Pi.single j (c j) : ι → ℝ) = c j • (Pi.single j 1 : ι → ℝ)`. Apply the tactic sequence `funext k; by_cases h : k = j <;> simp [h]`.

Rewrite using `[this, map_smul, smul_eq_mul]`.
-/
lemma clm_apply_eq_sum [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (c : ι → ℝ) :
    L c = ∑ j, c j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (c j) : ι → ℝ) = c j • (Pi.single j 1 : ι → ℝ) := by
    funext k; by_cases h : k = j <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

end Levi

/- English proof (translation)
Introduce `D ι _ _ η U u hU hη hu`. Use `⟨regMax_usc η fun j => (hu j).1, fun z w hzw => ?_⟩` and prove the remaining obligations. Establish `h` using `fun j => (hu j).2 z w hzw`. Establish `hc` using `regMax_circle hη (fun ζ j => u j (z + ζ • w)) 0 1 fun j => (h j).1`. Conclude with `⟨hc.1, le_trans (regMax_mono η fun j => (h j).2) hc.2⟩`.
-/
theorem regMaxPsh_thm : RegMaxPshStatement := by
  intro D ι _ _ η U u hU hη hu
  refine ⟨regMax_usc η fun j => (hu j).1, fun z w hzw => ?_⟩
  have h := fun j => (hu j).2 z w hzw
  have hc := regMax_circle hη (fun ζ j => u j (z + ζ • w)) 0 1 fun j => (h j).1
  exact ⟨hc.1, le_trans (regMax_mono η fun j => (h j).2) hc.2⟩

/- English proof (translation)
Introduce `D ι _ _ η U u hU hη hu z hz w g hg`. Unfold `levi`. Rewrite using `[regMax_comp_fderiv2 hη hU hu hz w, regMax_comp_fderiv2 hη hU hu hz (Complex.I • w), clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z)), clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z))]`. Establish `q1` using `regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z w)`. Establish `q2` using `regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z (Complex.I • w))`.

Establish `hsum` using `regMax_fderiv_sum hη (fun j => u j z)`. Establish `h3 : 4 * g ≤ ∑ j, fderiv ℝ (fderiv ℝ (u j)) z w w * fderiv ℝ (regMax (ι` using `ι) η) (fun j => u j z) (Pi.single j 1) + ∑ j, fderiv ℝ (fderiv ℝ (u j)) z (Complex.I • w) (Complex.I • w) * fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) := by`. Establish `e4 : 4 * g = ∑ j, 4 * g * fderiv ℝ (regMax (ι` using `ι) η) (fun j => u j z) (Pi.single j 1) := by`. Rewrite using `[← Finset.mul_sum, hsum, mul_one]`. Rewrite using `[e4, ← Finset.sum_add_distrib]`.

Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `hj` using `hg j`. Unfold `levi at hj`. Apply the tactic sequence `have hn := regMax_fderiv_nonneg hη (fun j => u j z) (Pi.single j 1) (fun k => by rw [Pi.single_apply]; split_ifs <;> norm_num)`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem regMaxLevi_thm : RegMaxLeviStatement := by
  intro D ι _ _ η U u hU hη hu z hz w g hg
  classical
  unfold levi
  rw [regMax_comp_fderiv2 hη hU hu hz w, regMax_comp_fderiv2 hη hU hu hz (Complex.I • w),
    clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z)),
    clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z))]
  have q1 := regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z w)
  have q2 := regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z (Complex.I • w))
  have hsum := regMax_fderiv_sum hη (fun j => u j z)
  have h3 : 4 * g ≤ ∑ j, fderiv ℝ (fderiv ℝ (u j)) z w w *
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) +
      ∑ j, fderiv ℝ (fderiv ℝ (u j)) z (Complex.I • w) (Complex.I • w) *
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) := by
    have e4 : 4 * g = ∑ j, 4 * g * fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) := by
      rw [← Finset.mul_sum, hsum, mul_one]
    rw [e4, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := hg j
    unfold levi at hj
    have hn := regMax_fderiv_nonneg hη (fun j => u j z) (Pi.single j 1)
      (fun k => by rw [Pi.single_apply]; split_ifs <;> norm_num)
    nlinarith
  linarith

end

end ReciprocityTheory.AnForm.A
