import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Matrix Filter

noncomputable section

namespace ConeFsLog

variable {n : ℕ}

/- English proof (translation)
Establish `hA : IsUnit h.matᵀ.det` using `by rw [Matrix.det_transpose]; exact h.isUnit_det`. Rewrite using `[HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec, EuclideanSpace.norm_eq]`.
-/
theorem dualNorm_pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

/- English proof (translation)
Simplify using `only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem sum_mul_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by
  simp only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Simplify using `only [norm_mul]`. Conclude with `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`.
-/
theorem norm_sum_mul_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by
  rw [sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/- English proof (translation)
Rewrite using `[fsLog, dualNorm_pointOf]`.
-/
theorem fsLog_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by
  rw [fsLog, dualNorm_pointOf]

/- English proof (translation)
Rewrite using `[fsLog_pointOf]`. Break down `(div_nonneg (norm_nonneg _) (norm_nonneg y) : 0 ≤ ‖∑ j, u j * h.pointOf y j‖ / ‖y‖).eq_or_lt with hr | hr` into its components or cases. Rewrite using `[← hr, Real.log_zero]`. Conclude with `le_max_right _ _`. Use `(Real.log_le_log hr ?_).trans (le_max_left _ _)` and prove the remaining obligations.

Establish `hy : 0 < ‖y‖`. Break down `(norm_nonneg y).eq_or_lt with h0 | h0` into its components or cases. Simplify using `[← h0] at hr`. Conclude with `h0`. Conclude with `(div_le_iff₀ hy).mpr (norm_sum_mul_pointOf_le h u y)`.
-/
theorem fsLog_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) ≤ max (Real.log (h.norm u)) 0 := by
  rw [fsLog_pointOf]
  rcases (div_nonneg (norm_nonneg _) (norm_nonneg y) :
    0 ≤ ‖∑ j, u j * h.pointOf y j‖ / ‖y‖).eq_or_lt with hr | hr
  · rw [← hr, Real.log_zero]; exact le_max_right _ _
  · refine (Real.log_le_log hr ?_).trans (le_max_left _ _)
    have hy : 0 < ‖y‖ := by
      rcases (norm_nonneg y).eq_or_lt with h0 | h0
      · simp [← h0] at hr
      · exact h0
    exact (div_le_iff₀ hy).mpr (norm_sum_mul_pointOf_le h u y)

/- English proof (translation)
Rewrite `hy` using `[fsLog_pointOf]`. Break down `(norm_nonneg y).eq_or_lt with h0 | h0` into its components or cases. Use `norm_sum_mul_pointOf_le h u y` as an intermediate fact. Rewrite `this` using `[← h0, mul_zero]`. Rewrite using `[← h0, mul_zero]`.

Conclude with `this`. Break down `(norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha` into its components or cases. Rewrite using `[← ha]`. Check the signs of the components of the expression. Use `(Real.log_le_iff_le_exp (div_pos ha h0)).mp hy` as an intermediate fact.

Rewrite `this` using `[div_le_iff₀ h0]`. Then use the resulting hypothesis.
-/
theorem norm_le_of_fsLog_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by
  rw [fsLog_pointOf] at hy
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · have := norm_sum_mul_pointOf_le h u y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]; exact this
  rcases (norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha
  · rw [← ha]; positivity
  · have := (Real.log_le_iff_le_exp (div_pos ha h0)).mp hy
    rwa [div_le_iff₀ h0] at this

end ConeFsLog

open ConeFsLog in

/- English proof (translation)
Introduce `n e h W f u hW hf hu`. Establish `hS` using `hfin n e h W f hW hf`. Take `⟨C, α, hα, hC⟩` from `hslab n e h W f u hW hf hu`. Use `set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)`. Use `set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef`.

Use `set M := max (Real.log (h.norm u)) 0`. Establish `hFm : Measurable F`. Establish `: F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖)`. Use function extensionality and compare the values at `fun y => fsLog_pointOf h u y`. Rewrite using `[this]`.

Establish `hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y)`. Unfold `HermNorm.pointOf`. Use `fun_prop`. Use `Real.measurable_log.comp (Measurable.div ?_ measurable_norm)` and prove the remaining obligations. Conclude with `(continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable`.

Use `set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0`. Establish `hGm : Measurable G` using `hFm.neg.max measurable_const`. Establish `hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤`. Rewrite using `[lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _) hGm.aemeasurable]`. Establish `hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0)` using `(exp_neg_integrableOn_Ioi 0 hα).const_mul C`.

Use `lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply (measurableSet_le measurable_const hGm)]`. Use `(measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hyS⟩`.

Use `⟨hyS, norm_le_of_fsLog_le h u y ?_⟩` and prove the remaining obligations. Establish `: t ≤ -F y`. Break down `le_max_iff.mp (show t ≤ G y from hy) with h1 | h1` into its components or cases. Conclude with `h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Express the relevant statement in the definitionally equal form `F y ≤ -t`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Real.exp_mul]`. Put the polynomial expressions in normal form. Use `⟨hFm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Unfold `HasFiniteIntegral`. Establish `hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y)`. Introduce `y`. Rewrite using `[Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Establish `h1` using `fsLog_pointOf_le h u y`. Break down `le_or_gt 0 (F y) with h2 | h2` into its components or cases. Rewrite using `[abs_of_nonneg h2]`. Use `le_max_right (-F y) 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[abs_of_neg h2]`. Use `le_max_left (-F y) 0` as an intermediate fact. Use `le_max_right (Real.log (h.norm u)) 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `lt_of_le_of_lt (lintegral_mono hle) ?_` and prove the remaining obligations.

Rewrite using `[lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]`. Conclude with `ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩`.
-/
theorem ConeFsLogIntegrable.proof (hfin : ConeBallFinite.Statement)
    (hslab : ConeSlabBound.Statement) : ConeFsLogIntegrable.Statement := by
  intro n e h W f u hW hf hu
  have hS := hfin n e h W f hW hf
  obtain ⟨C, α, hα, hC⟩ := hslab n e h W f u hW hf hu
  set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef
  set M := max (Real.log (h.norm u)) 0
  have hFm : Measurable F := by
    have : F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) :=
      funext fun y => fsLog_pointOf h u y
    rw [this]
    have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
      unfold HermNorm.pointOf; fun_prop
    refine Real.measurable_log.comp (Measurable.div ?_ measurable_norm)
    exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0
  have hGm : Measurable G := hFm.neg.max measurable_const

  have hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro y ⟨hy, hyS⟩
      refine ⟨hyS, norm_le_of_fsLog_le h u y ?_⟩
      have : t ≤ -F y := by
        rcases le_max_iff.mp (show t ≤ G y from hy) with h1 | h1
        · exact h1
        · linarith
      change F y ≤ -t; linarith
    · rw [← Real.exp_mul]; ring_nf
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := fsLog_pointOf_le h u y
    rcases le_or_gt 0 (F y) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F y) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F y) 0; have := le_max_right (Real.log (h.norm u)) 0
      linarith
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩

end

end GroundTheory.Heights₂.Heights
