import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Filter Topology ArithmeticFunction MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.P.PsiZeroIntegral

private def dom (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)

/- English proof (translation)
Use `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(Real.log t)⁻¹) (l := 0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(((Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos ha).ne').neg).continuousWithinAt`. Introduce `x hx`. Establish `hx1 : (1 : ℝ) < x` using `lt_trans ha hx`. Establish `hx0 : x ≠ 0` using `(by linarith : (0 : ℝ) < x).ne'`.

Establish `hl : Real.log x ≠ 0` using `(Real.log_pos hx1).ne'`. Establish `h` using `((Real.hasDerivAt_log hx0).inv hl).neg`. Use `h.congr_deriv ?_` and prove the remaining obligations. Unfold `dom`. Use `first`.

Consider the case `(rw [neg_div, neg_neg, one_div, mul_inv, div_eq_mul_inv])`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Introduce `x hx`. Establish `hx1 : (1 : ℝ) < x` using `lt_trans ha hx`.

Unfold `dom`. Establish `hpos : 0 < x * Real.log x ^ 2` using `mul_pos (by linarith) (pow_pos (Real.log_pos hx1) 2)`. Conclude with `(one_div_pos.2 hpos).le`. Establish `h` using `(Real.tendsto_log_atTop.inv_tendsto_atTop).neg`. Simplify using `using h`.
-/
private lemma dom_integrableOn {a : ℝ} (ha : 1 < a) : IntegrableOn dom (Set.Ioi a) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(Real.log t)⁻¹) (l := 0) ?_ ?_ ?_ ?_
  · exact (((Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos ha).ne').neg).continuousWithinAt
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_trans ha hx
    have hx0 : x ≠ 0 := (by linarith : (0 : ℝ) < x).ne'
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have h := ((Real.hasDerivAt_log hx0).inv hl).neg
    refine h.congr_deriv ?_
    unfold dom
    first
      | (rw [neg_div, neg_neg, one_div, mul_inv, div_eq_mul_inv])
      | (field_simp; done)
      | (field_simp; ring)
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_trans ha hx
    unfold dom
    have hpos : 0 < x * Real.log x ^ 2 := mul_pos (by linarith) (pow_pos (Real.log_pos hx1) 2)
    exact (one_div_pos.2 hpos).le
  · have h := (Real.tendsto_log_atTop.inv_tendsto_atTop).neg
    simpa using h

/- English proof (translation)
Establish `hL : 0 < Real.log x` using `Real.log_pos hx`. Establish `hy0 : 0 < c * Real.sqrt (Real.log x)` using `mul_pos hc (Real.sqrt_pos.2 hL)`. Establish `h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2`. Rewrite using `[mul_pow, show Real.sqrt (Real.log x) ^ 4 = (Real.sqrt (Real.log x) ^ 2) ^ 2 by ring, Real.sq_sqrt hL.le]`. Establish `hexp : (c * Real.sqrt (Real.log x)) ^ 4 / 24 ≤ Real.exp (c * Real.sqrt (Real.log x))`.

Establish `h` using `Real.pow_div_factorial_le_exp _ hy0.le 4`. Evaluate the numerical expressions using `[Nat.factorial] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[show -c * Real.sqrt (Real.log x) = -(c * Real.sqrt (Real.log x)) by ring, Real.exp_neg, div_div, ← h4]`. Establish `hq : 0 < (c * Real.sqrt (Real.log x)) ^ 4 / 24` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma exp_sqrt_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hy0 : 0 < c * Real.sqrt (Real.log x) := mul_pos hc (Real.sqrt_pos.2 hL)
  have h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [mul_pow, show Real.sqrt (Real.log x) ^ 4 = (Real.sqrt (Real.log x) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hL.le]
  have hexp : (c * Real.sqrt (Real.log x)) ^ 4 / 24 ≤ Real.exp (c * Real.sqrt (Real.log x)) := by
    have h := Real.pow_div_factorial_le_exp _ hy0.le 4
    norm_num [Nat.factorial] at h
    linarith
  rw [show -c * Real.sqrt (Real.log x) = -(c * Real.sqrt (Real.log x)) by ring, Real.exp_neg,
    div_div, ← h4]
  have hq : 0 < (c * Real.sqrt (Real.log x)) ^ 4 / 24 := by positivity
  calc (Real.exp (c * Real.sqrt (Real.log x)))⁻¹
      = 1 / Real.exp (c * Real.sqrt (Real.log x)) := inv_eq_one_div _
    _ ≤ 1 / ((c * Real.sqrt (Real.log x)) ^ 4 / 24) := one_div_le_one_div_of_le hq hexp
    _ = 24 / (c * Real.sqrt (Real.log x)) ^ 4 := by field_simp

private def rem (a : ℕ → ℂ) (m : ℂ) (t : ℝ) : ℂ := (∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t

private def RemBound (a : ℕ → ℂ) (m : ℂ) : Prop :=
  ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖rem a m t‖ ≤ K * t / Real.log t ^ 2

/- English proof (translation)
Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos ht]`. Use `congr 1`.
-/
private lemma norm_cpow_neg_add_one {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    ‖(t : ℂ) ^ (-((σ : ℂ) + 1))‖ = t ^ (-(σ + 1)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  congr 1

/- English proof (translation)
Unfold `rem`. Conclude with `((measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, a k)).comp Nat.measurable_floor).sub (measurable_const.mul Complex.measurable_ofReal)`.
-/
private lemma rem_measurable (a : ℕ → ℂ) (m : ℂ) : Measurable (rem a m) := by
  unfold rem
  exact ((measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, a k)).comp Nat.measurable_floor).sub
    (measurable_const.mul Complex.measurable_ofReal)

/- English proof (translation)
Conclude with `(rem_measurable a m).mul (Complex.measurable_ofReal.pow_const s)`.
-/
private lemma F_measurable (a : ℕ → ℂ) (m : ℂ) (s : ℂ) :
    Measurable (fun t : ℝ => rem a m t * (t : ℂ) ^ s) := by
  exact (rem_measurable a m).mul (Complex.measurable_ofReal.pow_const s)

/- English proof (translation)
Introduce `t ht`. Establish `ht' : (0 : ℝ) < t` using `lt_of_lt_of_le one_pos ht`. Conclude with `(Complex.continuous_ofReal.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.2 ht')).continuousWithinAt`.
-/
private lemma cpow_contOn (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Set.Ici 1) := by
  intro t ht
  have ht' : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 ht')).continuousWithinAt

/- English proof (translation)
Take `⟨K, x₁, hx₁, hK⟩` from `h`. Use `Asymptotics.IsBigO.of_bound K ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop x₁] with t ht`. Establish `ht0 : 0 < t` using `by linarith`. Establish `hl : Real.log t ≠ 0` using `(Real.log_pos (by linarith)).ne'`.

Rewrite using `[norm_mul, norm_cpow_neg_add_one ht0 1]`. Establish `hd : 0 ≤ dom t`. Unfold `dom`. Conclude with `div_nonneg zero_le_one (mul_nonneg ht0.le (sq_nonneg _))`. Rewrite using `[Real.norm_of_nonneg hd]`.

Establish `h2 : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹`. Rewrite using `[show -((1 : ℝ) + 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Unfold `dom`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma core_bigO {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) =O[atTop] dom := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop x₁] with t ht
  have ht0 : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  rw [norm_mul, norm_cpow_neg_add_one ht0 1]
  have hd : 0 ≤ dom t := by
    unfold dom
    exact div_nonneg zero_le_one (mul_nonneg ht0.le (sq_nonneg _))
  rw [Real.norm_of_nonneg hd]
  have h2 : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹ := by
    rw [show -((1 : ℝ) + 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
  rw [h2]
  calc ‖rem a m t‖ * (t ^ 2)⁻¹ ≤ K * t / Real.log t ^ 2 * (t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (hK t ht) (by positivity)
    _ = K * dom t := by
        unfold dom
        field_simp

/- English proof (translation)
Take `⟨K, x₁, hx₁, hK⟩` from `h`. Rewrite using `[← Set.Ioc_union_Ioi_eq_Ioi hx₁.le]`. Use `IntegrableOn.union ?_ ?_` and prove the remaining obligations. Use `MeasureTheory.Integrable.mono' ((continuous_const (y := ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) (F_measurable a m _).aestronglyMeasurable ?_ filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht` and prove the remaining obligations. Establish `ht0 : 0 < t` using `lt_trans one_pos ht.1`.

Rewrite using `[norm_mul, norm_cpow_neg_add_one ht0 1]`. Establish `hp : t ^ (-((1 : ℝ) + 1)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)`. Establish `hr : ‖rem a m t‖ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁`. Unfold `rem`. Combine the equalities or inequalities in the displayed calculation.

Use `add_le_add (norm_sum_le _ _) ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]`. Conclude with `mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)`. Use `_ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := by`. Use `add_le_add ?_ le_rfl` and prove the remaining obligations.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Conclude with `Finset.Icc_subset_Icc le_rfl (Nat.floor_mono ht.2)`. Introduce `i _ _`. Conclude with `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Use `MeasureTheory.Integrable.mono' (MeasureTheory.Integrable.const_mul (dom_integrableOn hx₁) K) (F_measurable a m _).aestronglyMeasurable ?_ filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht` and prove the remaining obligations. Establish `ht' : x₁ ≤ t` using `le_of_lt ht`. Establish `ht0 : 0 < t` using `by linarith`. Establish `hl : Real.log t ≠ 0` using `(Real.log_pos (by linarith)).ne'`. Rewrite using `[norm_mul, norm_cpow_neg_add_one ht0 1]`.

Establish `h2 : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹`. Rewrite using `[show -((1 : ℝ) + 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Unfold `dom`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma core_integrable {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    IntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) (Set.Ioi 1) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  rw [← Set.Ioc_union_Ioi_eq_Ioi hx₁.le]
  refine IntegrableOn.union ?_ ?_
  · refine MeasureTheory.Integrable.mono'
      ((continuous_const (y := ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self)
      (F_measurable a m _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    rw [norm_mul, norm_cpow_neg_add_one ht0 1]
    have hp : t ^ (-((1 : ℝ) + 1)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)
    have hr : ‖rem a m t‖ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
      unfold rem
      calc ‖(∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t‖ ≤ ‖∑ k ∈ Icc 1 ⌊t⌋₊, a k‖ + ‖m * (t : ℂ)‖ := norm_sub_le _ _
        _ ≤ ∑ k ∈ Icc 1 ⌊t⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
            refine add_le_add (norm_sum_le _ _) ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
            exact mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
        _ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
            refine add_le_add ?_ le_rfl
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono ht.2)
            · intro i _ _
              exact norm_nonneg _
    calc ‖rem a m t‖ * t ^ (-((1 : ℝ) + 1)) ≤ (∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁) * 1 :=
          mul_le_mul hr hp (Real.rpow_nonneg ht0.le _) (le_trans (norm_nonneg _) hr)
      _ = ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := mul_one _
  · refine MeasureTheory.Integrable.mono' (MeasureTheory.Integrable.const_mul (dom_integrableOn hx₁) K)
      (F_measurable a m _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : x₁ ≤ t := le_of_lt ht
    have ht0 : 0 < t := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [norm_mul, norm_cpow_neg_add_one ht0 1]
    have h2 : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹ := by
      rw [show -((1 : ℝ) + 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [h2]
    calc ‖rem a m t‖ * (t ^ 2)⁻¹ ≤ K * t / Real.log t ^ 2 * (t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hK t ht') (by positivity)
      _ = K * dom t := by
          unfold dom
          field_simp

/- English proof (translation)
Establish `ht0 : 0 < t` using `by linarith`. Rewrite using `[norm_mul, norm_mul, norm_cpow_neg_add_one ht0 σ, norm_cpow_neg_add_one ht0 1]`. Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (norm_nonneg _)`.
-/
private lemma F_bound (a : ℕ → ℂ) (m : ℂ) {σ : ℝ} (hσ : 1 ≤ σ) {t : ℝ} (ht : 1 < t) :
    ‖rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))‖ ≤ ‖rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))‖ := by
  have ht0 : 0 < t := by linarith
  rw [norm_mul, norm_mul, norm_cpow_neg_add_one ht0 σ, norm_cpow_neg_add_one ht0 1]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (norm_nonneg _)

/- English proof (translation)
Use `MeasureTheory.Integrable.mono (core_integrable h) ((F_measurable a m _).aestronglyMeasurable) ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht`. Conclude with `F_bound a m hσ ht`.
-/
private lemma core_integrable' {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) {σ : ℝ} (hσ : 1 ≤ σ) :
    IntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (Set.Ioi 1) := by
  refine MeasureTheory.Integrable.mono (core_integrable h) ((F_measurable a m _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact F_bound a m hσ ht

/- English proof (translation)
Establish `hI : Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (𝓝[>] 1) (𝓝 (∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))))`. Use `tendsto_integral_filter_of_dominated_convergence (fun t => ‖rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))‖) ?_ ?_ (core_integrable h).norm ?_` and prove the remaining obligations. Conclude with `Eventually.of_forall fun σ => (F_measurable a m _).aestronglyMeasurable`. Use `filter_upwards [self_mem_nhdsWithin] with σ hσ`. Conclude with `ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => F_bound a m (le_of_lt hσ) ht`.

Use `ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : (t : ℂ) ≠ 0`. Establish `: (0 : ℝ) < t` using `lt_trans zero_lt_one ht`. Conclude with `this.ne'` after adjusting the coercions. Establish `hc : Continuous (fun σ : ℝ => rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1)))` using `continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl ht0))`.

Conclude with `(hc.tendsto 1).mono_left nhdsWithin_le_nhds`. Establish `hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ))` using `(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds`. Simplify using `using hσ.mul hI`.
-/
private lemma core_tendsto {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)))) := by
  have hI : Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))‖) ?_ ?_ (core_integrable h).norm ?_
    · exact Eventually.of_forall fun σ => (F_measurable a m _).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => F_bound a m (le_of_lt hσ) ht
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (t : ℂ) ≠ 0 := by
        have : (0 : ℝ) < t := lt_trans zero_lt_one ht
        exact_mod_cast this.ne'
      have hc : Continuous (fun σ : ℝ => rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))) :=
        continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl ht0))
      exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using hσ.mul hI

/- English proof (translation)
Simplify using `only [rem, Nat.floor_natCast, Complex.ofReal_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_eq_rem (a : ℕ → ℂ) (m : ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, a k = rem a m n + m * n := by
  simp only [rem, Nat.floor_natCast, Complex.ofReal_natCast]
  ring

/- English proof (translation)
Take `⟨K, x₁, hx₁, hK⟩` from `h`. Establish `hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n` using `(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1`. Establish `hx : ∀ᶠ n : ℕ in atTop, x₁ ≤ n` using `tendsto_natCast_atTop_atTop.eventually_ge_atTop x₁`. Use `Asymptotics.IsBigO.of_bound (|K| + ‖m‖) ?_` and prove the remaining obligations. Use `filter_upwards [hlog, hx] with n hl hxn`.

Rewrite using `[sum_eq_rem a m n]`. Establish `h1` using `hK n hxn`. Establish `hn0 : (0 : ℝ) ≤ n` using `n.cast_nonneg`. Rewrite using `[Real.rpow_one, Real.norm_of_nonneg hn0]`. Establish `hL : 1 ≤ Real.log n ^ 2` using `by nlinarith`.

Establish `h2 : ‖rem a m n‖ ≤ |K| * n`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖m * (n : ℂ)‖ = ‖m‖ * n`. Rewrite using `[norm_mul]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma rem_bigO {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hx : ∀ᶠ n : ℕ in atTop, x₁ ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop x₁
  refine Asymptotics.IsBigO.of_bound (|K| + ‖m‖) ?_
  filter_upwards [hlog, hx] with n hl hxn
  rw [sum_eq_rem a m n]
  have h1 := hK n hxn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [Real.rpow_one, Real.norm_of_nonneg hn0]
  have hL : 1 ≤ Real.log n ^ 2 := by nlinarith
  have h2 : ‖rem a m n‖ ≤ |K| * n := by
    calc ‖rem a m n‖ ≤ K * n / Real.log n ^ 2 := h1
      _ ≤ |K| * n / Real.log n ^ 2 := by gcongr; exact le_abs_self K
      _ ≤ |K| * n := div_le_self (by positivity) hL
  have h3 : ‖m * (n : ℂ)‖ = ‖m‖ * n := by
    rw [norm_mul]
    simp
  calc ‖rem a m n + m * n‖ ≤ ‖rem a m n‖ + ‖m * (n : ℂ)‖ := norm_add_le _ _
    _ ≤ |K| * n + ‖m‖ * n := by rw [h3]; linarith
    _ = (|K| + ‖m‖) * n := by ring

/- English proof (translation)
Apply `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` to reduce the goal to its premises. Conclude with `(Complex.continuous_ofReal.tendsto' (1 : ℝ) 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with σ hσ`. Rewrite using `[Set.mem_compl_singleton_iff]`. Establish `h1 : σ ≠ 1` using `(show (1 : ℝ) < σ from hσ).ne'`.

Conclude with `h1` after adjusting the coercions.
-/
private lemma ofReal_tendsto_punctured :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (Complex.continuous_ofReal.tendsto' (1 : ℝ) 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [Set.mem_compl_singleton_iff]
    have h1 : σ ≠ 1 := (show (1 : ℝ) < σ from hσ).ne'
    exact_mod_cast h1

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = Function.update (fun s => (s - 1) * riemannZeta s) 1 1` from `⟨_, rfl⟩`. Establish `hgs : ∀ s : ℂ, s ≠ 1 → g s = (s - 1) * riemannZeta s` using `fun s hs => by`. Simplify using `[hg, Function.update_apply, hs]`. Establish `h1 : g 1 = 1` using `by simp [hg]`. Establish `hdiff : Differentiable ℂ g`.

Establish `hon : DifferentiableOn ℂ g (Set.univ \ {1})`. Introduce `s hs`. Establish `hs1 : s ≠ 1` using `hs.2`. Establish `hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z` using `by filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz`. Conclude with `hgs z hz`.

Conclude with `(((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq hev).differentiableWithinAt`. Establish `hcont : ContinuousAt g 1`. Rewrite using `[continuousAt_iff_punctured_nhds, h1]`. Use `riemannZeta_residue_one.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Conclude with `(hgs s hs).symm`. Establish `hall` using `(Complex.differentiableOn_compl_singleton_and_continuousAt_iff Filter.univ_mem).1 ⟨hon, hcont⟩`. Conclude with `differentiableOn_univ.1 hall`. Establish `hd1 : deriv g 1 = Real.eulerMascheroniConstant`. Establish `h2` using `hasDerivAt_iff_tendsto_slope.1 (hdiff 1).hasDerivAt`.

Establish `h3 : Tendsto (slope g 1) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ))`. Use `tendsto_riemannZeta_sub_one_div.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Establish `hs1 : s - 1 ≠ 0` using `sub_ne_zero.2 hs`. Rewrite using `[slope_def_field, hgs s hs, h1]`.

Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Conclude with `tendsto_nhds_unique h2 h3`. Establish `hcd : ContinuousAt (deriv g) 1` using `((hdiff.analyticAt 1).deriv).continuousAt`.

Establish `hlim : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ))`. Establish `h4 : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (deriv g 1 / g 1))` using `(hcd.div (hdiff 1).continuousAt (by rw [h1]; exact one_ne_zero)).tendsto.mono_left nhdsWithin_le_nhds`. Rewrite `h4` using `[hd1, h1, div_one]`. Conclude with `h4`. Use `hlim.congr' ?_` and prove the remaining obligations.

Establish `hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), g s ≠ 0` using `((hdiff 1).continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)).filter_mono nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin, hne] with s hs hgs0`. Establish `hs1 : s - 1 ≠ 0` using `sub_ne_zero.2 hs`. Establish `hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z` using `by filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz`. Conclude with `hgs z hz`.

Establish `hdg : deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s`. Rewrite using `[hev.deriv_eq]`. Establish `h5 : HasDerivAt (fun z => (z - 1) * riemannZeta z) (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s` using `((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt`. Rewrite using `[h5.deriv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hgs0`, the goal using `[hgs s hs]`. Establish `hz : riemannZeta s ≠ 0` using `right_ne_zero_of_mul hgs0`. Rewrite using `[hdg]`. Use `first`. Consider the case `(field_simp; done)`.

Consider the case `(field_simp; ring)`.
-/
private lemma zeta_logderiv_limit :
    Tendsto (fun s : ℂ => deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) (𝓝[≠] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = Function.update (fun s => (s - 1) * riemannZeta s) 1 1 := ⟨_, rfl⟩
  have hgs : ∀ s : ℂ, s ≠ 1 → g s = (s - 1) * riemannZeta s := fun s hs => by
    simp [hg, Function.update_apply, hs]
  have h1 : g 1 = 1 := by simp [hg]
  have hdiff : Differentiable ℂ g := by
    have hon : DifferentiableOn ℂ g (Set.univ \ {1}) := by
      intro s hs
      have hs1 : s ≠ 1 := hs.2
      have hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
        exact hgs z hz
      exact (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    have hcont : ContinuousAt g 1 := by
      rw [continuousAt_iff_punctured_nhds, h1]
      refine riemannZeta_residue_one.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hgs s hs).symm
    have hall := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff Filter.univ_mem).1 ⟨hon, hcont⟩
    exact differentiableOn_univ.1 hall
  have hd1 : deriv g 1 = Real.eulerMascheroniConstant := by
    have h2 := hasDerivAt_iff_tendsto_slope.1 (hdiff 1).hasDerivAt
    have h3 : Tendsto (slope g 1) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
      refine tendsto_riemannZeta_sub_one_div.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
      rw [slope_def_field, hgs s hs, h1]
      first
        | (field_simp; done)
        | (field_simp; ring)
    exact tendsto_nhds_unique h2 h3
  have hcd : ContinuousAt (deriv g) 1 := ((hdiff.analyticAt 1).deriv).continuousAt
  have hlim : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have h4 : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (deriv g 1 / g 1)) :=
      (hcd.div (hdiff 1).continuousAt (by rw [h1]; exact one_ne_zero)).tendsto.mono_left
        nhdsWithin_le_nhds
    rw [hd1, h1, div_one] at h4
    exact h4
  refine hlim.congr' ?_
  have hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), g s ≠ 0 :=
    ((hdiff 1).continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hne] with s hs hgs0
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact hgs z hz
  have hdg : deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hev.deriv_eq]
    have h5 : HasDerivAt (fun z => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
    rw [h5.deriv]
    ring
  rw [hgs s hs] at hgs0 ⊢
  have hz : riemannZeta s ≠ 0 := right_ne_zero_of_mul hgs0
  rw [hdg]
  first
    | (field_simp; done)
    | (field_simp; ring)

/- English proof (translation)
Take `⟨c, C, hc, h⟩` from `Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos`. Establish `hE : 0 < Real.exp (q : ℝ)` using `Real.exp_pos _`. Use `⟨|C| * (24 / c ^ 4), Real.exp q + 2, by linarith, fun t ht => ?_⟩` and prove the remaining obligations. Establish `ht2 : 2 ≤ t` using `by linarith`. Establish `ht0 : 0 < t` using `by linarith`.

Establish `hq : (q : ℝ) ≤ Real.log t ^ (1 : ℝ)`. Rewrite using `[Real.rpow_one, Real.le_log_iff_exp_le ht0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `h q χ t ht2 hq`. Establish `e : rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (if χ = 1 then 1 else 0) t = Formalism.ZeroFreeDirichlet.psiChi χ t - (if χ = 1 then (t : ℂ) else 0)`.

Unfold `rem Formalism.ZeroFreeDirichlet.psiChi`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`. Use `h1.trans ?_` and prove the remaining obligations. Establish `h2` using `exp_sqrt_le hc (x := t) (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_abs_self C`. Use `_ = |C| * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring`.
-/
private lemma sw_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (if χ = 1 then 1 else 0) := by
  obtain ⟨c, C, hc, h⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  have hE : 0 < Real.exp (q : ℝ) := Real.exp_pos _
  refine ⟨|C| * (24 / c ^ 4), Real.exp q + 2, by linarith, fun t ht => ?_⟩
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hq : (q : ℝ) ≤ Real.log t ^ (1 : ℝ) := by
    rw [Real.rpow_one, Real.le_log_iff_exp_le ht0]
    linarith
  have h1 := h q χ t ht2 hq
  have e : rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (if χ = 1 then 1 else 0) t =
      Formalism.ZeroFreeDirichlet.psiChi χ t - (if χ = 1 then (t : ℂ) else 0) := by
    unfold rem Formalism.ZeroFreeDirichlet.psiChi
    split_ifs <;> simp
  rw [e]
  refine h1.trans ?_
  have h2 := exp_sqrt_le hc (x := t) (by linarith)
  calc C * t * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ |C| * t * (24 / c ^ 4 / Real.log t ^ 2) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring

/- English proof (translation)
Establish `hI : Icc 0 n = insert 0 (Icc 1 n)`. Use extensionality with `k`. Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`. Apply the tactic sequence `constructor <;> intro hk <;> omega`. Rewrite using `[hI, Finset.sum_insert (by simp), hb, zero_add]`.
-/
private lemma sum_Icc_zero {b : ℕ → ℂ} (hb : b 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, b k = ∑ k ∈ Icc 1 n, b k := by
  have hI : Icc 0 n = insert 0 (Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor <;> intro hk <;> omega
  rw [hI, Finset.sum_insert (by simp), hb, zero_add]

/- English proof (translation)
Unfold `Formalism.HermitianLattices.GL2a2.LogDerivSeries`. Introduce `q _ χ hχ`. Establish `h : RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0`. Establish `h0` using `sw_bound q χ`. Rewrite `h0` using `[if_neg hχ]`.

Conclude with `h0`. Establish `hc0 : ((Λ 0 : ℝ) : ℂ) * χ ((0 : ℕ) : ZMod q) = 0` using `by simp`. Establish `hs : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1)` using `(Complex.continuous_ofReal.tendsto' (1 : ℝ) 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds`. Establish `hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ)` using `DirichletCharacter.differentiable_LFunction hχ`. Establish `hcL : ContinuousAt (fun s : ℂ => -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) 1` using `((hdiff.analyticAt 1).deriv.continuousAt.neg).div hdiff.continuous.continuousAt (DirichletCharacter.LFunction_apply_one_ne_zero hχ)`.

Establish `hA : Tendsto (fun σ : ℝ => -deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ) (𝓝[>] 1) (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))` using `hcL.tendsto.comp hs`. Establish `hid : ∀ σ : ℝ, 1 < σ → (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 t * (t : ℂ) ^ (-((σ : ℂ) + 1)) = -deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ`. Introduce `σ hσ`. Establish `hre : (1 : ℝ) < ((σ : ℂ)).re` using `by simpa using hσ`. Establish `hfun : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) = (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => ((Λ n : ℝ) : ℂ))`.

Use function extensionality and compare the values at `n`. Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : LSeriesSummable (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) σ`. Rewrite using `[hfun]`.

Conclude with `DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hre`. Establish `hL` using `LSeries_eq_mul_integral (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) zero_le_one hre hsum (rem_bigO h)`. Establish `key` using `DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre`. Rewrite `key` using `[← hfun]`. Rewrite using `[DirichletCharacter.LFunction_eq_LSeries χ hre, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hre, ← key, hL]`.

Use `congr 1`. Use `setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)` and prove the remaining obligations. Simplify using `[rem]`. Establish `hF : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (𝓝[>] 1) (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))`. Use `hA.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with σ hσ`. Conclude with `(hid σ hσ).symm`. Establish `hI` using `tendsto_nhds_unique (core_tendsto h) hF`. Establish `hdf : ∀ t : ℝ, t ≠ 0 → deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t = ((-(t ^ 2)⁻¹ : ℝ) : ℂ)` using `fun t ht => ((hasDerivAt_inv ht).ofReal_comp).deriv`. Establish `hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t` using `fun t ht => ((hasDerivAt_inv (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne').ofReal_comp).differentiableAt`.

Establish `hf_int : LocallyIntegrableOn (deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ))) (Set.Ici 1)`. Establish `hc : ContinuousOn (fun t : ℝ => ((-(t ^ 2)⁻¹ : ℝ) : ℂ)) (Set.Ici 1)`. Apply `Complex.continuous_ofReal.comp_continuousOn` to reduce the goal to its premises. Apply `ContinuousOn.neg` to reduce the goal to its premises. Apply `ContinuousOn.inv₀ (by fun_prop)` to reduce the goal to its premises.

Introduce `t ht`. Conclude with `pow_ne_zero 2 (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne'`. Conclude with `(hc.congr (fun t ht => hdf t (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne')).locallyIntegrableOn measurableSet_Ici`. Establish `hlim0 : Tendsto (fun n : ℕ => ((((n : ℝ))⁻¹ : ℝ) : ℂ) * ∑ k ∈ Icc 0 n, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q)) atTop (𝓝 0)`. Take `⟨K, x₁, hx₁, hK⟩` from `h`.

Establish `hlog2 : Tendsto (fun n : ℕ => Real.log n ^ 2) atTop atTop` using `(tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)`. Use `squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hlog2 : Tendsto (fun n : ℕ => K / Real.log n ^ 2) atTop (𝓝 0))` and prove the remaining obligations. Use `filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop x₁] with n hn`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hn1 : (n : ℝ) ≠ 0` using `hn0.ne'`.

Rewrite using `[sum_Icc_zero hc0, sum_eq_rem _ 0 n, zero_mul, add_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Establish `hinv : ((n : ℝ))⁻¹ * n = 1` using `inv_mul_cancel₀ hn1`. Combine the equalities or inequalities in the displayed calculation. Establish `hdom : (fun t : ℝ => deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q)) =O[atTop] dom`. Use `(core_bigO h).neg_left.congr' ?_ EventuallyEq.rfl` and prove the remaining obligations.

Use `filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht`. Establish `ht0 : t ≠ 0` using `(show (0 : ℝ) < t by linarith).ne'`. Rewrite using `[hdf t ht0, sum_Icc_zero hc0, show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]`. Simplify using `only [rem, zero_mul, sub_zero]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hg_int : IntegrableAtFilter dom atTop` using `⟨Set.Ioi 2, Ioi_mem_atTop 2, dom_integrableOn one_lt_two⟩`. Establish `hT` using `tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) (c := fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) hc0 hf_diff hf_int hlim0 hdom hg_int`. Establish `hval : (0 : ℂ) - ∫ t in Set.Ioi (1 : ℝ), deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q) = -(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)`. Rewrite using `[← neg_div, ← hI, zero_sub, ← integral_neg]`.

Use `setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : t ≠ 0` using `(show (0 : ℝ) < t from lt_trans one_pos ht).ne'`. Use `beta_reduce`. Rewrite using `[hdf t ht0, sum_Icc_zero hc0, show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]`. Simplify using `only [rem, zero_mul, sub_zero]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hT` using `[hval]`. Use `hT.congr (fun N => ?_)` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[sum_Icc_zero (b := fun k : ℕ => ((((k : ℝ))⁻¹ : ℝ) : ℂ) * (((Λ k : ℝ) : ℂ) * χ (k : ZMod q))) (by simp) N]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem logDerivSeries_main : Formalism.HermitianLattices.GL2a2.LogDerivSeries := by
  unfold Formalism.HermitianLattices.GL2a2.LogDerivSeries
  intro q _ χ hχ
  have h : RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 := by
    have h0 := sw_bound q χ
    rw [if_neg hχ] at h0
    exact h0
  have hc0 : ((Λ 0 : ℝ) : ℂ) * χ ((0 : ℕ) : ZMod q) = 0 := by simp
  have hs : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto' (1 : ℝ) 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hcL : ContinuousAt (fun s : ℂ => -deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) 1 :=
    ((hdiff.analyticAt 1).deriv.continuousAt.neg).div hdiff.continuous.continuousAt
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have hA : Tendsto (fun σ : ℝ => -deriv (DirichletCharacter.LFunction χ) σ /
      DirichletCharacter.LFunction χ σ) (𝓝[>] 1)
      (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) :=
    hcL.tendsto.comp hs
  have hid : ∀ σ : ℝ, 1 < σ → (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 t * (t : ℂ) ^ (-((σ : ℂ) + 1))
      = -deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ := by
    intro σ hσ
    have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
    have hfun : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) =
        (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => ((Λ n : ℝ) : ℂ)) := by
      funext n
      simp only [Pi.mul_apply]
      ring
    have hsum : LSeriesSummable (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) σ := by
      rw [hfun]
      exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hre
    have hL := LSeries_eq_mul_integral (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) zero_le_one hre
      hsum (rem_bigO h)
    have key := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [← hfun] at key
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hre,
      ← key, hL]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [rem]
  have hF : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) := by
    refine hA.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hid σ hσ).symm
  have hI := tendsto_nhds_unique (core_tendsto h) hF
  have hdf : ∀ t : ℝ, t ≠ 0 → deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t = ((-(t ^ 2)⁻¹ : ℝ) : ℂ) :=
    fun t ht => ((hasDerivAt_inv ht).ofReal_comp).deriv
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t :=
    fun t ht => ((hasDerivAt_inv (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne').ofReal_comp).differentiableAt
  have hf_int : LocallyIntegrableOn (deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ))) (Set.Ici 1) := by
    have hc : ContinuousOn (fun t : ℝ => ((-(t ^ 2)⁻¹ : ℝ) : ℂ)) (Set.Ici 1) := by
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      exact pow_ne_zero 2 (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne'
    exact (hc.congr (fun t ht => hdf t (show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht).ne')).locallyIntegrableOn
      measurableSet_Ici
  have hlim0 : Tendsto (fun n : ℕ => ((((n : ℝ))⁻¹ : ℝ) : ℂ) *
      ∑ k ∈ Icc 0 n, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q)) atTop (𝓝 0) := by
    obtain ⟨K, x₁, hx₁, hK⟩ := h
    have hlog2 : Tendsto (fun n : ℕ => Real.log n ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm' ?_
      (tendsto_const_nhds.div_atTop hlog2 : Tendsto (fun n : ℕ => K / Real.log n ^ 2) atTop (𝓝 0))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop x₁] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) ≠ 0 := hn0.ne'
    rw [sum_Icc_zero hc0, sum_eq_rem _ 0 n, zero_mul, add_zero, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hinv : ((n : ℝ))⁻¹ * n = 1 := inv_mul_cancel₀ hn1
    calc ((n : ℝ))⁻¹ * ‖rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) 0 n‖
        ≤ ((n : ℝ))⁻¹ * (K * n / Real.log n ^ 2) := mul_le_mul_of_nonneg_left (hK n hn) (by positivity)
      _ = K / Real.log n ^ 2 := by linear_combination (K / Real.log n ^ 2) * hinv
  have hdom : (fun t : ℝ => deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q)) =O[atTop] dom := by
    refine (core_bigO h).neg_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith).ne'
    rw [hdf t ht0, sum_Icc_zero hc0, show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_neg, Complex.cpow_natCast]
    simp only [rem, zero_mul, sub_zero]
    push_cast
    ring
  have hg_int : IntegrableAtFilter dom atTop := ⟨Set.Ioi 2, Ioi_mem_atTop 2, dom_integrableOn one_lt_two⟩
  have hT := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun t : ℝ => ((t⁻¹ : ℝ) : ℂ))
    (c := fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) hc0 hf_diff hf_int hlim0 hdom hg_int
  have hval : (0 : ℂ) - ∫ t in Set.Ioi (1 : ℝ), deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, ((Λ k : ℝ) : ℂ) * χ (k : ZMod q)
      = -(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) := by
    rw [← neg_div, ← hI, zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t from lt_trans one_pos ht).ne'
    beta_reduce
    rw [hdf t ht0, sum_Icc_zero hc0, show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_neg, Complex.cpow_natCast]
    simp only [rem, zero_mul, sub_zero]
    push_cast
    ring
  rw [hval] at hT
  refine hT.congr (fun N => ?_)
  beta_reduce
  rw [sum_Icc_zero (b := fun k : ℕ => ((((k : ℝ))⁻¹ : ℝ) : ℂ) * (((Λ k : ℝ) : ℂ) * χ (k : ZMod q)))
    (by simp) N]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

/- English proof (translation)
Unfold `Formalism.HermitianLattices.GL2a2.PsiZeroConst`. Establish `hsub : Subsingleton (ZMod 1)` using `ZMod.subsingleton_iff.2 rfl`. Establish `hone : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1` using `fun n => by first`. Consider the case `exact MulChar.one_apply (isUnit_of_subsingleton _)`. Consider the case `simp`.

Establish `h : RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1`. Establish `h0` using `sw_bound 1 (1 : DirichletCharacter ℂ 1)`. Rewrite `h0` using `[if_pos rfl]`. Simplify using `only [hone, mul_one] at h0`. Conclude with `h0`.

Establish `hid : ∀ σ : ℝ, 1 < σ → (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)) = -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1`. Introduce `σ hσ`. Establish `hre : (1 : ℝ) < ((σ : ℂ)).re` using `by simpa using hσ`. Establish `hne : (σ : ℂ) - 1 ≠ 0`. Rewrite using `[sub_ne_zero]`.

Conclude with `hσ.ne'` after adjusting the coercions. Establish `hne' : -(σ : ℂ) + 1 ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Take the linear combination `-h0`.

Establish `hsum : LSeriesSummable (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ` using `by first`. Consider the case `exact ArithmeticFunction.LSeriesSummable_vonMangoldt hre`. Consider the case `exact LSeriesSummable_vonMangoldt hre`. Establish `hL` using `LSeries_eq_mul_integral (fun n : ℕ => ((Λ n : ℝ) : ℂ)) zero_le_one hre hsum (rem_bigO h)`. Establish `key : LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ = -deriv riemannZeta σ / riemannZeta σ` using `LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre`.

Establish `hpint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(σ : ℂ))) (Set.Ioi 1)` using `integrableOn_Ioi_cpow_of_lt (by simpa using hσ) one_pos`. Establish `hsplit : ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-((σ : ℂ) + 1)) = (∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))) + ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ))`. Rewrite using `[← integral_add (core_integrable' h hσ.le) hpint]`. Use `setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : (t : ℂ) ≠ 0`.

Conclude with `(show (0 : ℝ) < t from lt_trans one_pos ht).ne'` after adjusting the coercions. Simplify using `only [rem]`. Rewrite using `[show -(σ : ℂ) = 1 + (-((σ : ℂ) + 1)) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpow : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ)) = 1 / ((σ : ℂ) - 1)`.

Rewrite using `[integral_Ioi_cpow_of_lt (by simpa using hσ) one_pos, Complex.ofReal_one, Complex.one_cpow, div_eq_div_iff hne' hne]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : (σ : ℂ) * (1 / ((σ : ℂ) - 1)) = 1 / ((σ : ℂ) - 1) + 1`. Rewrite using `[mul_one_div, div_add_one hne]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmain : (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)) = LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ - (σ : ℂ) * (1 / ((σ : ℂ) - 1))`. Rewrite using `[hL, hsplit, hpow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmain, key, hq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hG : Tendsto (fun σ : ℝ => -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1) (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1))` using `((zeta_logderiv_limit.comp ofReal_tendsto_punctured).neg).sub_const 1`. Establish `hF : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1))`. Use `hG.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with σ hσ`.

Conclude with `(hid σ hσ).symm`. Establish `hlim` using `tendsto_nhds_unique (core_tendsto h) hF`. Establish `hF1 : ∀ u ∈ Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) = (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)`. Introduce `u hu`. Rewrite using `[show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]`.

Simplify using `only [rem, Formalism.HermitianLattices.GL2PrimeSums.psumR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : IntegrableOn (fun u : ℝ => (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2) (Set.Ioi 1)`. Use `(MeasureTheory.Integrable.re (core_integrable h)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu`. Simplify using `only [hF1 u hu, RCLike.re_to_complex, Complex.ofReal_re]`. Establish `e1 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) = ∫ u in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))` using `(setIntegral_congr_fun measurableSet_Ioi hF1).symm`. Establish `hval : ∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 = -1 - Real.eulerMascheroniConstant`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Establish `e0 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) = ((∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)` using `by first`. Consider the case `exact integral_complex_ofReal`. Consider the case `exact integral_ofReal`. Rewrite using `[← e0, e1, hlim]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hT` using `intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id`. Rewrite `hT` using `[hval]`. Conclude with `hT`.
-/
private theorem psiZeroConst_main : Formalism.HermitianLattices.GL2a2.PsiZeroConst := by
  unfold Formalism.HermitianLattices.GL2a2.PsiZeroConst
  have hsub : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
  have hone : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := fun n => by
    first
      | exact MulChar.one_apply (isUnit_of_subsingleton _)
      | simp
  have h : RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 := by
    have h0 := sw_bound 1 (1 : DirichletCharacter ℂ 1)
    rw [if_pos rfl] at h0
    simp only [hone, mul_one] at h0
    exact h0
  have hid : ∀ σ : ℝ, 1 < σ →
      (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1 := by
    intro σ hσ
    have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
    have hne : (σ : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hσ.ne'
    have hne' : -(σ : ℂ) + 1 ≠ 0 := by
      intro h0
      apply hne
      linear_combination -h0
    have hsum : LSeriesSummable (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ := by
      first
        | exact ArithmeticFunction.LSeriesSummable_vonMangoldt hre
        | exact LSeriesSummable_vonMangoldt hre
    have hL := LSeries_eq_mul_integral (fun n : ℕ => ((Λ n : ℝ) : ℂ)) zero_le_one hre hsum (rem_bigO h)
    have key : LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ = -deriv riemannZeta σ / riemannZeta σ :=
      LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    have hpint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(σ : ℂ))) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simpa using hσ) one_pos
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = (∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
          + ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ)) := by
      rw [← integral_add (core_integrable' h hσ.le) hpint]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (t : ℂ) ≠ 0 := by
        exact_mod_cast (show (0 : ℝ) < t from lt_trans one_pos ht).ne'
      simp only [rem]
      rw [show -(σ : ℂ) = 1 + (-((σ : ℂ) + 1)) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
      ring
    have hpow : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ)) = 1 / ((σ : ℂ) - 1) := by
      rw [integral_Ioi_cpow_of_lt (by simpa using hσ) one_pos, Complex.ofReal_one, Complex.one_cpow,
        div_eq_div_iff hne' hne]
      ring
    have hq : (σ : ℂ) * (1 / ((σ : ℂ) - 1)) = 1 / ((σ : ℂ) - 1) + 1 := by
      rw [mul_one_div, div_add_one hne]
      congr 1
      ring
    have hmain : (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ - (σ : ℂ) * (1 / ((σ : ℂ) - 1)) := by
      rw [hL, hsplit, hpow]
      ring
    rw [hmain, key, hq]
    ring
  have hG : Tendsto (fun σ : ℝ => -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1)
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1)) :=
    ((zeta_logderiv_limit.comp ofReal_tendsto_punctured).neg).sub_const 1
  have hF : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1)) := by
    refine hG.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hid σ hσ).symm
  have hlim := tendsto_nhds_unique (core_tendsto h) hF
  have hF1 : ∀ u ∈ Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))
        = (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) := by
    intro u hu
    rw [show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
    simp only [rem, Formalism.HermitianLattices.GL2PrimeSums.psumR]
    push_cast
    ring
  have hint : IntegrableOn (fun u : ℝ => (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2)
      (Set.Ioi 1) := by
    refine (MeasureTheory.Integrable.re (core_integrable h)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [hF1 u hu, RCLike.re_to_complex, Complex.ofReal_re]
  have e1 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)
      = ∫ u in Set.Ioi (1 : ℝ),
        rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) :=
    (setIntegral_congr_fun measurableSet_Ioi hF1).symm
  have hval : ∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2
      = -1 - Real.eulerMascheroniConstant := by
    apply Complex.ofReal_injective
    have e0 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)
        = ((∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) := by
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [← e0, e1, hlim]
    push_cast
    ring
  have hT := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
  rw [hval] at hT
  exact hT

end Formalism.HermitianLattices.P.PsiZeroIntegral

namespace Formalism.HermitianLattices.GL2a2

/- English proof (translation)
Conclude with `Formalism.HermitianLattices.P.PsiZeroIntegral.logDerivSeries_main`.
-/
theorem log_deriv_series : Formalism.HermitianLattices.GL2a2.LogDerivSeries := by
  exact Formalism.HermitianLattices.P.PsiZeroIntegral.logDerivSeries_main

/- English proof (translation)
Conclude with `Formalism.HermitianLattices.P.PsiZeroIntegral.psiZeroConst_main`.
-/
theorem psi_zero_integral_constant : Formalism.HermitianLattices.GL2a2.PsiZeroConst := by
  exact Formalism.HermitianLattices.P.PsiZeroIntegral.psiZeroConst_main

end Formalism.HermitianLattices.GL2a2
