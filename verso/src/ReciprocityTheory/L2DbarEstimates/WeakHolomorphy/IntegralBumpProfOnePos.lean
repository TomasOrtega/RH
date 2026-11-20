import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

variable {n : ℕ}

noncomputable def bumpProf (t s : ℝ) : ℝ := Real.smoothTransition (1 - 4 * (s / t) ^ 2)

noncomputable def mollConst (n : ℕ) : ℝ := (∫ z : V n, bumpProf 1 ‖z‖)⁻¹

noncomputable def mollProf (n : ℕ) (t s : ℝ) : ℝ := mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t s

noncomputable def moll (n : ℕ) (t : ℝ) (z : V n) : ℝ := mollProf n t ‖z‖

noncomputable def mollify (n : ℕ) (t : ℝ) (u : V n → ℂ) (x : V n) : ℂ :=
  ∫ y, (moll n t (x - y) : ℂ) * u y

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bumpProf_scale {t : ℝ} (ht : 0 < t) (z : V n) : bumpProf t ‖z‖ = bumpProf 1 ‖t⁻¹ • z‖ := by
  simp only [bumpProf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_one]
  congr 1
  ring

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem integral_bumpProf {t : ℝ} (ht : 0 < t) :
    ∫ z : V n, bumpProf t ‖z‖ = t ^ (2 * n) * ∫ z : V n, bumpProf 1 ‖z‖ := by
  simp_rw [bumpProf_scale ht]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : V n => bumpProf 1 ‖z‖) ht.le,
    finrank_V, smul_eq_mul]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma bumpProf_eq_zero_of_half_lt {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) : bumpProf t s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 1 / 2 < s / t := by rw [lt_div_iff₀ ht]; linarith
  nlinarith

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma continuous_bumpProf_norm (n : ℕ) (t : ℝ) : Continuous (fun z : V n => bumpProf t ‖z‖) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem integral_bumpProf_one_pos (n : ℕ) : 0 < ∫ z : V n, bumpProf 1 ‖z‖ := by
  have hcs : HasCompactSupport (fun z : V n => bumpProf 1 ‖z‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V n) (1 / 2)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact bumpProf_eq_zero_of_half_lt one_pos hz
  refine (continuous_bumpProf_norm n 1).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => Real.smoothTransition.nonneg _) (x := 0) ?_
  simp [bumpProf]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mollConst_nonneg (n : ℕ) : 0 ≤ mollConst n := by
  unfold mollConst
  exact inv_nonneg.mpr (integral_nonneg fun z => Real.smoothTransition.nonneg _)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem moll_nonneg (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by
  have h : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  exact mul_nonneg (mul_nonneg (mollConst_nonneg n) (inv_nonneg.mpr h)) (Real.smoothTransition.nonneg _)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem moll_contDiff (n : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (moll n t) := by
  have h : moll n t = fun z => mollConst n * (t ^ (2 * n))⁻¹ *
      Real.smoothTransition (1 - 4 * (‖z‖ ^ 2 / t ^ 2)) := by
    funext z
    simp only [moll, mollProf, bumpProf, div_pow]
  rw [h]
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_norm_sq ℂ).div_const _))))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem moll_tsupport (n : ℕ) {t : ℝ} (ht : 0 < t) : tsupport (moll n t) ⊆ closedBall 0 (t / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hnot
  rw [mem_closedBall, dist_zero_right, not_le] at hnot
  apply hz
  simp only [moll, mollProf, bumpProf_eq_zero_of_half_lt ht hnot, mul_zero]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem moll_hasCompactSupport (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by
  exact (isCompact_closedBall (0 : V n) (t / 2)).of_isClosed_subset (isClosed_tsupport _)
    (moll_tsupport n ht)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem moll_integral (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ z : V n, moll n t z = 1 := by
  simp only [moll, mollProf]
  rw [integral_const_mul, integral_bumpProf ht, mollConst]
  have h1 := integral_bumpProf_one_pos n
  have h2 : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem moll_le (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ z : V n, moll n t z ≤ C / volume.real (ball (0 : V n) t) := by
  refine ⟨mollConst n * volume.real (ball (0 : V n) 1), fun t ht z => ?_⟩
  have hv : 0 < volume.real (ball (0 : V n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : V n) one_pos).ne' measure_ball_lt_top.ne
  have hball : volume.real (ball (0 : V n) t) = t ^ (2 * n) * volume.real (ball (0 : V n) 1) := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume (0 : V n) ht, finrank_V,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos ht _).le]
  rw [hball, mul_div_mul_right _ _ hv.ne']
  have htp : 0 < t ^ (2 * n) := pow_pos ht _
  have hb : bumpProf t ‖z‖ ≤ 1 := Real.smoothTransition.le_one _
  have hc := mollConst_nonneg n
  simp only [moll, mollProf]
  calc mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t ‖z‖
      ≤ mollConst n * (t ^ (2 * n))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hc (inv_nonneg.mpr htp.le))
    _ = mollConst n / t ^ (2 * n) := by ring

end ReciprocityTheory.L2DbarEstimates.C
