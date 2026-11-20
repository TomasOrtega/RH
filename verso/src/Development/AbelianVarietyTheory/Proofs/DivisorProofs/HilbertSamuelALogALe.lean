import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hD1' : (1 : ℝ) ≤ D` using `by exact_mod_cast hD1`. Establish `hDT' : (D : ℝ) ≤ T` using `by exact_mod_cast hDT`. Establish `hT1 : (1 : ℝ) ≤ T` using `le_trans hD1' hDT'`. Use `set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef`. Establish `hA1 : 1 ≤ A`.

Establish `: (0 : ℝ) ≤ 2 * z * T` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmax : max A 1 = A` using `max_eq_left hA1`. Rewrite using `[hmax]`. Establish `hApos : 0 < A` using `by linarith`.

Establish `hAle : A ≤ 702 * (T : ℝ) ^ 2`. Establish `h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2` using `by nlinarith`. Establish `h2 : 2 * z * (T : ℝ) ≤ T` using `by nlinarith`. Establish `h3 : (T : ℝ) ≤ (T : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hT0 : (0 : ℝ) < T` using `by linarith`. Establish `hTsq : (T : ℝ) ≤ Real.sqrt b` using `by nlinarith`. Establish `hlogT : 2 * Real.log T ≤ PP`. Establish `h1 : Real.log T ≤ Real.log (Real.sqrt b)` using `Real.log_le_log hT0 hTsq`. Rewrite `h1` using `[Real.log_sqrt (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog702 : Real.log 702 < 7`. Rewrite using `[Real.log_lt_iff_lt_exp (by norm_num)]`. Establish `he` using `Real.exp_one_gt_d9`. Establish `: Real.exp 7 = Real.exp 1 ^ 7`.

Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Rewrite using `[this]`. Establish `h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7`. Apply `pow_le_pow_left₀ (by norm_num); linarith` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `hlogA : Real.log A ≤ 8 * PP`. Establish `h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2)` using `Real.log_le_log hApos hAle`. Establish `h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T`. Rewrite using `[Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogA0 : 0 ≤ Real.log A` using `Real.log_nonneg hA1`. Establish `hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP)` using `mul_le_mul hAle hlogA hlogA0 (by positivity)`. Establish `hsq : ((T : ℝ) * PP) ^ 2 ≤ b`. Establish `h0 : 0 ≤ (T : ℝ) * PP` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2`. Establish `: PP ≤ PP ^ 2` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_left this (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hilbertSamuel_ALogA_le (T D : ℕ) (PP b z : ℝ) (hD1 : 1 ≤ D) (hDT : D ≤ T) (hPP : 1 ≤ PP)
    (hb : 1 ≤ b) (hlogb : Real.log b ≤ PP) (hTP : (T : ℝ) * PP ≤ Real.sqrt b) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (max (26 * (26 * (D : ℝ) ^ 2 + 2 * z * T)) 1)
      ≤ 6000 * b := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDT' : (D : ℝ) ≤ T := by exact_mod_cast hDT
  have hT1 : (1 : ℝ) ≤ T := le_trans hD1' hDT'
  set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 2 * z * T := by positivity
    nlinarith
  have hmax : max A 1 = A := max_eq_left hA1
  rw [hmax]
  have hApos : 0 < A := by linarith
  have hAle : A ≤ 702 * (T : ℝ) ^ 2 := by
    have h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith
    have h2 : 2 * z * (T : ℝ) ≤ T := by nlinarith
    have h3 : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (T : ℝ) ≤ Real.sqrt b := by nlinarith
  have hlogT : 2 * Real.log T ≤ PP := by
    have h1 : Real.log T ≤ Real.log (Real.sqrt b) := Real.log_le_log hT0 hTsq
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog702 : Real.log 702 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hlogA : Real.log A ≤ 8 * PP := by
    have h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2) := Real.log_le_log hApos hAle
    have h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP) :=
    mul_le_mul hAle hlogA hlogA0 (by positivity)
  have hsq : ((T : ℝ) * PP) ^ 2 ≤ b := by
    have h0 : 0 ≤ (T : ℝ) * PP := by positivity
    calc ((T : ℝ) * PP) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ h0 hTP 2
      _ = b := Real.sq_sqrt (by linarith)
  have hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2 := by
    have : PP ≤ PP ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

end GlobalTheory
