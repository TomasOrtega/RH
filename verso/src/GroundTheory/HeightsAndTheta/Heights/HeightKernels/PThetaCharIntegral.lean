import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory

noncomputable section

namespace KThetaCharIntegral

/- English proof (translation)
Rewrite using `[integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]`. Use `split_ifs with hn`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Establish `hc : (2 * π * Complex.I * n : ℂ) ≠ 0`.

Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero, hn]`. Establish `h1 : ∀ t : ℝ, 2 * π * Complex.I * ((n : ℂ) * (t : ℂ)) = 2 * π * Complex.I * n * t`. Introduce `t`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[h1]`.

Rewrite using `[integral_exp_mul_complex hc]`. Establish `h2 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1`. Rewrite using `[show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I n`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules.
-/
theorem integral_Icc_exp (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((n : ℂ) * (t : ℂ))) =
      if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h1 : ∀ t : ℝ, 2 * π * Complex.I * ((n : ℂ) * (t : ℂ)) = 2 * π * Complex.I * n * t := by
      intro t; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h2]
    simp

/- English proof (translation)
Unfold `torusChar`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`.
-/
theorem torusChar_eq_prod {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by
  unfold torusChar
  rw [Finset.mul_sum, Complex.exp_sum]

end KThetaCharIntegral

/- English proof (translation)
Introduce `g m`. Establish `hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1`. Rewrite using `[← Set.pi_univ_Icc]`. Both sides reduce to the same expression. Rewrite using `[hset, volume_pi, Measure.restrict_pi_pi]`.

Repeatedly rewrite using `[KThetaCharIntegral.torusChar_eq_prod]`. Rewrite using `[integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]`. Repeatedly rewrite using `[KThetaCharIntegral.integral_Icc_exp]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hm (funext h)`.

Rewrite using `[if_neg hm]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)`.
-/
theorem ThetaCharIntegral.proof : ThetaCharIntegral.Statement := by
  intro g m
  have hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]; rfl
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [KThetaCharIntegral.torusChar_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]
  simp_rw [KThetaCharIntegral.integral_Icc_exp]
  by_cases hm : m = 0
  · subst hm; simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    rw [if_neg hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end

end GroundTheory.Heights₂.Heights
