import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine.Intg

/- English proof (translation)
Establish `h` using `integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4) (by rw [Complex.finrank_real_complex]; norm_num)`. Use `(h.const_mul (1 / Real.pi)).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hx : (0 : ℝ) < 1 + ‖x‖ ^ 2` using `by positivity`. Establish `e : (-4 / 2 : ℝ) = -((2 : ℕ) : ℝ)` using `by norm_num`. Simplify using `only [fsDens]`.

Rewrite using `[e, Real.rpow_neg hx.le, Real.rpow_natCast]`. Use `Real.pi_pos` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem integrable_fsDens : Integrable fsDens := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (h.const_mul (1 / Real.pi)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have e : (-4 / 2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
  simp only [fsDens]
  rw [e, Real.rpow_neg hx.le, Real.rpow_natCast]
  have := Real.pi_pos
  field_simp

/- English proof (translation)
Use `fin_cases a`. Simplify `continuous_const` using `[lineVec]`. Simplify `continuous_id'` using `[lineVec]`.
-/
theorem continuous_lineVec (a : Fin 2) : Continuous fun x : ℂ => lineVec x a := by
  fin_cases a
  · simpa [lineVec] using continuous_const
  · simpa [lineVec] using continuous_id'

/- English proof (translation)
Unfold `qCoef`. Use `Continuous.div ((continuous_lineVec _).mul (Complex.continuous_conj.comp (continuous_lineVec _))) (Complex.continuous_ofReal.comp (by fun_prop)) fun x => ?_` and prove the remaining obligations. Establish `hx : (0 : ℝ) < 1 + ‖x‖ ^ 2` using `by positivity`. Conclude with `hx.ne'` after adjusting the coercions.
-/
theorem continuous_qCoef (ab : Fin 2 × Fin 2) : Continuous fun x : ℂ => qCoef x ab := by
  unfold qCoef
  refine Continuous.div ((continuous_lineVec _).mul (Complex.continuous_conj.comp (continuous_lineVec _)))
    (Complex.continuous_ofReal.comp (by fun_prop)) fun x => ?_
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  exact_mod_cast hx.ne'

/- English proof (translation)
Use `fin_cases a`. Simplify using `[lineVec]`. Simplify using `[lineVec]`.
-/
theorem norm_lineVec_sq_le (x : ℂ) (a : Fin 2) : ‖lineVec x a‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
  fin_cases a
  · simp [lineVec]
  · simp [lineVec]

/- English proof (translation)
Establish `hx : (0 : ℝ) < 1 + ‖x‖ ^ 2` using `by positivity`. Unfold `qCoef`. Rewrite using `[norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx.le, div_le_one hx]`. Establish `h1` using `norm_lineVec_sq_le x ab.1`. Establish `h2` using `norm_lineVec_sq_le x ab.2`.

Use polynomial arithmetic with `[sq_nonneg (‖lineVec x ab.2‖ - ‖lineVec x ab.1‖)]`.
-/
theorem norm_qCoef_le (x : ℂ) (ab : Fin 2 × Fin 2) : ‖qCoef x ab‖ ≤ 1 := by
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold qCoef
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx.le, div_le_one hx]
  have h1 := norm_lineVec_sq_le x ab.1
  have h2 := norm_lineVec_sq_le x ab.2
  nlinarith [sq_nonneg (‖lineVec x ab.2‖ - ‖lineVec x ab.1‖)]

/- English proof (translation)
Establish `h : Integrable (fun x : ℂ => (fsDens x : ℂ))` using `integrable_fsDens.ofReal`. Use `h.bdd_mul (c := 1) (continuous_finset_prod _ fun i _ => continuous_qCoef (f i)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_qCoef_le x (f i)`.
-/
theorem integrable_prod_qCoef_mul_fsDens (k : ℕ) (f : Fin k → Fin 2 × Fin 2) :
    Integrable (fun x : ℂ => (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) := by
  have h : Integrable (fun x : ℂ => (fsDens x : ℂ)) := integrable_fsDens.ofReal
  refine h.bdd_mul (c := 1) (continuous_finset_prod _ fun i _ => continuous_qCoef (f i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_qCoef_le x (f i)

end GlobalTheory.FibLine.Intg
