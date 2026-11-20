import Mathlib

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma vert_inv_right (c d b : ℝ) (w : ℂ) (hb : w.re < b) :
    I • ∫ y : ℝ in c..d, 1 / (((b : ℂ) + y * I) - w) =
      Complex.log (((b : ℂ) + d * I) - w) - Complex.log (((b : ℂ) + c * I) - w) := by
  have hz : ∀ y : ℝ, ((b : ℂ) + y * I - w) ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((b : ℂ) + y * I - w) ≠ 0 := fun y => Complex.slitPlane_ne_zero (hz y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.log ((b : ℂ) + y * I - w))
      (I * (1 / ((b : ℂ) + y * I - w))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (b : ℂ) + y * I - w) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (b : ℂ)).sub_const w
    have h2 := h1.clog_real (hz y)
    convert h2 using 1
    rw [one_div, div_eq_mul_inv]
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  exact (continuous_const.mul (continuous_const.div (by fun_prop) hne)).intervalIntegrable _ _

end PI.EF.PK
