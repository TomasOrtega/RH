import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma conj_mul_im_eq_normSq_mul_div_im (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
lemma ne_zero_and_div_im_pos (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    a ≠ 0 ∧ 0 < (b / a).im := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  refine ⟨ha, ?_⟩
  rw [conj_mul_im_eq_normSq_mul_div_im a b ha] at hab
  exact pos_of_mul_pos_right hab (Complex.normSq_nonneg a)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem discr_closure_pair_ne_zero (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by
  obtain ⟨ha, hpos⟩ := ne_zero_and_div_im_pos a b hab
  rw [discr_closure_pair a b hpos]
  have hpi : (2 * Real.pi / a : ℂ) ≠ 0 := by
    refine div_ne_zero ?_ ha
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ (ModularForm.eta_ne_zero hpos))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
