import Mathlib

namespace GlobalTheory.ClosingLemmaFourth

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
